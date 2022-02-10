set PRODUITS;
set MOISp ordered; 
set MOIS := MOISp  diff {last(MOISp)} ordered;
set MACHINES;

param limite_vente{MOIS,PRODUITS};
param arret_maintenance{MACHINES,MOIS};
param temps{MACHINES,PRODUITS};
param prix_vente{PRODUITS};
param limite_maintenance{MACHINES};
param prix_machine{MACHINES};

var quantite_fabriquee{PRODUITS,MOIS} integer >=0;
var quantite_vendue{PRODUITS,MOIS} integer  >=0;
var quantite_stockee{PRODUITS,MOISp} integer  >=0, <=100;
var maintenance{MACHINES,MOIS} integer >=0;
var achat_machine{MACHINES} integer >=0;

maximize profit :
   sum{t in MOIS, p in PRODUITS} (quantite_vendue[p,t]*prix_vente[p] - 0.5*quantite_stockee[p,t])-175/*-(sum{o in MACHINES} achat_machine[o]*prix_machine[o])*/;
   
subject to stockage_debut {p in PRODUITS}:
   quantite_stockee[p,first(MOISp)]=0;
subject to stockage_fin {p in PRODUITS}:
   quantite_stockee[p,last(MOISp)]=50; 

#---------------------------Question1-----------------------------------------------------------------
#-------------------------------------------------------------------------------------------------
/*subject to duree_construction {t in MOIS, o in MACHINES}: 
   sum{p in PRODUITS} quantite_fabriquee[p,t]*temps[o,p] <= 192*arret_maintenance[o,t];*/
#----------------------------------------------------------------------------------------------------
#--------------------------------------------------------------------------------------------------


#----------------------------Question2----------------------------------------------------------------
#-------------------------------------------------------------------------------------------------
subject to null {o in MACHINES}:
   sum{t in MOIS} maintenance[o,t]=limite_maintenance[o];
   
subject to duree_construction {t in MOIS, o in MACHINES}:
   sum{p in PRODUITS} quantite_fabriquee[p,t]*temps[o,p] <= (if o='broyeuses' then 2*limite_maintenance[o]*192 - maintenance[o,t]*192 else limite_maintenance[o]*192 - maintenance[o,t]*192);
#------------------------------------------------------------------------------------------------
#--------------------------------------------------------------------------------------------------  


#----------------------------Question3----------------------------------------------------------------
#-------------------------------------------------------------------------------------------------
/*subject to null {o in MACHINES}:
   sum{t in MOIS} maintenance[o,t]=limite_maintenance[o];
   
subject to duree_construction {t in MOIS, o in MACHINES}:
   sum{p in PRODUITS} quantite_fabriquee[p,t]*temps[o,p] <= (if o='broyeuses' then (2+limite_maintenance[o])*192 - maintenance[o,t]*192 else limite_maintenance[o]*192 - maintenance[o,t]*192);*/
#------------------------------------------------------------------------------------------------
#--------------------------------------------------------------------------------------------------  




#----------------------------Question3.1--------------------------------------------------------------
#---------------------------------------------------------------------------------------------------
/*subject to null {o in MACHINES}:
   sum{t in MOIS} maintenance[o,t]=limite_maintenance[o]+achat_machine[o];
   
subject to duree_construction {t in MOIS, o in MACHINES}:
   sum{p in PRODUITS} quantite_fabriquee[p,t]*temps[o,p] <= (if o='broyeuses' then (2*limite_maintenance[o]+achat_machine[o])*192 - maintenance[o,t]*192 else (limite_maintenance[o]+achat_machine[o])*192 - maintenance[o,t]*192);*/
   
#-----------------------------------------------------------------------------------------------------
#----------------------------------------------------------------------------------------------------------------
   
subject to balance {t in MOIS, p in PRODUITS}:
   quantite_fabriquee[p,t]+quantite_stockee[p,t]=quantite_vendue[p,t]+quantite_stockee[p,next(t,MOISp)];
   
subject to limitation {t in MOIS, p in PRODUITS}:
   quantite_vendue[p,t]<=limite_vente[t,p];
