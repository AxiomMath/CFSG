module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin

@[expose] def elemBaumann (P : Type*) [Group P] (p : ℕ) : Subgroup P :=
  Subgroup.centralizer (CFSG.elemThompsonCenterTorsion P p : Set P)

@[expose] def IsPrimeReduced {E : Type*} [Group E] (p : ℕ) (V : Subgroup E) : Prop :=
  ∃ _ : V.Normal, CFSG.IsElementaryAbelian p V ∧
    CFSG.pCore p (E ⧸ Subgroup.centralizer (V : Set E)) = ⊥

@[expose] def primeReducedFamily (E : Type*) [Group E] (p : ℕ) : Set (Subgroup E) :=
  {V | IsPrimeReduced p V}

@[expose] def primeReducedAggregate (E : Type*) [Group E] (p : ℕ) : Subgroup E :=
  sSup (primeReducedFamily E p)

end CFSG.Quasithin
