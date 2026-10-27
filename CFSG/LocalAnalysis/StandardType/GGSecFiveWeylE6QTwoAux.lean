module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem

variable {G : Type} [Group G] [Finite G]

theorem card_coxeterGroup_reindex {ι κ : Type} (M : CoxeterMatrix ι) (e : ι ≃ κ) :
    Nat.card (M.reindex e).Group = Nat.card M.Group :=
  Nat.card_congr (CoxeterMatrix.reindexGroupEquiv M e).toEquiv

theorem card_coxeterE6_group :
    Nat.card (CoxeterMatrix.E₆).Group = 51840 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 := cartanE_eq 6
  have hmat : CoxeterMatrix.E₆ = coxeterMatrix (isFiniteType_cartan .E6) := by
    have h := coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E6)
      (M := CoxeterMatrix.E₆) (isFiniteType_cartan .E6) (hc.symm ▸ ggIntCartan_E₆)
    exact h.symm
  have hgroup : WeylGroup .E6 = (CoxeterMatrix.E₆).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (WeylGroup .E6) = Nat.card (CoxeterMatrix.E₆).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact CFSG.StandardType.NoOffExc.card_weyl_E6

theorem card_coxeterE7_group :
    Nat.card (CoxeterMatrix.E₇).Group = 2903040 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E7 = CartanMatrix.E 7 := cartanE_eq 7
  have hmat : CoxeterMatrix.E₇ = coxeterMatrix (isFiniteType_cartan .E7) := by
    have h := coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E7)
      (M := CoxeterMatrix.E₇) (isFiniteType_cartan .E7) (hc.symm ▸ ggIntCartan_E₇)
    exact h.symm
  have hgroup : WeylGroup .E7 = (CoxeterMatrix.E₇).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (WeylGroup .E7) = Nat.card (CoxeterMatrix.E₇).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact CFSG.StandardType.NoOffExc.card_weyl_E7

theorem card_coxeterE8_group :
    Nat.card (CoxeterMatrix.E₈).Group = 696729600 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E8 = CartanMatrix.E 8 := cartanE_eq 8
  have hmat : CoxeterMatrix.E₈ = coxeterMatrix (isFiniteType_cartan .E8) := by
    have h := coxeterMatrix_eq_of_ggIntCartan (C := CFSG.Blueprint.Chevalley.Tag.cartan .E8)
      (M := CoxeterMatrix.E₈) (isFiniteType_cartan .E8) (hc.symm ▸ ggIntCartan_E₈)
    exact h.symm
  have hgroup : WeylGroup .E8 = (CoxeterMatrix.E₈).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (WeylGroup .E8) = Nat.card (CoxeterMatrix.E₈).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact CFSG.StandardType.NoOffExc.card_weyl_E8

theorem ggIsWeylMatrix_E6 : GGIsWeylMatrix CoxeterMatrix.E₆ :=
  Or.inr (Or.inl ⟨Equiv.refl (Fin 6), (ggCoxeterMatrix_reindex_refl _).symm⟩)

theorem ggIsWeylMatrix_E7 : GGIsWeylMatrix CoxeterMatrix.E₇ :=
  Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), (ggCoxeterMatrix_reindex_refl _).symm⟩))

theorem ggIsWeylMatrix_E8 : GGIsWeylMatrix CoxeterMatrix.E₈ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 8), (ggCoxeterMatrix_reindex_refl _).symm⟩)))

omit [Finite G] in
theorem GGWeylOfType.weylReflectionGroup {p : ℕ} {Bs : Subgroup G} {ι : Type}
    {M : CoxeterMatrix ι} {A : Subgroup (MulAut ↥Bs)} (hM : GGIsWeylMatrix M)
    (h : GGWeylOfType p M A) : GGWeylReflectionGroup p A :=
  ⟨ι, M, hM, h⟩

theorem ggNbrSet_singleton {p : ℕ} {B : Subgroup G} {x : G} {D J : Subgroup G} {y : G}
    {K : Subgroup G} (h : GGNbr p B x D J y K) : GGNbrSet p B x D J {K} :=
  ⟨by simp, by
    intro K' hK'
    rw [Finset.mem_singleton] at hK'
    subst hK'
    exact ⟨y, h⟩⟩

end CFSG.StandardType

end
