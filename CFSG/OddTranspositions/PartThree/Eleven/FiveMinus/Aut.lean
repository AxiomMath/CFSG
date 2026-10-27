module

public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.ComponentClassification.ExactGenPSp45Out
import CFSG.Sporadic.Recognition.LyonsAmalgamExtAut

public section

namespace CFSG.OddTranspositions.PartThree

theorem card_mulAut_le_two_mul_card_of_lieModel_psp_two_five {S : Type} [Group S] [Finite S]
    (h : CFSG.Blueprint.LieModel S .PSp 2 5 1) : Nat.card (MulAut S) ≤ 2 * Nat.card S := by
  have h1 : Nat.card (MulAut S) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) *
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
  have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) ≤
      Nat.card S :=
    Nat.card_le_card_of_surjective
      (MulAut.conj : S →* MulAut S).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  have h3 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤ 2 :=
    CFSG.ComponentClassification.SolMax.SwapP2.ExactPSp45.outer_psp45_le_two S h
  rw [h1]
  exact Nat.mul_le_mul h3 h2

theorem card_eq_two_mul_card_of_centralizer_eq_bot {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (hC : Subgroup.centralizer (N : Set G) = ⊥)
    (hAut : Nat.card (MulAut N) ≤ 2 * Nat.card N) (hN : N ≠ ⊤) :
    Nat.card G = 2 * Nat.card N := by
  haveI : Finite (G ⧸ N) := ((finite_iff_subgroup_quotient N).mp inferInstance).2
  have hinj : Function.Injective (MulAut.conjNormal : G →* MulAut N) :=
    CFSG.Sporadic.Recognition.LyonsSims.conjNormal_injective_of_centralizer_eq_bot N hC
  have hle : Nat.card G ≤ Nat.card (MulAut N) := Nat.card_le_card_of_injective _ hinj
  have hidx : Nat.card N * N.index = Nat.card G := N.card_mul_index
  have h2 : 2 ≤ N.index := by
    have := N.one_lt_index_of_ne_top hN
    omega
  apply le_antisymm
  · calc Nat.card G ≤ Nat.card (MulAut N) := hle
      _ ≤ 2 * Nat.card N := hAut
  · calc 2 * Nat.card N = Nat.card N * 2 := Nat.mul_comm _ _
      _ ≤ Nat.card N * N.index := Nat.mul_le_mul_left _ h2
      _ = Nat.card G := hidx

theorem nonempty_mulEquiv_of_centralizer_eq_bot_of_card_eq {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    [Finite G₁] [Finite G₂] {N₁ : Subgroup G₁} {N₂ : Subgroup G₂} [N₁.Normal] [N₂.Normal]
    (ε : N₁ ≃* N₂) (h₁ : Subgroup.centralizer (N₁ : Set G₁) = ⊥)
    (h₂ : Subgroup.centralizer (N₂ : Set G₂) = ⊥) (hcard : Nat.card G₁ = Nat.card G₂)
    (hAut : Nat.card (MulAut N₁) ≤ Nat.card G₁) : Nonempty (G₁ ≃* G₂) := by
  have hcardAut : Nat.card (MulAut N₂) = Nat.card (MulAut N₁) :=
    (Nat.card_congr (MulAut.congr ε).toEquiv).symm
  have hAut₂ : Nat.card (MulAut N₂) ≤ Nat.card G₂ := by
    rw [hcardAut, ← hcard]
    exact hAut
  refine ⟨(CFSG.Sporadic.Recognition.LyonsSims.conjNormalEquiv N₁ h₁ hAut).trans
    ((MulAut.congr ε).trans
      (CFSG.Sporadic.Recognition.LyonsSims.conjNormalEquiv N₂ h₂ hAut₂).symm)⟩

end CFSG.OddTranspositions.PartThree
