module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.MatColumn
public import CFSG.GroupTheory.AlternatingFive.CommutingPair
public import CFSG.Quasithin.Background.F918Z2Swap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

theorem exists_sqModel_of_swap16 {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L₁ L₂ X : Subgroup (MulAut W)} (hX : X = L₁ ⊔ L₂)
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (ha₁ : IsAlt ↥L₁ 5) (ha₂ : IsAlt ↥L₂ 5)
    {g : MulAut W} (hgX : g ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hg : L₂ = L₁.map (MulAut.conj g).toMonoidHom) (hirr : IsIrrOn X ⊤ ⊥) (hrk : rk W = 16) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (β : W ≃* Multiplicative (Matrix (Fin 4) (Fin 4) F))
      (ρ : ↥L₁ →* Matrix.GeneralLinearGroup (Fin 4) F)
      (σ : ↥L₂ →* Matrix.GeneralLinearGroup (Fin 4) F),
      Nat.card F = 2 ∧ IsMatModel L₁ L₂ β ρ σ ∧ AlternatingNatural L₁ (matColSub β 0) ⊥ 5 := by
  classical
  haveI : Nontrivial W := by
    obtain ⟨w, -, hw⟩ := SetLike.exists_of_lt hirr.1
    exact ⟨w, 1, by simpa using hw⟩
  have hL₁ne : L₁ ≠ ⊥ := ne_bot_of_isAlt_five ha₁
  have hgX₂₁ : g ∈ Subgroup.normalizer ((L₂ ⊔ L₁ : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [sup_comm, ← hX]
    exact hgX
  have hcomm₂₁ : ∀ x ∈ L₂, ∀ y ∈ L₁, x * y = y * x :=
    fun x hx y hy => (hcomm y hy x hx).symm
  have hg' : L₁ = L₂.map (MulAut.conj g).toMonoidHom := by
    rcases CFSG.GroupTheory.AlternatingFive.map_conj_eq_or_eq_of_normalizes hcomm₂₁ ha₂ ha₁
      hgX₂₁ with h | h
    ·
      exfalso
      have hXmap : X.map (MulAut.conj g).toMonoidHom = X :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hgX
      have hsup : X.map (MulAut.conj g).toMonoidHom = L₂ := by
        rw [hX, Subgroup.map_sup, ← hg, h, sup_idem]
      have hXeq : X = L₂ := hXmap.symm.trans hsup
      have hL₁le : L₁ ≤ L₂ := by
        rw [← hXeq, hX]
        exact le_sup_left
      have hdisj : L₁ ⊓ L₂ = ⊥ := inf_eq_bot_of_commute_isAlt_five hcomm ha₁
      have hbot : L₁ = ⊥ := by
        rw [← hdisj, inf_of_le_left hL₁le]
      exact hL₁ne hbot
    · exact h.symm
  have hIrr : IsIrrOn (L₁ ⊔ L₂) ⊤ ⊥ := by
    simpa only [hX] using hirr
  have hirr' : ∀ U : Subgroup W, (∀ x ∈ L₁ ⊔ L₂, ∀ u ∈ U, x u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    exact hIrr.2.2.2 U (show StableUnder (L₁ ⊔ L₂) U from hU) bot_le le_top
  obtain ⟨F, hF, hFin, _, d, β, ρ, σ, _, _, _, hd, hM, _, _, _⟩ :=
    hasSqModel_swap_form hW hcomm hirr' hg hg'
  letI : Field F := hF
  letI : Finite F := hFin
  have hcardW : Nat.card W = 2 ^ 16 := by
    rw [card_eq_two_pow_rk hW, hrk]
  have hcardβ : Nat.card W = Nat.card F ^ (d * d) := card_eq_card_pow_of_matEquiv β
  have hd4 : d = 4 := by
    rcases matModel_column_cases hW hM ha₁ (j := ⟨0, hd⟩) with ⟨-, h, -⟩ | ⟨hF4, hd2⟩
    · exact h
    · exfalso
      have hEq : Nat.card F ^ (d * d) = 2 ^ 16 := by rw [← hcardβ, hcardW]
      rw [hF4, hd2] at hEq
      norm_num at hEq
  subst d
  rcases matModel_column_cases hW hM ha₁ (0 : Fin 4) with ⟨hF2, -, hAlt⟩ | ⟨-, hbad⟩
  · exact ⟨F, hF, hFin, β, ρ, σ, hF2, hM, hAlt⟩
  · omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
