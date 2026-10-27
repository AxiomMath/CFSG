module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofMinusCore

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG
open scoped MatrixGroups

namespace Item211Res4Proof

theorem commute_of_kappa {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (hF4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) {T : Subgroup (MulAut Y)} {u f q : MulAut Y}
    (hu : u ∈ T) (hfT : f ∈ Subgroup.centralizer (T : Set (MulAut Y))) (hf3 : f ^ 3 = 1)
    (hfInn : f ∈ (MulAut.conj : Y →* MulAut Y).range) (κ : SL(2, F) →* MulAut Y)
    (hκInn : ∀ B, κ B ∈ (MulAut.conj : Y →* MulAut Y).range)
    (hκT : ∀ B, κ B ∈ Subgroup.centralizer (T : Set (MulAut Y)))
    (hκker : ∀ B, κ B = 1 → B = 1 ∨ B = -1) {X₀ : SL(2, F)}
    (hX₀ : ¬ Item211Lie3Proof.IsScalar2 (X₀ : Matrix (Fin 2) (Fin 2) F)) (hX₀3 : X₀ ^ 3 = 1)
    (hκf : κ X₀ = f)
    (hq : q ∈ inSubgroup (CFSG.pCore 2) (threeGen ((MulAut.conj : Y →* MulAut Y).range ⊓
      Subgroup.centralizer ({u} : Set (MulAut Y))) ⊓ Subgroup.centralizer (T : Set (MulAut Y))))
    (β : MulAut SL(2, F)) (hβ : ∀ B, κ (β B) = q * κ B * q⁻¹) :
    q * f = f * q := by
  set Δ := threeGen ((MulAut.conj : Y →* MulAut Y).range ⊓
    Subgroup.centralizer ({u} : Set (MulAut Y))) with hΔ
  set H := Δ ⊓ Subgroup.centralizer (T : Set (MulAut Y)) with hH
  set Q := inSubgroup (CFSG.pCore 2) H with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map H.subtype
  have hQN : H ≤ Subgroup.normalizer (Q : Set (MulAut Y)) := fun b hb =>
    CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H hb
  have hκu : ∀ B, κ B ∈ (MulAut.conj : Y →* MulAut Y).range ⊓
      Subgroup.centralizer ({u} : Set (MulAut Y)) := fun B =>
    Subgroup.mem_inf.mpr ⟨hκInn B, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hκT B) u hu).symm⟩
  have hfΔ : f ∈ Δ := by
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hfInn, ?_⟩, 1, by rw [pow_one, hf3]⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hfT u hu).symm
  have hκΔ : ∀ B, κ B ∈ Δ := fun B =>
    Item211Lie3Proof.mem_of_normalizer hF4 h2 κ (fun b => mem_normalizer_threeGen (hκu b))
      hX₀ hX₀3 (z := 1) (fun b => by rw [mul_one, one_mul])
      (by rw [mul_one, hκf]; exact hfΔ) B
  have hκH : ∀ B, κ B ∈ H := fun B => Subgroup.mem_inf.mpr ⟨hκΔ B, hκT B⟩
  rw [← hκf]
  exact centralizes_of_sl2_normal hF4 κ hκH hκker hQ2 hQN hq β hβ X₀

end Item211Res4Proof

end CFSG.RankThree.PartTwo.Sec21
