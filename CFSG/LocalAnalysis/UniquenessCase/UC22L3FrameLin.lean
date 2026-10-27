module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3FrameSplit
import CFSG.LocalAnalysis.UniquenessCase.UC22L3FrameMap
import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinFrame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

private theorem card_sl_two (K : Type) [Field K] [Fintype K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Fintype.card K * (Fintype.card K ^ 2 - 1) := by
  have h1 := Matrix.card_SL_mul_card_units (n := Fin 2) (R := K)
  rw [Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_units, Nat.card_eq_fintype_card (α := K)]
    at h1
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h1
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have e : Fintype.card K ^ 2 - Fintype.card K = Fintype.card K * (Fintype.card K - 1) := by
    rw [Nat.mul_sub, mul_one, sq]
  rw [e, ← mul_assoc] at h1
  have h2 := Nat.eq_of_mul_eq_mul_right (by omega) h1
  rw [h2, mul_comm]

theorem l3FrameExists_psl : L3FrameExists .PSL := by
  intro X _ _ p hp hp5 hX
  have : Fact p.Prime := ⟨hp⟩
  have hXm : CFSG.Open.StatedClassicalModel X .PSL 3 p 1 := by
    rcases hX with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨hadm, K, _, _, hK, ⟨e₁⟩⟩ := hXm
  let φ : X ≃* projectiveSL 3 K := (e₁.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have hcard : Nat.card K = p := by rw [hK, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hcard])
  have hY : CFSG.Open.StatedClassicalModel (projectiveSL 3 K) .PSL 3 p 1 :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨φ.symm.trans e₁⟩⟩
  set Fr := L3Lin.linFrame hp5 hcard hY with hFr
  set Ψ : MulAut X ≃* MulAut (projectiveSL 3 K) := MulAut.congr φ with hΨ
  have hΨconj : ∀ x : X, Ψ (MulAut.conj x) = MulAut.conj (φ x) := by
    intro x
    ext y
    simp [hΨ, MulAut.congr_apply, MulAut.conj_apply, map_mul, map_inv]
  refine ⟨?_, K, inferInstance, inferInstance, inferInstance, Fr.comap Ψ, ?_,
    (blockSub (F := K)).map φ.symm.toMonoidHom, ?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : φ z ∈ Subgroup.center (projectiveSL 3 K) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨x, rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_mul, hz x]
    rw [center_projectiveSL_three_eq_bot, Subgroup.mem_bot] at hz'
    exact φ.injective (hz'.trans (map_one φ).symm)
  ·
    rw [L3Frame.comap_I, hFr, L3Lin.linFrame_I]
    ext α
    rw [Subgroup.mem_comap, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨φ.symm y, Ψ.injective ?_⟩
      rw [hΨconj, MulEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨x, rfl⟩
      exact ⟨φ x, (hΨconj x).symm⟩
  ·
    have h4 : 4 ≤ Nat.card K := by omega
    rw [← Subgroup.map_commutator, L3Lin.commutator_blockSub h4]
  ·
    rw [Subgroup.card_map_of_injective φ.symm.injective, blockSub,
      ← Nat.card_congr (MonoidHom.ofInjective (blockEmb_injective (F := K))).toEquiv,
      card_sl_two, ← Nat.card_eq_fintype_card, hcard]
  ·
    rw [L3Frame.comap_Kb, hFr, L3Lin.linFrame_Kb]
    ext α
    rw [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, hbe⟩
      refine ⟨φ.symm b, ⟨b, hb, rfl⟩, Ψ.injective ?_⟩
      rw [hΨconj, MulEquiv.apply_symm_apply]
      exact hbe
    · rintro ⟨x, ⟨b, hb, rfl⟩, rfl⟩
      refine ⟨b, hb, ?_⟩
      show MulAut.conj b = Ψ (MulAut.conj (φ.symm b))
      rw [hΨconj, MulEquiv.apply_symm_apply]

end CFSG.LocalAnalysis.UniquenessCase.UC22
