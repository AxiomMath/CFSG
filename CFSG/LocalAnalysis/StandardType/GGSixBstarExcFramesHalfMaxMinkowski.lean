module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.SimplyLacedCommutation

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.E6

open scoped Matrix

section Minkowski


theorem eq_one_of_modMat_weylMatrix_eq_one {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : 3 ≤ p) {w : WeylGroup τ} (h : modMat p (weylMatrix w) = 1) : w = 1 := by
  have hsymm : ∀ i : Fin τ.rank, τ.symmetrizer i i = 1 := by
    rcases hτ with rfl | rfl <;> intro i <;> simp [Tag.symmetrizer]
  refine eq_of_smul_single_eq fun i => ?_
  set α : Fin τ.rank → ℤ := Pi.single i 1 with hα
  set v : Fin τ.rank → ℤ := w • α - α with hv
  have hαα : iform α α = 2 := by
    rw [hα, iform_single_single, hsymm i, mul_one]
  have hwα : iform (w • α) (w • α) = 2 := by
    rw [iform_smul w α α, hαα]
  have hentry : ∀ j, ((v j : ℤ) : ZMod p) = 0 := by
    intro j
    have hji : modMat p (weylMatrix w) j i =
        (1 : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod p)) j i := by rw [h]
    have hcast : ((weylMatrix w j i : ℤ) : ZMod p) =
        (((Pi.single i 1 : Fin τ.rank → ℤ) j : ℤ) : ZMod p) := by
      simpa [modMat, Matrix.map_apply, Matrix.one_apply, Pi.single_apply] using hji
    rw [hv, Pi.sub_apply, hα, ← weylMatrix_apply w j i, Int.cast_sub, hcast]
    ring
  have hdvd : ∀ j, (p : ℤ) ∣ v j := by
    intro j
    have := hentry j
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  have hdvd2 : (p : ℤ) ^ 2 ∣ iform v v := by
    rw [iform]
    apply Finset.dvd_sum
    intro r _
    apply Finset.dvd_sum
    intro s _
    rcases hdvd r with ⟨a, ha⟩
    rcases hdvd s with ⟨c, hc⟩
    exact ⟨a * τ.symmetrizedCartan r s * c, by rw [ha, hc]; ring⟩
  have hpos : 0 ≤ iform (w • α + α) (w • α + α) := by
    by_cases hz : w • α + α = 0
    · rw [hz]; simp [iform]
    · exact le_of_lt (iform_self_pos hz)
  have hexp : iform (w • α + α) (w • α + α) = 4 + 2 * iform (w • α) α := by
    simp only [iform_add_left, iform_add_right]
    rw [iform_comm α (w • α), hwα, hαα]
    ring
  have hge : -2 ≤ iform (w • α) α := by
    have := hpos
    rw [hexp] at this
    omega
  have hsub : iform v v = 4 - 2 * iform (w • α) α := by
    rw [hv]
    simp only [iform_sub_left, iform_sub_right]
    rw [iform_comm α (w • α), hwα, hαα]
    ring
  have hvv_le : iform v v ≤ 8 := by
    rw [hsub]
    omega
  have hvv_nonneg : 0 ≤ iform v v := by
    by_cases hv0 : v = 0
    · rw [hv0]; simp [iform]
    · exact le_of_lt (iform_self_pos hv0)
  have hp2 : (9 : ℤ) ≤ (p : ℤ) ^ 2 := by
    have hp3 : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    nlinarith
  have hvv_zero : iform v v = 0 := by
    by_contra hne
    have hpos' : 0 < iform v v := lt_of_le_of_ne hvv_nonneg (Ne.symm hne)
    have hle : (p : ℤ) ^ 2 ≤ iform v v := Int.le_of_dvd hpos' hdvd2
    have h9 : (9 : ℤ) ≤ iform v v := le_trans hp2 hle
    omega
  have hvzero : v = 0 := by
    by_contra hvne
    exact (ne_of_gt (iform_self_pos hvne)) hvv_zero
  have hwαα : w • α = α := by
    have : w • α - α = 0 := by rw [← hv]; exact hvzero
    exact sub_eq_zero.mp this
  rw [hwαα, one_smul]

end Minkowski

end ExcFramesHalf

end CFSG.StandardType
