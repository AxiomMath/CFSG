module

public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LieType.Universal.SpinOmega.Kernel

public section

namespace CFSG.RankThree.PartOne.CTP

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin

theorem center_spinGroup_quadMinus_eq_bot {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 4 ≤ n) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center (spinGroup (quadMinus n F b c)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [← (spinToStatedProj_quadMinus hn hirr).2.2, (spinToStatedProj_quadMinus hn hirr).2.1,
    Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hx
  obtain ⟨d, hd⟩ := mem_scalars.mp hx
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero_of_hypPair _
    (minusPair F b c (⟨0, by omega⟩ : Fin (n - 1)))
  have hd2 : d * d = 1 := by
    have h := map_spinAction (quadMinus n F b c) x v₀
    rw [hd, map_smul_eq_sq] at h
    have h' : (d ^ 2 - 1) * (quadMinus n F b c) v₀ = 0 := by rw [sub_mul, h, one_mul, sub_self]
    linear_combination (mul_eq_zero.mp h').resolve_right hv₀
  have hd1 : d = 1 := by
    rcases mul_self_eq_one_iff.mp hd2 with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq]
  have := isCentral_cliffordAlgebra_quadMinus n b c hirr
  have hker := ker_spinAction_eq_bot_of_isCentral (quadMinus n F b c) CharTwo.two_eq_zero
  have hxker : x ∈ (spinAction (quadMinus n F b c)).ker := by
    rw [MonoidHom.mem_ker]
    exact LinearEquiv.ext fun v => by rw [hd, hd1, one_smul]; rfl
  rw [hker] at hxker
  exact hxker

end CFSG.RankThree.PartOne.CTP
