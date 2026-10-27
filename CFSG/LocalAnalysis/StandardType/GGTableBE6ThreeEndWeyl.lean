module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

namespace E6ThreeEnd

variable {τ : Tag}

theorem iform_eq_sum (x y : Fin τ.rank → ℤ) :
    iform x y = ∑ l, y l * iform x (Pi.single l 1) := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring


theorem eq_one_of_fix_of_pow_three (j₀ : Fin τ.rank) {w : WeylGroup τ}
    (hfix : ∀ i, i ≠ j₀ → w • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single i 1)
    (h3 : w ^ 3 = 1) : w = 1 := by
  set e : Fin τ.rank → ℤ := Pi.single j₀ 1 with he
  set u : Fin τ.rank → ℤ := w • e - e with hu
  have hwe : w • e = e + u := by
    rw [hu]
    abel
  have horth : ∀ i, i ≠ j₀ → iform u (Pi.single i 1) = 0 := by
    intro i hi
    have h1 : iform (w • e) (Pi.single i 1) = iform e (Pi.single i 1) := by
      conv_lhs => rw [← hfix i hi]
      exact iform_smul w e _
    rw [hu, iform_sub_left, h1, sub_self]
  have hexp : iform u u = u j₀ * iform u e := by
    rw [iform_eq_sum u u, Finset.sum_eq_single j₀ (fun l _ hl => by rw [horth l hl, mul_zero])
      (by simp)]
  have hinv : iform (e + u) (e + u) = iform e e := by
    rw [← hwe]
    exact iform_smul w e e
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm e u] at hinv
  have key : (u j₀ + 2) * iform u e = 0 := by
    linear_combination hinv - hexp
  have hk : ∀ k, w • (Pi.single k 1 : Fin τ.rank → ℤ) =
      Pi.single k 1 + if k = j₀ then u else 0 := by
    intro k
    by_cases hkj : k = j₀
    · rw [hkj]
      simp only [ite_true]
      exact hwe
    · simp only [hkj, ite_false, add_zero]
      exact hfix k hkj
  have hext : ∀ w' : WeylGroup τ, w' • e = e →
      (∀ i, i ≠ j₀ → w' • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single i 1) → w' = 1 := by
    intro w' hw' hfix'
    refine ext_single fun i => ?_
    rw [one_smul]
    by_cases hi : i = j₀
    · rw [hi]
      exact hw'
    · exact hfix' i hi
  rcases mul_eq_zero.mp key with h | h
  ·
    have hu0 : u j₀ = -2 := by linarith
    have hlin : ∀ v : Fin τ.rank → ℤ, w • v = v + v j₀ • u := by
      intro v
      rw [TableBExc.E6Three.weyl_smul_eq_sum w v]
      simp only [hk, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      congr 1
      conv_rhs => rw [← Finset.univ_sum_single v]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    have hej : (e + u) j₀ = -1 := by
      rw [Pi.add_apply, hu0, he, Pi.single_eq_same]
      norm_num
    have hw2 : (w * w) • e = e := by
      rw [mul_smul, hwe, hlin (e + u), hej, neg_one_smul, add_neg_cancel_right]
    have hww : w * w = 1 := hext _ hw2 fun i hi => by rw [mul_smul, hfix i hi, hfix i hi]
    calc w = w ^ 3 * (w * w)⁻¹ := by group
      _ = 1 := by rw [h3, hww, inv_one, one_mul]
  ·
    have huu : iform u u = 0 := by rw [hexp, h, mul_zero]
    have hu0 : u = 0 := by
      by_contra hne
      exact absurd huu (ne_of_gt (iform_self_pos hne))
    exact hext w (by rw [hwe, hu0, add_zero]) hfix

end E6ThreeEnd

end CFSG.StandardType
