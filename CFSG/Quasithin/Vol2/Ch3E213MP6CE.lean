module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CC

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat minorJ minorJ_apply minorJ_mul_self mem_antiSp transpose_mul_minorJ_mul_apply)

variable {F : Type} [Field F]

theorem spBil_single (x : Fin 4 → F) (i : Fin 4) :
    spBil x (Pi.single i 1) = x (Fin.rev i) := by
  fin_cases i <;> simp [spBil_apply, Fin.rev]

theorem spBil_self [CharP F 2] (x : Fin 4 → F) : spBil x x = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [spBil_apply]
  linear_combination (x 0 * x 3 + x 1 * x 2) * h2

theorem exists_dual_pair {w w' : Fin 4 → F} (hli : LinearIndependent F ![w, w']) :
    ∃ y₀ y₁ : Fin 4 → F, spBil w y₀ = 1 ∧ spBil w' y₀ = 0 ∧ spBil w y₁ = 0 ∧ spBil w' y₁ = 1 := by
  have hminor : ∃ i j : Fin 4,
      w (Fin.rev i) * w' (Fin.rev j) - w (Fin.rev j) * w' (Fin.rev i) ≠ 0 := by
    by_contra hc
    push Not at hc
    have hw : w ≠ 0 := by simpa using hli.ne_zero 0
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have hi' : w i ≠ 0 := by simpa using hi
    set lam := w' i / w i
    have hdep : lam • w + (-1 : F) • w' = 0 := by
      ext m
      have hm := hc (Fin.rev i) (Fin.rev m)
      simp only [Fin.rev_rev] at hm
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, lam]
      field_simp
      linear_combination -hm
    have := (LinearIndependent.pair_iff.mp hli) lam (-1) hdep
    exact one_ne_zero (neg_eq_zero.mp this.2)
  obtain ⟨i, j, hp⟩ := hminor
  set p := w (Fin.rev i) * w' (Fin.rev j) - w (Fin.rev j) * w' (Fin.rev i)
  refine ⟨p⁻¹ • (w' (Fin.rev j) • Pi.single i 1 - w' (Fin.rev i) • Pi.single j 1),
    p⁻¹ • (w (Fin.rev i) • Pi.single j 1 - w (Fin.rev j) • Pi.single i 1), ?_, ?_, ?_, ?_⟩ <;>
    simp only [map_smul, map_sub, spBil_single, smul_eq_mul] <;> field_simp <;> ring

theorem exists_antiSp_flag [CharP F 2] {w w' : Fin 4 → F} (hli : LinearIndependent F ![w, w'])
    (hww : spBil w w' = 0) :
    ∃ z : antiSp F, natAct z (Pi.single 0 1) = w ∧ natAct z (Pi.single 1 1) = w' := by
  obtain ⟨y₀, y₁, h1, h2, h3, h4⟩ := exists_dual_pair hli
  set y' := y₁ + spBil y₁ y₀ • w with hy'
  have hc2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e1 : spBil w y' = 0 := by simp [hy', h3, spBil_self]
  have e2 : spBil w' y' = 1 := by simp [hy', h4, spBil_comm w' w, hww]
  have e3 : spBil y' y₀ = 0 := by
    simp only [hy', map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h1,
      smul_eq_mul, mul_one]
    linear_combination spBil y₁ y₀ * hc2
  set cols : Fin 4 → Fin 4 → F := ![w, w', y', y₀] with hcols
  set Z : Matrix (Fin 4) (Fin 4) F := Matrix.of fun r s => cols s r with hZ
  have hgram : ∀ s t, spBil (cols s) (cols t) = minorJ F s t := by
    intro s t
    fin_cases s <;> fin_cases t <;>
      simp [hcols, minorJ_apply, spBil_self, h1, h2, e1, e2, e3, hww, spBil_comm w' w,
        spBil_comm y' w, spBil_comm y' w', spBil_comm y₀ w, spBil_comm y₀ w', spBil_comm y₀ y']
  have hJ : Z.transpose * minorJ F * Z = minorJ F := by
    ext s t
    rw [transpose_mul_minorJ_mul_apply, ← hgram, spBil_apply]
    simp [hZ]
  have hleft : (minorJ F * Z.transpose * minorJ F) * Z = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Z.transpose, hJ, minorJ_mul_self]
  have hright : Z * (minorJ F * Z.transpose * minorJ F) = 1 := mul_eq_one_comm.mp hleft
  refine ⟨⟨⟨Z, minorJ F * Z.transpose * minorJ F, hright, hleft⟩, hJ⟩, ?_, ?_⟩
  · change Matrix.mulVec Z (Pi.single 0 1) = w
    ext r
    simp [hZ, hcols, Matrix.mulVec, dotProduct, Pi.single_apply]
  · change Matrix.mulVec Z (Pi.single 1 1) = w'
    ext r
    simp [hZ, hcols, Matrix.mulVec, dotProduct, Pi.single_apply]

end CFSG.Quasithin.Ch3E213M
