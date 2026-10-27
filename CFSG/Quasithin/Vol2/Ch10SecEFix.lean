module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem mul_self_eq_one_of_mulVec_eq {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {g : Matrix (Fin 2) (Fin 2) F} (hdet : g.det = 1) {v : Fin 2 → F} (hv : v ≠ 0)
    (hg : g.mulVec v = v) : g * g = 1 := by
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hdet
  have key0 : ((g 0 0 - 1) * (g 1 1 - 1) - g 0 1 * g 1 0) * v 0 = 0 := by
    linear_combination (g 1 1 - 1) * h0 - g 0 1 * h1
  have key1 : ((g 0 0 - 1) * (g 1 1 - 1) - g 0 1 * g 1 0) * v 1 = 0 := by
    linear_combination (g 0 0 - 1) * h1 - g 1 0 * h0
  have hD : (g 0 0 - 1) * (g 1 1 - 1) - g 0 1 * g 1 0 = 0 := by
    by_contra hD
    apply hv
    funext i
    fin_cases i
    · exact (mul_eq_zero.mp key0).resolve_left hD
    · exact (mul_eq_zero.mp key1).resolve_left hD
  have htr : g 0 0 + g 1 1 = 0 := by linear_combination hdet - hD + h2
  have e00 : g 0 0 * g 0 0 + g 0 1 * g 1 0 = 1 := by linear_combination g 0 0 * htr - hdet - h2
  have e01 : g 0 0 * g 0 1 + g 0 1 * g 1 1 = 0 := by linear_combination g 0 1 * htr
  have e10 : g 1 0 * g 0 0 + g 1 1 * g 1 0 = 0 := by linear_combination g 1 0 * htr
  have e11 : g 1 0 * g 0 1 + g 1 1 * g 1 1 = 1 := by linear_combination g 1 1 * htr - hdet - h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, e00,
    e01, e10, e11]

@[expose] def cThree : Perm (Fin 5) := c[0, 1, 2]

@[expose] def cThree' : Perm (Fin 5) := c[2, 3, 4]

@[expose] def vThree : Fin 5 → ZMod 2 := ![0, 0, 0, 1, 1]

@[expose] def zThree : Fin 5 → ZMod 2 := ![0, 0, 1, 0, 1]

@[expose] def vTwo : Fin 5 → ZMod 2 := ![1, 1, 0, 0, 0]

theorem cThree_pow_three : cThree ^ 3 = 1 := by decide +kernel

theorem cThree'_pow_three : cThree' ^ 3 = 1 := by decide +kernel

theorem cThree_mul_self_ne_one : cThree * cThree ≠ 1 := by decide +kernel

theorem isEven_vThree : isEven vThree := by decide +kernel

theorem isEven_zThree : isEven zThree := by decide +kernel

theorem isEven_vTwo : isEven vTwo := by decide +kernel

theorem pact_cThree_vThree : pact cThree vThree = vThree := by decide +kernel

theorem pact_cThree'_zThree : pact cThree' zThree + zThree = vThree := by decide +kernel

theorem pact_cThree'_vThree : pact cThree' vThree ≠ vThree := by decide +kernel

theorem pact_cThree_sq_vTwo : pact (cThree * cThree) vTwo ≠ vTwo := by decide +kernel

end CFSG.Quasithin.Vol2.Ch10.SecE
