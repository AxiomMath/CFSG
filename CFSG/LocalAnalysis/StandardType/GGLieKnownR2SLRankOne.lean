module

public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.LieKnownR2.SpecialLinearNC

open CFSG.Open CFSG.LieType.Universal

private theorem fin_two_cases {i j : Fin 2} (hij : i ≠ j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  fin_cases i <;> fin_cases j <;> simp_all

private theorem fin_two_eq_or {i j : Fin 2} (hij : i ≠ j) (p : Fin 2) : p = i ∨ p = j := by
  fin_cases i <;> fin_cases j <;> fin_cases p <;> simp_all

private theorem pow_mulVec_of_mulVec_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [CommRing F]
    {A : Matrix ι ι F} {v : ι → F} {l : F} (h : A.mulVec v = l • v) (n : ℕ) :
    (A ^ n).mulVec v = l ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
    congr 1
    ring

theorem pCoreOf_normalizer_rootSubgroup_le {F : Type} [Field F] [CharP F 2] {i j : Fin 2}
    (hij : i ≠ j) :
    pCoreOf 2 (Subgroup.normalizer
      ((SpecialLinear.rootSubgroup 1 F hij : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F))) ≤ SpecialLinear.rootSubgroup 1 F hij := by
  intro x hx
  have hxN := GGRootNorm.pCoreOf_le _ hx
  obtain ⟨k, hk⟩ := GGRootNorm.isPGroup_pCoreOf _ ⟨x, hx⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨c, hc⟩ := (SpecialLinear.mem_rootSubgroup hij _).1
    ((Subgroup.mem_normalizer_iff.1 hxN _).1 (SpecialLinear.transvection_mem_rootSubgroup hij 1))
  have h2 : Matrix.SpecialLinearGroup.transvection hij c * x =
      x * Matrix.SpecialLinearGroup.transvection hij (1 : F) := by
    rw [hc, inv_mul_cancel_right]
  have h3 := congrFun (congrFun (congrArg
    (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) h2) j) j
  have hji : (x : Matrix (Fin 2) (Fin 2) F) j i = 0 := by
    simpa [Matrix.SpecialLinearGroup.transvection_coe, add_mul, mul_add, hij.symm] using h3
  have hv : (x : Matrix (Fin 2) (Fin 2) F).mulVec (Pi.single i 1) =
      (x : Matrix (Fin 2) (Fin 2) F) i i • (Pi.single i 1 : Fin 2 → F) := by
    funext p
    rw [Matrix.mulVec_single_one]
    rcases fin_two_eq_or hij p with h | h
    · subst h
      simp
    · subst h
      simp [hji, hij.symm]
  have hpow := pow_mulVec_of_mulVec_eq hv (2 ^ k)
  have hxk' : (x : Matrix (Fin 2) (Fin 2) F) ^ 2 ^ k = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hxk, Matrix.SpecialLinearGroup.coe_one]
  rw [hxk', Matrix.one_mulVec] at hpow
  have hl : (x : Matrix (Fin 2) (Fin 2) F) i i ^ 2 ^ k = 1 := by
    simpa using (congrFun hpow i).symm
  have hii : (x : Matrix (Fin 2) (Fin 2) F) i i = 1 := by
    have h4 : ((x : Matrix (Fin 2) (Fin 2) F) i i - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, hl, one_pow, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by positivity)).1 h4)
  have hdet : (x : Matrix (Fin 2) (Fin 2) F) i i * (x : Matrix (Fin 2) (Fin 2) F) j j -
      (x : Matrix (Fin 2) (Fin 2) F) i j * (x : Matrix (Fin 2) (Fin 2) F) j i = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe x
    rw [Matrix.det_fin_two] at this
    rcases fin_two_cases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linear_combination this
  have hjj : (x : Matrix (Fin 2) (Fin 2) F) j j = 1 := by
    simpa [hii, hji] using hdet
  rw [SpecialLinear.mem_rootSubgroup hij]
  refine ⟨(x : Matrix (Fin 2) (Fin 2) F) i j, ?_⟩
  refine Matrix.SpecialLinearGroup.ext _ _ fun p q => ?_
  rcases fin_two_eq_or hij p with hp | hp <;> rcases fin_two_eq_or hij q with hq | hq <;>
    subst hp <;> subst hq <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply, hii,
      hjj, hji, hij, hij.symm]

end CFSG.StandardType.LieKnownR2.SpecialLinearNC
