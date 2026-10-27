module

public import CFSG.RankThree.PartOne.SLB4A.Basic

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank Matrix

section Unip

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def cC2 (K : Type) [Field K] (x : C2) : K := ((Multiplicative.toAdd x).val : K)

theorem cC2_one : cC2 K 1 = 0 := by simp [cC2]

theorem cC2_gen : cC2 K c2gen = 1 := by
  simp only [cC2, c2gen, toAdd_ofAdd]
  rw [show (1 : ZMod 2).val = 1 from rfl, Nat.cast_one]

theorem cC2_mul [CharP K 2] (x y : C2) : cC2 K (x * y) = cC2 K x + cC2 K y := by
  have h2 : (1 : K) + 1 = 0 := by
    have := CharP.cast_eq_zero K 2
    rw [Nat.cast_ofNat] at this
    rw [← two_mul, mul_one]
    exact this
  rcases c2_eq_one_or_gen x with rfl | rfl <;> rcases c2_eq_one_or_gen y with rfl | rfl <;>
    simp [cC2_one, cC2_gen, c2_mul_self, h2]

theorem cC2_eq_zero (x : C2) (h : cC2 K x = 0) (h1 : (1 : K) ≠ 0) : x = 1 := by
  rcases c2_eq_one_or_gen x with rfl | rfl
  · rfl
  · rw [cC2_gen] at h
    exact absurd h h1

variable (X : Fin 5 → Matrix ι ι K)

@[expose] def Xsum (v : V2 5) : Matrix ι ι K := ∑ k, cC2 K (v k) • X k

variable {X}

omit [Fintype ι] [DecidableEq ι] in
theorem Xsum_one : Xsum X (1 : V2 5) = 0 := by
  simp [Xsum, cC2_one]

omit [Fintype ι] [DecidableEq ι] in
omit [Fintype ι] [DecidableEq ι] in
theorem Xsum_mulSingle (k : Fin 5) : Xsum X (Pi.mulSingle k c2gen) = X k := by
  simp only [Xsum]
  rw [Finset.sum_eq_single k]
  · simp [cC2_gen]
  · intro l _ hl
    simp [Pi.mulSingle_eq_of_ne hl, cC2_one]
  · simp

omit [Fintype ι] [DecidableEq ι] in
theorem Xsum_mul_vec [CharP K 2] (v w : V2 5) : Xsum X (v * w) = Xsum X v + Xsum X w := by
  simp only [Xsum, Pi.mul_apply, cC2_mul, add_smul, Finset.sum_add_distrib]

theorem Xsum_mul_Xsum (hX : ∀ k l, X k * X l = 0) (v w : V2 5) :
    Xsum X v * Xsum X w = 0 := by
  simp only [Xsum, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
  rw [hX, smul_zero]

theorem one_add_Xsum_mul [CharP K 2] (hX : ∀ k l, X k * X l = 0) (v : V2 5) :
    (1 + Xsum X v) * (1 + Xsum X v) = 1 := by
  have h2 : Xsum X v + Xsum X v = 0 := by
    have : (2 : K) = 0 := by
      have := CharP.cast_eq_zero K 2
      rwa [Nat.cast_ofNat] at this
    rw [← two_smul K (Xsum X v), this, zero_smul]
  have e : (1 + Xsum X v) * (1 + Xsum X v) = 1 + (Xsum X v + Xsum X v) + Xsum X v * Xsum X v := by
    noncomm_ring
  rw [e, h2, Xsum_mul_Xsum hX]
  simp

@[expose] def uniMat [CharP K 2] (hX : ∀ k l, X k * X l = 0) (v : V2 5) : GL ι K where
  val := 1 + Xsum X v
  inv := 1 + Xsum X v
  val_inv := one_add_Xsum_mul hX v
  inv_val := one_add_Xsum_mul hX v

theorem coe_uniMat [CharP K 2] (hX : ∀ k l, X k * X l = 0) (v : V2 5) :
    ((uniMat hX v : GL ι K) : Matrix ι ι K) = 1 + Xsum X v := rfl

@[expose] def uniHom [CharP K 2] (hX : ∀ k l, X k * X l = 0) : V2 5 →* GL ι K where
  toFun := uniMat hX
  map_one' := Units.ext (by simp [coe_uniMat, Xsum_one])
  map_mul' v w := Units.ext (by
    rw [Units.val_mul]
    simp only [coe_uniMat]
    have e : (1 + Xsum X v) * (1 + Xsum X w) = 1 + (Xsum X v + Xsum X w) + Xsum X v * Xsum X w := by
      noncomm_ring
    rw [Xsum_mul_vec, e, Xsum_mul_Xsum hX, add_zero])

theorem uniHom_apply [CharP K 2] (hX : ∀ k l, X k * X l = 0) (v : V2 5) :
    uniHom hX v = uniMat hX v := rfl

theorem det_uniMat [CharP K 2] (hX : ∀ k l, X k * X l = 0) (v : V2 5) :
    ((uniMat hX v : GL ι K) : Matrix ι ι K).det = 1 := by
  have h := congrArg Matrix.det (one_add_Xsum_mul hX v)
  rw [det_mul, det_one] at h
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    rwa [Nat.cast_ofNat] at this
  rw [coe_uniMat]
  have : (Matrix.det (1 + Xsum X v) - 1) ^ 2 = 0 := by
    linear_combination h + (1 - Matrix.det (1 + Xsum X v)) * h2
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  exact sub_eq_zero.1 this

theorem exists_two_pow_five_unip [CharP K 2] (hX : ∀ k l, X k * X l = 0)
    (hind : ∀ v : V2 5, (∃ c : K, Xsum X v = Matrix.scalar ι c) → v = 1)
    (H : Subgroup (GL ι K)) (hmem : ∀ k, uniMat hX (Pi.mulSingle k c2gen) ∈ H) :
    ∃ U : Subgroup (StatedProj H), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_statedProj H (uniHom hX) ?_ ?_ ?_
  · exact exists_mem_of_mulSingle (uniHom hX) H hmem
  · intro v w
    rw [← map_mul, inv_mul_cancel]
    exact one_mem _
  · intro v hv
    obtain ⟨c, hc⟩ := mem_statedScalars_iff.1 hv
    refine hind v ⟨(c : K) - 1, ?_⟩
    rw [uniHom_apply, coe_uniMat] at hc
    rw [map_sub, ← hc]
    simp

end Unip

end CFSG.RankThree.PartOne.SLB4A
