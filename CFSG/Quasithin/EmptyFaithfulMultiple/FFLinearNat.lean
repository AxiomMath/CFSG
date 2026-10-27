module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherInvariant

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.FFL

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {n : ℕ}

abbrev slMat (g : ↥(StatedSL n K)) : Matrix (Fin n) (Fin n) K :=
  ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem slMat_mul (g h : ↥(StatedSL n K)) : slMat (g * h) = slMat g * slMat h := rfl

theorem slMat_one : slMat (1 : ↥(StatedSL n K)) = 1 := rfl

theorem slMat_mul_inv (g : ↥(StatedSL n K)) : slMat g * slMat g⁻¹ = 1 := by
  rw [← slMat_mul, mul_inv_cancel, slMat_one]

@[expose] noncomputable def unitri (n : ℕ) (K : Type) [Field K] : Subgroup ↥(StatedSL n K) :=
  (LinearFlag.unitriangular n K).map (specialLinearGroupEquivStatedSL n K).toMonoidHom

theorem isPGroup_unitri [Finite K] [CharP K 2] (hn : 1 ≤ n) : IsPGroup 2 ↥(unitri n K) := by
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 hn
  have h := P.isPGroup'
  rw [hP] at h
  exact h.map _

@[expose] noncomputable def slT {i j : Fin n} (hij : i ≠ j) (c : K) : ↥(StatedSL n K) :=
  specialLinearGroupEquivStatedSL n K (SpecialLinearGroup.transvection hij c)

theorem slMat_slT {i j : Fin n} (hij : i ≠ j) (c : K) :
    slMat (slT hij c) = transvection i j c := rfl

theorem slT_mem_unitri {i j : Fin n} (h : i < j) (c : K) : slT h.ne c ∈ unitri n K :=
  Subgroup.mem_map_of_mem _ (LinearFlag.transvection_mem_unitriangular h c)

theorem slT_mulVec {i j : Fin n} (hij : i ≠ j) (c : K) (x : Fin n → K) :
    slMat (slT hij c) *ᵥ x = x + Pi.single i (c * x j) := by
  rw [slMat_slT, LinearFlag.transvection_mulVec]

@[expose] noncomputable def slGamma {a b : Fin n} (hab : a ≠ b) : ↥(StatedSL n K) :=
  slT hab 1 * slT hab.symm 1

theorem slGamma_mulVec {a b : Fin n} (hab : a ≠ b) (x : Fin n → K) :
    slMat (slGamma hab) *ᵥ x = x + Pi.single b (x a) + Pi.single a (x b + x a) := by
  rw [slGamma, slMat_mul, ← mulVec_mulVec, slT_mulVec, slT_mulVec, one_mul, one_mul]
  congr 2
  simp

theorem slGamma_mulVec_of {a b : Fin n} (hab : a ≠ b) {x : Fin n → K} (ha : x a = 0)
    (hb : x b = 0) : slMat (slGamma hab) *ᵥ x = x := by
  rw [slGamma_mulVec, ha, hb, add_zero, Pi.single_zero, Pi.single_zero, add_zero, add_zero]

section CharTwo

variable [CharP K 2]

theorem slGamma_mulVec_fst {a b : Fin n} (hab : a ≠ b) (x : Fin n → K) :
    (slMat (slGamma hab) *ᵥ x) a = x b := by
  rw [slGamma_mulVec]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab]
  linear_combination x a * (CharTwo.two_eq_zero : (2 : K) = 0)

omit [CharP K 2] in
theorem slGamma_mulVec_snd {a b : Fin n} (hab : a ≠ b) (x : Fin n → K) :
    (slMat (slGamma hab) *ᵥ x) b = x a + x b := by
  rw [slGamma_mulVec]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm]
  ring

omit [CharP K 2] in
theorem slGamma_mulVec_other {a b : Fin n} (hab : a ≠ b) (x : Fin n → K) {k : Fin n}
    (hka : k ≠ a) (hkb : k ≠ b) : (slMat (slGamma hab) *ᵥ x) k = x k := by
  rw [slGamma_mulVec]
  simp only [Pi.add_apply, Pi.single_eq_of_ne hka, Pi.single_eq_of_ne hkb, add_zero]

theorem slGamma_pow_three {a b : Fin n} (hab : a ≠ b) : slGamma (K := K) hab ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have key : ∀ x : Fin n → K, slMat (slGamma hab) *ᵥ (slMat (slGamma hab) *ᵥ
      (slMat (slGamma hab) *ᵥ x)) = x := by
    intro x
    funext k
    by_cases hka : k = a
    · rw [hka]
      simp only [slGamma_mulVec_fst, slGamma_mulVec_snd]
      linear_combination x b * h2
    · by_cases hkb : k = b
      · rw [hkb]
        simp only [slGamma_mulVec_fst, slGamma_mulVec_snd]
        linear_combination (x a + x b) * h2
      · simp only [slGamma_mulVec_other hab _ hka hkb]
  have hmat : slMat (slGamma (K := K) hab ^ 3) = 1 := by
    rw [pow_succ, pow_succ, pow_one, slMat_mul, slMat_mul]
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, key, one_mulVec]
  exact Subtype.ext (Units.ext hmat)

theorem slGamma_ne_one {a b : Fin n} (hab : a ≠ b) : slGamma (K := K) hab ≠ 1 := by
  intro h
  have h1 := slGamma_mulVec_fst hab (Pi.single a (1 : K))
  rw [h, slMat_one, one_mulVec] at h1
  simp [hab.symm] at h1

theorem orderOf_slGamma {a b : Fin n} (hab : a ≠ b) : orderOf (slGamma (K := K) hab) = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime (slGamma_pow_three hab) (slGamma_ne_one hab)

end CharTwo

theorem slGamma_transpose {a b : Fin n} (hab : a ≠ b) :
    (slMat (slGamma (K := K) hab))ᵀ = slMat (slGamma hab) := by
  rw [slGamma, slMat_mul, transpose_mul, slMat_slT, slMat_slT, transvection, transvection,
    transpose_add, transpose_add, transpose_one, transpose_single, transpose_single]

theorem eq_zero_of_fix_unitri {x : Fin n → K} (hx : ∀ τ ∈ unitri n K, slMat τ *ᵥ x = x)
    (k : Fin n) (hk : (k : ℕ) ≠ 0) : x k = 0 := by
  have hk1 : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk
  set i : Fin n := ⟨k - 1, by omega⟩ with hi
  have hik : i < k := by rw [Fin.lt_def]; simp [hi]; omega
  have h := hx _ (slT_mem_unitri hik 1)
  rw [slT_mulVec, one_mul] at h
  have h2 := congrFun h i
  simpa using h2

theorem eq_zero_of_fix_unitri_dual {x : Fin n → K}
    (hx : ∀ τ ∈ unitri n K, (slMat τ⁻¹)ᵀ *ᵥ x = x) (k : Fin n) (hk : (k : ℕ) + 1 < n) :
    x k = 0 := by
  set j : Fin n := ⟨k + 1, hk⟩ with hj
  have hkj : k < j := by rw [Fin.lt_def]; simp [hj]
  have h := hx _ ((unitri n K).inv_mem (slT_mem_unitri hkj 1))
  rw [inv_inv, slMat_slT, transvection, transpose_add, transpose_one, transpose_single,
    ← transvection, LinearFlag.transvection_mulVec, one_mul] at h
  have h2 := congrFun h j
  simpa using h2

theorem fixesFixed_nat {a b : Fin n} (hab : a ≠ b) (ha : (a : ℕ) ≠ 0) (hb : (b : ℕ) ≠ 0) :
    FixesFixed (FFModel.nat (StatedSL n K)) (unitri n K) (slGamma hab) := by
  intro m _ hm
  obtain ⟨x, rfl⟩ : ∃ x : Fin n → K, Multiplicative.ofAdd x = m := ⟨_, rfl⟩
  have hx : ∀ τ ∈ unitri n K, slMat τ *ᵥ x = x := by
    intro τ hτ
    have h1 := Subgroup.mem_bot.mp (hm τ hτ)
    exact congrArg Multiplicative.toAdd (mul_inv_eq_one.mp h1)
  apply Subgroup.mem_bot.mpr
  apply mul_inv_eq_one.mpr
  change Multiplicative.ofAdd (slMat (slGamma hab) *ᵥ x) = Multiplicative.ofAdd x
  rw [slGamma_mulVec_of hab (eq_zero_of_fix_unitri hx a ha) (eq_zero_of_fix_unitri hx b hb)]

theorem fixesFixed_dualNat {a b : Fin n} (hab : a ≠ b) (ha : (a : ℕ) + 1 < n)
    (hb : (b : ℕ) + 1 < n) :
    FixesFixed (FFModel.dualNat (StatedSL n K)) (unitri n K) (slGamma hab) := by
  intro m _ hm
  obtain ⟨x, rfl⟩ : ∃ x : Fin n → K, Multiplicative.ofAdd x = m := ⟨_, rfl⟩
  have hx : ∀ τ ∈ unitri n K, (slMat τ⁻¹)ᵀ *ᵥ x = x := by
    intro τ hτ
    have h1 := Subgroup.mem_bot.mp (hm τ hτ)
    exact congrArg Multiplicative.toAdd (mul_inv_eq_one.mp h1)
  have hγ : slMat (slGamma (K := K) hab) *ᵥ x = x :=
    slGamma_mulVec_of hab (eq_zero_of_fix_unitri_dual hx a ha)
      (eq_zero_of_fix_unitri_dual hx b hb)
  have hγt : (slMat (slGamma (K := K) hab))ᵀ *ᵥ x = x := by rw [slGamma_transpose, hγ]
  apply Subgroup.mem_bot.mpr
  apply mul_inv_eq_one.mpr
  change Multiplicative.ofAdd ((slMat (slGamma hab)⁻¹)ᵀ *ᵥ x) = Multiplicative.ofAdd x
  congr 1
  calc (slMat (slGamma hab)⁻¹)ᵀ *ᵥ x
      = (slMat (slGamma hab)⁻¹)ᵀ *ᵥ ((slMat (slGamma hab))ᵀ *ᵥ x) := by rw [hγt]
    _ = x := by rw [mulVec_mulVec, ← transpose_mul, slMat_mul_inv, transpose_one, one_mulVec]

end CFSG.Quasithin.EmptyFaithfulMultiple.FFL
