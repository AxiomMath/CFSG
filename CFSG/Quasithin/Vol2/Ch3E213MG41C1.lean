module

public import CFSG.GH74.Uniqueness.Bender.Psl2Subgroups
public import CFSG.Quasithin.Vol2.Ch3E213MSp4G41

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.GH74.Uniqueness.Bender

section Trace

variable {k : Type} [Field k] [CharP k 2]

theorem trace_mul_self (M : Matrix (Fin 4) (Fin 4) k) :
    Matrix.trace (M * M) = Matrix.trace M ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four]
  linear_combination (M 0 1 * M 1 0 + M 0 2 * M 2 0 + M 0 3 * M 3 0 + M 1 2 * M 2 1 +
    M 1 3 * M 3 1 + M 2 3 * M 3 2 - M 0 0 * M 1 1 - M 0 0 * M 2 2 - M 0 0 * M 3 3 -
    M 1 1 * M 2 2 - M 1 1 * M 3 3 - M 2 2 * M 3 3) * (CharTwo.two_eq_zero : (2 : k) = 0)

theorem trace_pow_two_pow (M : Matrix (Fin 4) (Fin 4) k) (j : ℕ) :
    Matrix.trace (M ^ 2 ^ j) = Matrix.trace M ^ 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_mul, pow_mul, sq, trace_mul_self, ih]

omit [CharP k 2] in
theorem glMat_pow (g : antiSp k) (n : ℕ) :
    glMat ((g ^ n : antiSp k) : GL (Fin 4) k) = glMat (g : GL (Fin 4) k) ^ n := by
  simp [glMat]

omit [CharP k 2] in
theorem trace_glMat_inv (g : antiSp k) :
    Matrix.trace (glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k)) =
      Matrix.trace (glMat (g : GL (Fin 4) k)) := by
  rw [glMat_inv_eq, Matrix.trace_mul_comm, ← Matrix.mul_assoc, minorJ_mul_self, Matrix.one_mul,
    Matrix.trace_transpose]

theorem trace_glMat_one : Matrix.trace (glMat ((1 : antiSp k) : GL (Fin 4) k)) = 0 := by
  have h4 : (4 : k) = 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num, CharTwo.two_eq_zero, zero_mul]
  simp [glMat, Matrix.trace_one, h4]

theorem trace_eq_zero_of_pow_two_pow {g : antiSp k} {j : ℕ} (hg : g ^ 2 ^ j = 1) :
    Matrix.trace (glMat (g : GL (Fin 4) k)) = 0 := by
  have h := trace_pow_two_pow (glMat (g : GL (Fin 4) k)) j
  rw [← glMat_pow, hg, trace_glMat_one] at h
  exact pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h.symm

theorem trace_frob {g : antiSp k} {m : ℕ}
    (h : g * g = 1 ∨ g ^ (2 ^ m - 1) = 1 ∨ g ^ (2 ^ m + 1) = 1) :
    Matrix.trace (glMat (g : GL (Fin 4) k)) ^ 2 ^ m =
      Matrix.trace (glMat (g : GL (Fin 4) k)) := by
  have hq : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rcases h with h | h | h
  · have h0 : Matrix.trace (glMat (g : GL (Fin 4) k)) = 0 :=
      trace_eq_zero_of_pow_two_pow (j := 1) (by rw [pow_one, sq]; exact h)
    rw [h0, zero_pow (pow_ne_zero _ two_ne_zero)]
  · have hgq : g ^ 2 ^ m = g := by
      calc g ^ 2 ^ m = g ^ (2 ^ m - 1) * g := by rw [← pow_succ, Nat.sub_add_cancel hq]
        _ = g := by rw [h, one_mul]
    rw [← trace_pow_two_pow, ← glMat_pow, hgq]
  · have hgq : g ^ 2 ^ m = g⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, h]
    rw [← trace_pow_two_pow, ← glMat_pow, hgq, trace_glMat_inv]

end Trace

section Bender

variable {K : Type*} [Group K] [Finite K]

theorem benderType_pow_cases {m : ℕ} (h : BenderType K m 1 1)
    (x : K) : x * x = 1 ∨ x ^ (2 ^ m - 1) = 1 ∨ x ^ (2 ^ m + 1) = 1 := by
  obtain ⟨s, r, hr, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  by_cases hr1 : r = 1
  · left
    apply h.sq_eq_one_of_two_pow_linear (k := s)
    rw [← orderOf_dvd_iff_pow_eq_one, hN, hr1, mul_one]
  · right
    have hdvd : 2 ^ s ∣ orderOf x := ⟨r, hN⟩
    have hy : orderOf (x ^ 2 ^ s) = r := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hN,
        Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    have hy1 : x ^ 2 ^ s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hy
      exact hr1 hy.symm
    obtain ⟨-, hcard, -⟩ := h.linear_odd_element hy1 (hy ▸ hr)
    have hxC : x ∈ Subgroup.centralizer ({x ^ 2 ^ s} : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy'
      rw [Set.mem_singleton_iff] at hy'
      rw [hy']
      exact ((Commute.refl x).pow_left _).eq
    have hpow : x ^ Nat.card (Subgroup.centralizer ({x ^ 2 ^ s} : Set K)) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hxC)
    rcases hcard with hc | hc
    · left
      rwa [hc] at hpow
    · right
      rwa [hc] at hpow

theorem benderType_sylow {m : ℕ} (h : BenderType K m 1 1)
    (S : Sylow 2 K) :
    Nat.card S = 2 ^ m ∧ ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), a * b = b * a := by
  obtain ⟨t, hc⟩ := h.exists_benderCore S
  have hSZ : rootCenter (S : Subgroup K) = (S : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
      (le_of_eq (by rw [hc.card_center, hc.card_eq, pow_one]))
  refine ⟨by rw [hc.card_eq, pow_one], fun a ha b hb => ?_⟩
  have ha' : a ∈ rootCenter (S : Subgroup K) := by
    rw [hSZ]
    exact ha
  exact ((Subgroup.mem_centralizer_iff.mp ha'.2) b hb).symm

end Bender

section FixField

variable (k : Type) [Field k] [CharP k 2]

@[expose] def fixField (m : ℕ) : Subfield k where
  carrier := {x | x ^ 2 ^ m = x}
  mul_mem' {a b} ha hb := by
    change a ^ 2 ^ m = a at ha
    change b ^ 2 ^ m = b at hb
    change (a * b) ^ 2 ^ m = a * b
    rw [mul_pow, ha, hb]
  one_mem' := one_pow _
  add_mem' {a b} ha hb := by
    change a ^ 2 ^ m = a at ha
    change b ^ 2 ^ m = b at hb
    change (a + b) ^ 2 ^ m = a + b
    rw [add_pow_char_pow, ha, hb]
  zero_mem' := zero_pow (pow_ne_zero _ two_ne_zero)
  neg_mem' {a} ha := by
    change (-a) ^ 2 ^ m = -a
    rw [CharTwo.neg_eq]
    exact ha
  inv_mem' a ha := by
    change a ^ 2 ^ m = a at ha
    change a⁻¹ ^ 2 ^ m = a⁻¹
    rw [inv_pow, ha]

variable {k}

theorem mem_fixField {m : ℕ} {x : k} : x ∈ fixField k m ↔ x ^ 2 ^ m = x :=
  Iff.rfl

variable (k)

theorem ncard_fixField_le [Finite k] {m : ℕ} (hm : 1 ≤ m) :
    (fixField k m : Set k).ncard ≤ 2 ^ m := by
  classical
  have h1 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  set p : Polynomial k := Polynomial.X ^ 2 ^ m - Polynomial.X with hp
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k h1
  have hsub : (fixField k m : Set k) ⊆ (p.roots.toFinset : Set k) := by
    intro x hx
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp0, hp,
      Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [SetLike.mem_coe, mem_fixField] at hx
    rw [hx, sub_self]
  calc (fixField k m : Set k).ncard ≤ (p.roots.toFinset : Set k).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ = 2 ^ m := FiniteField.X_pow_card_sub_X_natDegree_eq k h1

end FixField

section PSL

variable {k : Type} [Field k] [Finite k]

instance finite_sl2 : Finite (Matrix.SpecialLinearGroup (Fin 2) k) :=
  Finite.of_injective (fun A : Matrix.SpecialLinearGroup (Fin 2) k =>
    (A : Matrix (Fin 2) (Fin 2) k)) Subtype.coe_injective

instance finite_psl2 : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) :=
  Finite.of_surjective (QuotientGroup.mk : Matrix.SpecialLinearGroup (Fin 2) k → _)
    Quot.mk_surjective

theorem benderType_psl2 {n : ℕ} (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n) :
    BenderType (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) n 1 1 :=
  BenderType.linear n hn (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField k 2 n (by omega) hk) (Fin 2))

omit [Finite k] in
theorem center_sl2_eq_bot [CharP k 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by
      linear_combination hr + (1 - r) * (CharTwo.two_eq_zero : (2 : k) = 0)
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

end PSL

end CFSG.Quasithin.Ch3E213M.G41
