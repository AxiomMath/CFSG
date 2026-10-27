module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2OddWords
import CFSG.Quasithin.Vol2.Ch11SecO5D
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix Polynomial CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem dvd_orderOf_mk_of {N : SL(2, K)} {n : ℕ}
    (h : ∀ j : ℕ, N ^ j ∈ Subgroup.center SL(2, K) → n ∣ j) :
    n ∣ orderOf (QuotientGroup.mk N : PSL2 K) := by
  apply h
  have h1 := pow_orderOf_eq_one (QuotientGroup.mk N : PSL2 K)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem exists_eq_scalar_of_mem_center {N : SL(2, K)} (hN : N ∈ Subgroup.center SL(2, K)) :
    ∃ c : K, c ^ 2 = 1 ∧ (N : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) c := by
  obtain ⟨c, hc, hcN⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hN
  exact ⟨c, by simpa using hc, hcN.symm⟩

@[expose] def diagSL (a : Kˣ) : SL(2, K) :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem coe_diagSL (a : Kˣ) :
    ((diagSL a : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] :=
  rfl

theorem diagSL_mul (a b : Kˣ) : diagSL a * diagSL b = diagSL (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagSL_one : diagSL (1 : Kˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagSL]

theorem diagSL_pow (a : Kˣ) (k : ℕ) : diagSL a ^ k = diagSL (a ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, diagSL_one]
  | succ k ih => rw [pow_succ, ih, diagSL_mul, pow_succ]

theorem diagSL_inv (a : Kˣ) : (diagSL a)⁻¹ = diagSL a⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [diagSL_mul, mul_inv_cancel, diagSL_one])

theorem pow_two_mul_eq_one_of_diagSL_mem_center {b : Kˣ} {j : ℕ}
    (h : diagSL b ^ j ∈ Subgroup.center SL(2, K)) : b ^ (2 * j) = 1 := by
  obtain ⟨c, -, hc⟩ := exists_eq_scalar_of_mem_center h
  rw [diagSL_pow] at hc
  have e0 := congrFun (congrFun hc 0) 0
  have e1 := congrFun (congrFun hc 1) 1
  simp only [coe_diagSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e0 e1
  have h3 : b ^ j = (b ^ j)⁻¹ := Units.ext (e0.trans e1.symm)
  rw [two_mul, pow_add]
  exact mul_eq_one_iff_eq_inv.mpr h3

theorem exists_inverted_dvd_orderOf [Finite K] {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {g : PGL2 K} (hg1 : g ≠ 1) (hg2 : g * g = 1) {n : ℕ} (hn : Odd n)
    (hnq : n ∣ Nat.card K - 1 ∨ n ∣ Nat.card K + 1) :
    ∃ y : PSL2 K, n ∣ orderOf (pglAction K g y * y⁻¹) := by
  classical
  obtain ⟨U, hUcyc, hU0, hUcard, hUinv⟩ : ∃ U : Subgroup (PGL2 K), IsCyclic U ∧
      Nat.card U ≠ 0 ∧ n ∣ Nat.card U ∧ ∀ y ∈ U, g * y * g⁻¹ = y⁻¹ := by
    rcases hnq with h | h
    · obtain ⟨U, hU, hc, hi⟩ :=
        CFSG.Quasithin.Vol2.Ch11.SecG.O5.exists_inverted_torus hKcard hK hcard hg1 hg2 true
      simp only [if_true] at hc
      exact ⟨U, hU, by omega, hc ▸ h, hi⟩
    · obtain ⟨U, hU, hc, hi⟩ :=
        CFSG.Quasithin.Vol2.Ch11.SecG.O5.exists_inverted_torus hKcard hK hcard hg1 hg2 false
      simp only [Bool.false_eq_true, if_false] at hc
      exact ⟨U, hU, by omega, hc ▸ h, hi⟩
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := U)
  have hcord : orderOf c = Nat.card U := orderOf_eq_card_of_forall_mem_zpowers hc
  set z : U := c ^ (Nat.card U / n) with hz
  have hzord : orderOf z = n := by
    rw [hz, ← hcord,
      orderOf_pow_orderOf_div (by rw [hcord]; exact hU0) (by rw [hcord]; exact hUcard)]
  have hzn : ((z : PGL2 K)) ^ n = 1 := by
    rw [← Subgroup.coe_pow, ← hzord, pow_orderOf_eq_one, Subgroup.coe_one]
  obtain ⟨y, hy⟩ := CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_pow_odd hn hzn
  have hyord : orderOf y = n := by
    rw [← orderOf_injective _ Matrix.ProjectiveSpecialLinearGroup.toPGL_injective y, hy,
      Subgroup.orderOf_coe, hzord]
  have hinv : pglAction K g y = y⁻¹ := by
    apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [toPGL_pglAction, hy, map_inv, hy]
    exact hUinv _ z.2
  refine ⟨y, ?_⟩
  rw [hinv, ← _root_.mul_inv_rev, ← sq, orderOf_inv,
    Nat.Coprime.orderOf_pow (by rw [hyord]; exact Nat.coprime_two_right.mpr hn), hyord]

@[expose] def unipSL (b : K) : SL(2, K) := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_unipSL (b : K) :
    ((unipSL b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, b; 0, 1] := rfl

theorem unipSL_mul (b c : K) : unipSL b * unipSL c = unipSL (b + c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipSL_zero : unipSL (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipSL]

theorem unipSL_inv (b : K) : (unipSL b)⁻¹ = unipSL (-b) :=
  inv_eq_of_mul_eq_one_right (by rw [unipSL_mul, add_neg_cancel, unipSL_zero])

theorem unipSL_pow (b : K) (k : ℕ) : unipSL b ^ k = unipSL (k * b) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, unipSL_zero]
  | succ k ih => rw [pow_succ, ih, unipSL_mul, Nat.cast_succ, add_mul, one_mul]

theorem orderOf_mk_unipSL {p : ℕ} [Fact p.Prime] [CharP K p] {c : K} (hc : c ≠ 0) :
    orderOf (QuotientGroup.mk (unipSL c) : PSL2 K) = p := by
  refine orderOf_mk_eq_prime Fact.out (Or.inr ?_) (by simpa [coe_unipSL] using hc)
  rw [← Matrix.SpecialLinearGroup.coe_pow, unipSL_pow, CharP.cast_eq_zero, zero_mul, unipSL_zero,
    Matrix.SpecialLinearGroup.coe_one]

@[expose] noncomputable def negDiagGL : GL (Fin 2) K where
  val := !![1, 0; 0, -1]
  inv := !![1, 0; 0, -1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_negDiagGL :
    ((negDiagGL : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, -1] := rfl

theorem exists_unipotent_dvd_orderOf {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) :
    ∃ x : PSL2 K, p ∣ orderOf (pglAction K (ProjGenLinGroup.mk negDiagGL) x * x⁻¹) := by
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  have hc : (-1 : K) + -1 ≠ 0 := by
    rw [← neg_add, neg_ne_zero, one_add_one_eq_two]
    exact h2
  refine ⟨QuotientGroup.mk (unipSL (1 : K)), dvd_of_eq ?_⟩
  have hα := pglAction_mk_mk negDiagGL (unipSL (1 : K)) (unipSL (-1 : K)) (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_negDiagGL, coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two])
  rw [hα, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, unipSL_inv, unipSL_mul,
    orderOf_mk_unipSL hc]

theorem psl2FieldAut_mk (σ : K ≃+* K) (X : SL(2, K)) :
    psl2FieldAut K σ (QuotientGroup.mk X : PSL2 K) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map σ.toRingHom X) := by
  rw [psl2FieldAut_apply]
  exact psl2RingEquiv_mk σ X

theorem exists_field_unipotent_dvd_orderOf {p : ℕ} [Fact p.Prime] [CharP K p] (σ : K ≃+* K)
    {b : K} (hb : σ b ≠ b) :
    ∃ x : PSL2 K, p ∣ orderOf (psl2FieldAut K σ x * x⁻¹) := by
  refine ⟨QuotientGroup.mk (unipSL b), dvd_of_eq ?_⟩
  have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom (unipSL b) = unipSL (σ b) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_unipSL]
  rw [psl2FieldAut_mk, hmap, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, unipSL_inv,
    unipSL_mul, ← sub_eq_add_neg, orderOf_mk_unipSL (sub_ne_zero.mpr hb)]

theorem exists_field_split_dvd_orderOf [Finite K] (σ : K ≃+* K) {r : ℕ} (hr : 2 ≤ r)
    (hK : Nat.card K = r ^ 2) (hσ : ∀ x, σ x = x ^ r) {n : ℕ} (hn : Odd n) (hnr : n ∣ r + 1) :
    ∃ x : PSL2 K, n ∣ orderOf (psl2FieldAut K σ x * x⁻¹) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf a = r ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_units, hK]
  refine ⟨QuotientGroup.mk (diagSL a), ?_⟩
  have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom (diagSL a) = diagSL (a ^ r) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_diagSL, hσ, show r ≠ 0 by omega]
  rw [psl2FieldAut_mk, hmap, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, diagSL_inv,
    diagSL_mul]
  apply dvd_orderOf_mk_of
  intro j hj
  have h1 := pow_two_mul_eq_one_of_diagSL_mem_center hj
  have e : a ^ r * a⁻¹ = a ^ (r - 1) := by
    rw [← pow_sub_one_mul (by omega : r ≠ 0), mul_assoc, mul_inv_cancel, mul_one]
  rw [e, ← pow_mul] at h1
  have h2 : r ^ 2 - 1 ∣ (r - 1) * (2 * j) := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h1
  have h3 : r ^ 2 - 1 = (r - 1) * (r + 1) := by
    have h1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, (by omega : 1 ≤ r)]
    ring
  rw [h3] at h2
  have h4 : r + 1 ∣ 2 * j := Nat.dvd_of_mul_dvd_mul_left (by omega) h2
  exact (Nat.coprime_two_right.mpr hn).dvd_of_dvd_mul_left (hnr.trans h4)

end CFSG.RankThree.PartTwo.Sec20
