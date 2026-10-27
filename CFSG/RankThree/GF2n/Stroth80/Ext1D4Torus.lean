module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Potential
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

@[expose] def dot4 (u v : Fin 4 → ℤ) : ℤ := ∑ i, u i * v i

@[expose] def testVec : Finset (Fin 4 → ℤ) :=
  {![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 1, 0, 0], ![1, -1, 0, 0],
    ![1, 0, 1, 0], ![1, 0, -1, 0], ![1, 0, 0, 1], ![1, 0, 0, -1], ![0, 1, 1, 0], ![0, 1, -1, 0],
    ![0, 1, 0, 1], ![0, 1, 0, -1], ![0, 0, 1, 1], ![0, 0, 1, -1]}

@[expose] def IsGoodVal (x : ℤ) : Prop := x ≠ 0 ∧ x % 3 ≠ 0 ∧ x % 7 ≠ 0 ∧ |x| ≤ 14

instance : DecidablePred IsGoodVal := fun x => by unfold IsGoodVal; infer_instance

theorem sep_self {W : Finset (Fin 4 → ℤ)} (hW : W = natWt ∨ W = evenWt ∨ W = oddWt) :
    ∀ β ∈ posRoot, ∀ ψ ∈ W, ∀ χ ∈ W, ψ - χ ≠ 0 → ψ - χ ≠ β → ψ - χ ≠ -β →
      ∃ e ∈ testVec, dot4 β e = 0 ∧ IsGoodVal (dot4 (ψ - χ) e) := by
  rcases hW with rfl | rfl | rfl <;> decide +kernel

theorem sep_mixed {W₁ W₂ : Finset (Fin 4 → ℤ)}
    (hW : (W₁ = natWt ∧ W₂ = evenWt) ∨ (W₁ = natWt ∧ W₂ = oddWt) ∨
      (W₁ = evenWt ∧ W₂ = natWt) ∨ (W₁ = evenWt ∧ W₂ = oddWt) ∨
      (W₁ = oddWt ∧ W₂ = natWt) ∨ (W₁ = oddWt ∧ W₂ = evenWt)) {a b : ℕ} (ha : a ≤ 1)
    (hb : b ≤ 1) :
    ∀ β ∈ posRoot, ∀ ψ ∈ W₁, ∀ χ ∈ W₂,
      ∃ e ∈ testVec, dot4 β e = 0 ∧ IsGoodVal (dot4 ((2 : ℤ) ^ a • ψ - (2 : ℤ) ^ b • χ) e) := by
  interval_cases a <;> interval_cases b <;>
    rcases hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    decide +kernel

section Char

variable {K : Type*} [Field K]

@[expose] def wtChar (m k : ℕ) (v : Fin 4 → ℤ) (z : Fin 4 → Kˣ) : Kˣ :=
  (∏ i, z i ^ (v i * (m : ℤ))) ^ (2 ^ k)

theorem wtChar_add (m k : ℕ) (v w : Fin 4 → ℤ) (z : Fin 4 → Kˣ) :
    wtChar m k (v + w) z = wtChar m k v z * wtChar m k w z := by
  simp only [wtChar, Pi.add_apply, add_mul, zpow_add, Finset.prod_mul_distrib, mul_pow]

theorem wtChar_zpow (m k : ℕ) (v e : Fin 4 → ℤ) (g : Kˣ) :
    wtChar m k v (fun i => g ^ e i) = g ^ ((2 : ℤ) ^ k * (dot4 v e * m)) := by
  simp only [wtChar, dot4, Fin.prod_univ_four, Fin.sum_univ_four, ← zpow_mul, ← zpow_add]
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

variable [Fintype K]

theorem exists_orderOf_eq_card_sub_one : ∃ g : Kˣ, orderOf g = Fintype.card K - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
    Nat.card_eq_fintype_card]⟩

theorem zpow_ne_one_of_isGoodVal [CharP K 2] {g : Kˣ} (hg : orderOf g = Fintype.card K - 1)
    {m : ℕ} (hm : 2 * m = Fintype.card K) (hq : 4 ≤ Fintype.card K) {x : ℤ} (hx : IsGoodVal x)
    (k : ℕ) : g ^ ((2 : ℤ) ^ k * (x * m)) ≠ 1 := by
  intro h
  rw [← orderOf_dvd_iff_zpow_eq_one, hg] at h
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  set q := Fintype.card K
  have hf2 : 2 ≤ (f : ℕ) := by
    by_contra hlt
    have : (f : ℕ) = 1 := by have := f.pos; omega
    rw [this, pow_one] at hf
    omega
  have hm' : m = 2 ^ ((f : ℕ) - 1) := by
    have : q = 2 * 2 ^ ((f : ℕ) - 1) := by rw [hf, ← pow_succ']; congr 1; omega
    omega
  have hodd : Odd (q - 1) := by
    rw [hf]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (by
      rw [Nat.even_pow]; exact ⟨even_two, by omega⟩) odd_one
  have hcop : IsCoprime ((q - 1 : ℕ) : ℤ) ((2 : ℤ) ^ (k + ((f : ℕ) - 1))) := by
    rw [show ((2 : ℤ) ^ (k + ((f : ℕ) - 1))) = ((2 ^ (k + ((f : ℕ) - 1)) : ℕ) : ℤ) by
        push_cast; rfl,
      Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have hdvd : ((q - 1 : ℕ) : ℤ) ∣ x := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [hm'] at h
    convert h using 1
    push_cast
    rw [pow_add]
    ring
  obtain ⟨hx0, hx3, hx7, hx14⟩ := hx
  have hq1 : q - 1 = 2 ^ (f : ℕ) - 1 := by rw [hf]
  rcases Nat.lt_or_ge (f : ℕ) 4 with hlt | hge
  · interval_cases hfv : (f : ℕ)
    · rw [hq1] at hdvd
      exact hx3 (Int.emod_eq_zero_of_dvd (by exact_mod_cast hdvd))
    · rw [hq1] at hdvd
      exact hx7 (Int.emod_eq_zero_of_dvd (by exact_mod_cast hdvd))
  · have h15 : 15 ≤ q - 1 := by
      rw [hq1]
      have : 2 ^ 4 ≤ 2 ^ (f : ℕ) := Nat.pow_le_pow_right (by norm_num) hge
      omega
    refine hx0 (Int.eq_zero_of_abs_lt_dvd hdvd ?_)
    have : (15 : ℤ) ≤ ((q - 1 : ℕ) : ℤ) := by exact_mod_cast h15
    linarith

end Char

theorem dot4_sub (u v e : Fin 4 → ℤ) : dot4 (u - v) e = dot4 u e - dot4 v e := by
  simp only [dot4, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dot4_smul (c : ℤ) (u e : Fin 4 → ℤ) : dot4 (c • u) e = c * dot4 u e := by
  simp only [dot4, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem posRoot_exists_two : ∀ β ∈ posRoot, ∃ i : Fin 4, β i = 2 := by decide

section Data

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem torusData_self {m : ℕ} (hm : 2 * m = Fintype.card K) (hq : 4 ≤ Fintype.card K)
    {W : Finset (Fin 4 → ℤ)} (hW : W = natWt ∨ W = evenWt ∨ W = oddWt) :
    (∀ β ∈ posRoot, ∀ z : Fin 4 → Kˣ, ∀ ψ χ : W, (ψ : Fin 4 → ℤ) = χ + β →
        wtChar m 0 (ψ : Fin 4 → ℤ) z = wtChar m 0 β z * wtChar m 0 (χ : Fin 4 → ℤ) z) ∧
    (∀ β ∈ posRoot, ∀ c : Kˣ, ∃ z : Fin 4 → Kˣ, wtChar m 0 β z = c) ∧
    (∀ β ∈ posRoot, ∀ ψ χ : W, ψ ≠ χ → (ψ : Fin 4 → ℤ) ≠ χ + β → (χ : Fin 4 → ℤ) ≠ ψ + β →
        ∃ z : Fin 4 → Kˣ, wtChar m 0 β z = 1 ∧
          wtChar m 0 (ψ : Fin 4 → ℤ) z ≠ wtChar m 0 (χ : Fin 4 → ℤ) z) := by
  classical
  refine ⟨fun β _ z ψ χ h => by rw [h, wtChar_add, mul_comm], fun β hβ c => ?_,
    fun β hβ ψ χ h1 h2 h3 => ?_⟩
  · obtain ⟨i, hi⟩ := posRoot_exists_two β hβ
    refine ⟨Pi.mulSingle i c, ?_⟩
    rw [wtChar, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
      (fun h => absurd (Finset.mem_univ i) h), Pi.mulSingle_eq_same, hi, pow_zero, pow_one]
    refine Units.ext ?_
    rw [show (2 : ℤ) * m = ((2 * m : ℕ) : ℤ) by push_cast; rfl, zpow_natCast,
      Units.val_pow_eq_pow_val,
      hm, FiniteField.pow_card]
  · obtain ⟨g, hg⟩ := exists_orderOf_eq_card_sub_one (K := K)
    obtain ⟨e, -, he0, hgood⟩ := sep_self hW β hβ ψ ψ.2 χ χ.2
      (sub_ne_zero.2 fun h => h1 (Subtype.ext h)) (fun h => h2 (eq_add_of_sub_eq' h))
      (fun h => h3 (by rw [show (χ : Fin 4 → ℤ) = ψ - (ψ - χ) by abel, h, sub_neg_eq_add]))
    refine ⟨fun i => g ^ e i, ?_, fun heq => ?_⟩
    · rw [wtChar_zpow, he0, zero_mul, mul_zero, zpow_zero]
    · rw [wtChar_zpow, wtChar_zpow] at heq
      apply zpow_ne_one_of_isGoodVal hg hm hq hgood 0
      rw [dot4_sub, sub_mul, mul_sub, zpow_sub, heq, mul_inv_cancel]

theorem torusSep_mixed {m : ℕ} (hm : 2 * m = Fintype.card K) (hq : 4 ≤ Fintype.card K)
    {W₁ W₂ : Finset (Fin 4 → ℤ)}
    (hW : (W₁ = natWt ∧ W₂ = evenWt) ∨ (W₁ = natWt ∧ W₂ = oddWt) ∨
      (W₁ = evenWt ∧ W₂ = natWt) ∨ (W₁ = evenWt ∧ W₂ = oddWt) ∨
      (W₁ = oddWt ∧ W₂ = natWt) ∨ (W₁ = oddWt ∧ W₂ = evenWt)) {a b : ℕ} (ha : a ≤ 1)
    (hb : b ≤ 1) :
    ∀ β ∈ posRoot, ∀ (ψ : W₁) (χ : W₂), ∃ z : Fin 4 → Kˣ, wtChar m 0 β z = 1 ∧
      wtChar m a (ψ : Fin 4 → ℤ) z ≠ wtChar m b (χ : Fin 4 → ℤ) z := by
  intro β hβ ψ χ
  obtain ⟨g, hg⟩ := exists_orderOf_eq_card_sub_one (K := K)
  obtain ⟨e, -, he0, hgood⟩ := sep_mixed hW ha hb β hβ ψ ψ.2 χ χ.2
  refine ⟨fun i => g ^ e i, ?_, fun heq => ?_⟩
  · rw [wtChar_zpow, he0, zero_mul, mul_zero, zpow_zero]
  · rw [wtChar_zpow, wtChar_zpow] at heq
    apply zpow_ne_one_of_isGoodVal hg hm hq hgood 0
    rw [dot4_sub, dot4_smul, dot4_smul, pow_zero, one_mul, sub_mul,
      zpow_sub, mul_assoc, mul_assoc, heq, mul_inv_cancel]

end Data

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
