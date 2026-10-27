module

public import CFSG.RankThree.PartOne.KF.QuadAlg
public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.RankThree.PartOne.KFQ

variable (K : Type) [Field K] [Finite K] [CharP K 2]

abbrev Qext : Type := FiniteField.Extension K 2 2

noncomputable def frobQ : Qext K ≃ₐ[K] Qext K := FiniteField.Extension.frob K 2 2

variable {K}

theorem frobQ_apply (x : Qext K) : frobQ K x = x ^ Nat.card K := by
  simp [frobQ]

theorem frobQ_frobQ (x : Qext K) : frobQ K (frobQ K x) = x := by
  have h : Nat.card (Qext K) = Nat.card K ^ 2 := FiniteField.natCard_extension K 2 2
  have := Fintype.ofFinite (Qext K)
  rw [frobQ_apply, frobQ_apply, ← pow_mul, ← sq, ← h, ← Fintype.card_eq_nat_card,
    FiniteField.pow_card]

theorem gal_cases (τ : Qext K ≃ₐ[K] Qext K) : τ = 1 ∨ τ = frobQ K := by
  obtain ⟨i, hi, rfl⟩ := FiniteField.Extension.exists_frob_pow_eq K 2 2 τ
  interval_cases i
  · left; simp
  · right; simp [frobQ]

theorem finrank_qext : Module.finrank K (Qext K) = 2 := FiniteField.finrank_extension K 2 2

theorem frobQ_eq_inv {x : Qext K} (hx : x ^ (Nat.card K + 1) = 1) : frobQ K x = x⁻¹ := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero _)] at hx
    exact zero_ne_one hx
  rw [frobQ_apply]
  apply eq_inv_of_mul_eq_one_right
  rw [← pow_succ', hx]

variable {p : ℕ}

omit [CharP K 2] in
theorem not_dvd_pred (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    ¬ p ∣ Nat.card K - 1 := by
  intro h
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have h2 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq h
  have : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
  rw [this] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem eq_one_of_mem_range {x : Qext K} (hp : p.Prime) (hnd : ¬ p ∣ Nat.card K - 1)
    (hxp : x ^ p = 1) (hxK : x ∈ Set.range (algebraMap K (Qext K))) : x = 1 := by
  obtain ⟨a, rfl⟩ := hxK
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow hp.ne_zero] at hxp
    exact zero_ne_one hxp
  have h1 : a ^ p = 1 := by
    apply (algebraMap K (Qext K)).injective
    rw [map_pow, hxp, map_one]
  have h2 : a ^ (Nat.card K - 1) = 1 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one a ha0
  have hcop : Nat.Coprime p (Nat.card K - 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
  have h3 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf a ∣ Nat.card K - 1 := orderOf_dvd_of_pow_eq_one h2
  have : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hcop h3 h4
  rw [orderOf_eq_one_iff.mp this, map_one]

theorem exists_root_not_mem (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    ∃ m : Qext K, m ^ p = 1 ∧ m ≠ 1 ∧ m ∉ Set.range (algebraMap K (Qext K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card (Qext K)ˣ := by
    rw [Nat.card_units, FiniteField.natCard_extension K 2 2]
    have : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      have hq : 1 ≤ Nat.card K := Nat.card_pos
      cases h : Nat.card K with
      | zero => omega
      | succ n => simp [sq]; ring_nf; omega
    rw [this]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hcard
  refine ⟨u, ?_, ?_, fun hK => ?_⟩
  · have := pow_orderOf_eq_one u
    rw [hu] at this
    simpa using congrArg Units.val this
  · intro h1
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    exact hp.one_lt.ne hu
  · have hpow : (u : Qext K) ^ p = 1 := by
      have := pow_orderOf_eq_one u
      rw [hu] at this
      simpa using congrArg Units.val this
    have h1 := eq_one_of_mem_range hp (not_dvd_pred hp hp2 hpq) hpow hK
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    exact hp.one_lt.ne hu

theorem span_roots_eq_top (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    Submodule.span K {x : Qext K | x ^ p = 1} = ⊤ := by
  obtain ⟨m, hmp, hm1, hmK⟩ := exists_root_not_mem hp hp2 hpq
  have hli : LinearIndependent K ![(1 : Qext K), m] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hmK
      refine ⟨-(s / t), ?_⟩
      have h1 : t • m = -(s • (1 : Qext K)) := eq_neg_of_add_eq_zero_right hst
      have h2 : m = (t⁻¹) • (t • m) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, h1, smul_neg, smul_smul, Algebra.algebraMap_eq_smul_one]
      simp [div_eq_inv_mul]
  have hspan : Submodule.span K (Set.range ![(1 : Qext K), m]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [finrank_qext])
  rw [eq_top_iff, ← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · simp
  · exact hmp

end CFSG.RankThree.PartOne.KFQ
