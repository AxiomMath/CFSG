module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.L3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] [Finite K]

omit [Field K] [Finite K] in
theorem not_three_dvd {f : ℕ} (hf : Odd f) (hK : Nat.card K = 2 ^ f) : ¬ 3 ∣ Nat.card K - 1 := by
  obtain ⟨k, rfl⟩ := hf
  rw [hK]
  have h1 : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * k + 1) = N at h1 ⊢
  omega

section Cube

variable (h3 : ¬ 3 ∣ Nat.card K - 1)
include h3

omit [Finite K] in
theorem eq_one_of_pow_three_eq_one {c : Kˣ} (hc : c ^ 3 = 1) : c = 1 := by
  have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc
  have h2 : orderOf c ∣ Nat.card Kˣ := orderOf_dvd_natCard c
  rw [Nat.card_units] at h2
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h2) h3

omit [Finite K] in
theorem scalars_three_eq_bot : scalars 3 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  rw [Subgroup.mem_bot]
  have hc1 := eq_one_of_pow_three_eq_one h3 hc
  subst hc1
  apply Subtype.ext
  change (A : Matrix (Fin 3) (Fin 3) K) = 1
  rw [hA, Units.val_one, map_one]

omit [Finite K] in
theorem proj_injective : Function.Injective (proj 3 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_three_eq_bot h3]

theorem linearAutGroup_le_inner : linearAutGroup 3 K ≤ inner (projectiveSL 3 K) := by
  have h1 := UnitaryHigher.relIndex_inner_linearAutGroup_dvd (k := K) (n := 3) (by norm_num)
  have h2 : Nat.gcd 3 (Nat.card K - 1) = 1 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)).symm
  rw [h2, Nat.dvd_one] at h1
  exact Subgroup.relIndex_eq_one.mp h1

end Cube

omit [Finite K] in
theorem exists_pow_conjAut_fieldAut (A : GL (Fin 3) K) (σ : K ≃+* K) (m : ℕ) :
    ∃ B : GL (Fin 3) K,
      (conjAut 3 K A * fieldAut 3 K σ) ^ m = conjAut 3 K B * fieldAut 3 K (σ ^ m) := by
  induction m with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, one_mul]⟩
  | succ m ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B * GeneralLinearGroup.map ((σ ^ m : K ≃+* K) : K →+* K) A, ?_⟩
    rw [pow_succ, hB, conjAut_mul_fieldAut_mul, pow_succ]

theorem fieldAut_mem_of_pow_mem {σ : K ≃+* K} {m : ℕ} (hm : Nat.Coprime m (Nat.card (RingAut K)))
    (h : fieldAut 3 K σ ^ m ∈ linearAutGroup 3 K) : fieldAut 3 K σ ∈ linearAutGroup 3 K := by
  set f := Nat.card (RingAut K) with hf
  have : Finite (RingAut K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    DFunLike.coe_injective
  have hσf : σ ^ f = 1 := pow_card_eq_one'
  have hff : fieldAut 3 K σ ^ f = 1 := by rw [← map_pow, hσf, map_one]
  have hm' : Nat.Coprime m (orderOf (fieldAut 3 K σ)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hff) hm
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hm'
  rw [← hu]
  exact pow_mem h u

theorem two_elt_cases {f : ℕ} (hf : Odd f) (hK : Nat.card K = 2 ^ f)
    (α : MulAut (projectiveSL 3 K)) {k : ℕ} (hα : α ^ (2 ^ k) = 1) :
    ∃ x : projectiveSL 3 K, α = MulAut.conj x ∨ α = MulAut.conj x * dualAut 3 K := by
  have h3 := not_three_dvd hf hK
  have htrans := standard_automorphism_transport (K := K) (n := 3)
  have hcard : Nat.card (RingAut K) = f :=
    (card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have hcop : ∀ j : ℕ, Nat.Coprime (2 ^ j) (Nat.card (RingAut K)) := fun j => by
    rw [hcard]
    exact Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hf)
  have hE : ∀ (A : GL (Fin 3) K) (σ : K ≃+* K) (j : ℕ),
      (conjAut 3 K A * fieldAut 3 K σ) ^ (2 ^ j) = 1 → fieldAut 3 K σ ∈ linearAutGroup 3 K := by
    intro A σ j hj
    obtain ⟨B, hB⟩ := exists_pow_conjAut_fieldAut A σ (2 ^ j)
    rw [hj] at hB
    have h1 : fieldAut 3 K σ ^ (2 ^ j) = conjAut 3 K B⁻¹ := by
      rw [← map_pow, map_inv]
      exact eq_inv_of_mul_eq_one_right hB.symm
    exact fieldAut_mem_of_pow_mem (hcop j) (h1 ▸ conjAut_mem_linearAutGroup _)
  have hinn : ∀ x ∈ linearAutGroup 3 K, ∃ y : projectiveSL 3 K, x = MulAut.conj y := by
    intro x hx
    obtain ⟨y, hy⟩ := linearAutGroup_le_inner h3 hx
    exact ⟨y, hy.symm⟩
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) (le_refl 3)).2 α
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one] at hα ⊢
    have hσ := hE A σ k hα
    obtain ⟨y, hy⟩ := hinn _ (mul_mem (conjAut_mem_linearAutGroup A) hσ)
    exact ⟨y, Or.inl hy⟩
  · rw [pow_one] at hα ⊢
    have hsq : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) ^ 2 =
        conjAut 3 K A * fieldAut 3 K σ *
          (conjAut 3 K (GeneralLinearGroup.inverseTranspose A) * fieldAut 3 K σ) := by
      have hδδ := htrans.2.2.2.1
      have key : conjAut 3 K A * fieldAut 3 K σ *
          ((dualAut 3 K * conjAut 3 K A * dualAut 3 K) *
            (dualAut 3 K * fieldAut 3 K σ * dualAut 3 K)) =
          (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) *
            (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) := by
        calc _ = conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K * conjAut 3 K A *
              (dualAut 3 K * dualAut 3 K) * fieldAut 3 K σ * dualAut 3 K := by group
          _ = _ := by rw [hδδ]; group
      rw [sq, ← key, htrans.2.2.2.2.1 A, htrans.2.2.2.2.2.1 σ]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, pow_one] at hα
      exact ⟨1, Or.inl (by rw [hα, map_one])⟩
    · have hsq' : (conjAut 3 K A * fieldAut 3 K σ *
          (conjAut 3 K (GeneralLinearGroup.inverseTranspose A) * fieldAut 3 K σ)) ^ (2 ^ (k - 1))
          = 1 := by
        rw [← hsq, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hk, hα]
      rw [conjAut_mul_fieldAut_mul] at hsq'
      have hσ2 := hE _ _ _ hsq'
      have hσ : fieldAut 3 K σ ∈ linearAutGroup 3 K := by
        refine fieldAut_mem_of_pow_mem (hcop 1) ?_
        rw [pow_one, ← map_pow, sq]
        exact hσ2
      obtain ⟨y, hy⟩ := hinn _ (mul_mem (conjAut_mem_linearAutGroup A) hσ)
      exact ⟨y, Or.inr (by rw [hy])⟩

end BK10.L3

end CFSG.Quasithin.Vol2.Ch11.SecD
