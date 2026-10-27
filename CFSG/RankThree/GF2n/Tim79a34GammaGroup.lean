module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.GF2n.Tim79a.Gamma

open scoped commutatorElement

theorem exists_conj_eq_of_comm_mem {G : Type*} [Group G] {P A E : Subgroup G} {b q : G}
    (hb : b * b = 1) (hsq : ∀ p ∈ P, p * p ∈ A)
    (hA : ∀ p ∈ P, ⁅p, b⁆ ∈ A → p * p = 1) (hE : ∀ p ∈ P, ⁅p, b⁆ = 1 → p ∈ E)
    (hcov : ∀ e ∈ E, ∃ r ∈ P, ⁅r, b⁆ = e) (hq : ⁅q, b⁆ ∈ P) :
    ∃ r ∈ P, q * b * q⁻¹ = r * b * r⁻¹ := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hcommsq : ∀ p : G, p * b * (p * b) = 1 → ⁅p, b⁆ = p * p := by
    intro p hp
    have hinv : (p * b)⁻¹ = p * b := inv_eq_of_mul_eq_one_right hp
    rw [mul_inv_rev, hbinv] at hinv
    rw [commutatorElement_def]
    calc p * b * p⁻¹ * b⁻¹ = p * (b * p⁻¹) * b⁻¹ := by group
      _ = p * (p * b) * b⁻¹ := by rw [hinv]
      _ = p * p := by group
  have hconj : q * b * q⁻¹ = ⁅q, b⁆ * b := by
    rw [commutatorElement_def]
    group
  have hinvol : ⁅q, b⁆ * b * (⁅q, b⁆ * b) = 1 := by
    rw [← hconj]
    calc q * b * q⁻¹ * (q * b * q⁻¹) = q * (b * b) * q⁻¹ := by group
      _ = 1 := by simp [hb]
  have hsqc : ⁅⁅q, b⁆, b⁆ = ⁅q, b⁆ * ⁅q, b⁆ := hcommsq _ hinvol
  have hpA : ⁅⁅q, b⁆, b⁆ ∈ A := by
    rw [hsqc]
    exact hsq _ hq
  have hsq1 : ⁅q, b⁆ * ⁅q, b⁆ = 1 := hA _ hq hpA
  have hpE : ⁅q, b⁆ ∈ E := hE _ hq (by rw [hsqc]; exact hsq1)
  obtain ⟨r, hr, hrb⟩ := hcov _ hpE
  refine ⟨r, hr, ?_⟩
  have hrconj : r * b * r⁻¹ = ⁅r, b⁆ * b := by
    rw [commutatorElement_def]
    group
  rw [hconj, hrconj, hrb]

theorem exists_pow_eq_one_of_stabilizes {G : Type*} [Group G] {p e : ℕ} {P A C : Subgroup G}
    {k : G} (hAe : ∀ a ∈ A, a ^ p ^ e = 1) (hkA : ∀ a ∈ A, k * a * k⁻¹ = a)
    (hkP : ∀ x ∈ P, k * x * k⁻¹ * x⁻¹ ∈ A)
    (hC : Subgroup.centralizer (P : Set G) ≤ C) (hCp : IsPGroup p C) :
    ∃ n : ℕ, k ^ p ^ n = 1 := by
  have hpow : ∀ x ∈ P, k ^ p ^ e * x * (k ^ p ^ e)⁻¹ = x := by
    intro x hx
    obtain ⟨d, hd⟩ : ∃ d, d = k * x * k⁻¹ * x⁻¹ := ⟨_, rfl⟩
    have hdA : d ∈ A := by
      rw [hd]
      exact hkP x hx
    have hkx : k * x * k⁻¹ = d * x := by
      rw [hd]
      group
    have hconj_pow : ∀ m : ℕ, k ^ m * x * (k ^ m)⁻¹ = d ^ m * x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hkdm : k * d ^ m * k⁻¹ = d ^ m := hkA _ (pow_mem hdA m)
        calc k ^ (m + 1) * x * (k ^ (m + 1))⁻¹
            = k * (k ^ m * x * (k ^ m)⁻¹) * k⁻¹ := by group
          _ = k * (d ^ m * x) * k⁻¹ := by rw [ih]
          _ = (k * d ^ m * k⁻¹) * (k * x * k⁻¹) := by group
          _ = d ^ m * (d * x) := by rw [hkdm, hkx]
          _ = d ^ (m + 1) * x := by rw [pow_succ, mul_assoc]
    have h1 := hconj_pow (p ^ e)
    rw [hAe d hdA, one_mul] at h1
    exact h1
  have hcent : k ^ p ^ e ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (mul_inv_eq_iff_eq_mul.mp (hpow h hh)).symm
  obtain ⟨f, hf⟩ := hCp ⟨k ^ p ^ e, hC hcent⟩
  have hf' : (k ^ p ^ e) ^ p ^ f = 1 := by
    have h2 := congrArg Subtype.val hf
    simpa using h2
  refine ⟨e + f, ?_⟩
  rw [pow_add, pow_mul]
  exact hf'

end CFSG.RankThree.GF2n.Tim79a.Gamma
