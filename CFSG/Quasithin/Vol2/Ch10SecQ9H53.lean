module

public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv

theorem eq_of_sq_eq_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A B : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)} (hA : A ^ 2 = 1) (hA1 : A ≠ 1)
    (hB : B ^ 2 = 1) (hB1 : B ≠ 1) : A = B := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)
    exact_mod_cast h
  exact Subtype.ext ((CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 A hA hA1).trans
    (CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 B hB hB1).symm)

variable {A : Type*} [Group A] [Finite A] {q : ℕ}

omit [Finite A] in
theorem eq_one_of_fix_inv [Fact q.Prime] (hq2 : q ≠ 2) (hexp : ∀ a : A, a ^ q = 1)
    {σ : MulAut A} {x : A} (h1 : σ x = x) (h2 : σ x = x⁻¹) : x = 1 := by
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [← inv_inv x]
    rw [← h2, h1, mul_inv_cancel]
  have hd : orderOf x ∣ Nat.gcd 2 q :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx2) (orderOf_dvd_of_pow_eq_one (hexp x))
  have hg : Nat.gcd 2 q = 1 :=
    (Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hq2)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem apply_eq_inv_of_comm [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ q = 1)
    (hcard : Nat.card A ≤ q ^ 2) {σ α β : MulAut A} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hασ : α * σ = σ * α) (hβσ : β * σ = σ * β) (hαβ : α * β ≠ β * α) (a : A) :
    σ a = a⁻¹ := by
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [← MulAut.mul_apply, hσ2, MulAut.one_apply]
  by_contra ha
  set u := a * σ a with hu
  have hσu : σ u = u := by rw [hu, map_mul, hσσ, hcomm]
  have hu1 : u ≠ 1 := fun h => ha (eq_inv_of_mul_eq_one_right h)
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, σ a₁ ≠ a₁ := by
    by_contra h
    push Not at h
    exact hσ1 (MulEquiv.ext h)
  set v := a₁ * (σ a₁)⁻¹ with hv
  have hσv : σ v = v⁻¹ := by rw [hv, map_mul, map_inv, hσσ, mul_inv_rev, inv_inv]
  have hv1 : v ≠ 1 := fun h => ha₁ (mul_inv_eq_one.mp h).symm
  have hou : orderOf u = q := orderOf_eq_prime (hexp u) hu1
  have hov : orderOf v = q := orderOf_eq_prime (hexp v) hv1
  have hfix : ∀ i : ℤ, σ (u ^ i) = u ^ i := fun i => by rw [map_zpow, hσu]
  have hinv : ∀ j : ℤ, σ (v ^ j) = (v ^ j)⁻¹ := fun j => by rw [map_zpow, hσv, inv_zpow]
  have hsep : ∀ i j : ℤ, u ^ i * v ^ j = 1 → u ^ i = 1 := by
    intro i j h
    have he : u ^ i = (v ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h
    refine eq_one_of_fix_inv hq2 hexp (σ := σ) (hfix i) ?_
    rw [he, map_inv, hinv, inv_inv]
  let f : Fin q × Fin q → A := fun ij => u ^ (ij.1 : ℤ) * v ^ (ij.2 : ℤ)
  have hfi : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := hcomm }
    have hxy : u ^ ((i : ℤ) - i') = v ^ ((j' : ℤ) - j) := by
      rw [zpow_sub, zpow_sub, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
      simp only [f] at h
      rw [h, mul_comm]
    have hi : u ^ ((i : ℤ) - i') = 1 := by
      refine eq_one_of_fix_inv hq2 hexp (σ := σ) (hfix _) ?_
      rw [hxy, hinv]
    have hj : v ^ ((j' : ℤ) - j) = 1 := hxy ▸ hi
    have hdi := (orderOf_dvd_iff_zpow_eq_one).mpr hi
    have hdj := (orderOf_dvd_iff_zpow_eq_one).mpr hj
    rw [hou] at hdi
    rw [hov] at hdj
    have hmod : ∀ a b : Fin q, ((q : ℤ) ∣ (a : ℤ) - b) → a = b := by
      intro a b hab
      have h1 := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr (Int.emod_eq_zero_of_dvd hab)
      rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast a.2),
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast b.2)] at h1
      exact Fin.ext (by exact_mod_cast h1)
    exact Prod.ext (hmod i i' hdi) (hmod j' j hdj).symm
  have hfs : Function.Surjective f := (hfi.bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_fin, ← pow_two]
    exact hcard)).2
  have hpowu : ∀ γ : MulAut A, γ * σ = σ * γ → ∃ i : ℤ, γ u = u ^ i := by
    intro γ hγ
    obtain ⟨⟨i, j⟩, hij⟩ := hfs (γ u)
    have hσγ : σ (γ u) = γ u := by
      rw [← MulAut.mul_apply, ← hγ, MulAut.mul_apply, hσu]
    refine ⟨i, ?_⟩
    have hj : v ^ (j : ℤ) = 1 := by
      simp only [f] at hij
      refine eq_one_of_fix_inv hq2 hexp (σ := σ) ?_ (hinv j)
      have h1 := hσγ
      rw [← hij, map_mul, hfix, hinv] at h1
      have h2 := mul_left_cancel h1
      rw [inv_eq_iff_eq_inv] at h2
      rw [hinv, ← h2]
    simp only [f] at hij
    rw [← hij, hj, mul_one]
  have hpowv : ∀ γ : MulAut A, γ * σ = σ * γ → ∃ j : ℤ, γ v = v ^ j := by
    intro γ hγ
    obtain ⟨⟨i, j⟩, hij⟩ := hfs (γ v)
    have hσγ : σ (γ v) = (γ v)⁻¹ := by
      rw [← MulAut.mul_apply, ← hγ, MulAut.mul_apply, hσv, map_inv]
    refine ⟨j, ?_⟩
    have hi : u ^ (i : ℤ) = 1 := by
      simp only [f] at hij
      refine eq_one_of_fix_inv hq2 hexp (σ := σ) (hfix i) ?_
      have h1 := hσγ
      rw [← hij, map_mul, hfix, hinv, mul_inv_rev, hcomm (v ^ (j : ℤ))⁻¹] at h1
      have h2 := mul_right_cancel h1
      rw [hfix]
      exact h2
    simp only [f] at hij
    rw [← hij, hi, one_mul]
  obtain ⟨i₁, hi₁⟩ := hpowu α hασ
  obtain ⟨i₂, hi₂⟩ := hpowu β hβσ
  obtain ⟨j₁, hj₁⟩ := hpowv α hασ
  obtain ⟨j₂, hj₂⟩ := hpowv β hβσ
  apply hαβ
  ext x
  obtain ⟨⟨i, j⟩, rfl⟩ := hfs x
  simp only [f, MulAut.mul_apply, map_mul, map_zpow, hi₁, hi₂, hj₁, hj₂, ← zpow_mul, mul_comm]
