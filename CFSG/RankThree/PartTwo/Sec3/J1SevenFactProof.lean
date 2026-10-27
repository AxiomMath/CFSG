module

public import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule
public import CFSG.Sporadic.J1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

public section

namespace CFSG.RankThree.PartTwo.Sec3.J1SevenFactProof

open CFSG.Sporadic.J1 CFSG.Blueprint

noncomputable def wJ : J :=
  a * b * a * b * a * b ^ 2 * a * b * a * b ^ 2 * a * b ^ 2 * a * b * a * b ^ 2 * a * b * a * b * a *
    b ^ 2 * a * b ^ 2 * a * b

theorem wJ_pow_seven : wJ ^ 7 = 1 := by
  apply mat_injective
  simp only [wJ, mat_pow, mat_mul, mat_one, mat_a, mat_b]
  decide +kernel

theorem b_mul_wJ : b * wJ = wJ ^ 4 * b := by
  apply mat_injective
  simp only [wJ, mat_pow, mat_mul, mat_one, mat_a, mat_b]
  decide +kernel

theorem wJ_ne_one : wJ ≠ 1 := by
  intro h
  have := congrArg mat h
  simp only [wJ, mat_pow, mat_mul, mat_one, mat_a, mat_b] at this
  revert this
  decide +kernel


theorem sylow_three_eq {Γ : Type*} [Group Γ] [Finite Γ] (hcard : Nat.card Γ = 175560)
    {x : Γ} (hx : orderOf x = 3) :
    ∃ Q : Sylow 3 Γ, (Q : Subgroup Γ) = Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hxP.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  obtain ⟨n, hn⟩ := (Q.isPGroup').exists_card_eq
  have hdvd : Nat.card (Q : Subgroup Γ) ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_zpowers, hx, hn]
  rw [hn, hcard] at hdvd
  by_contra hlt
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n ≤ 1 := by omega
    have : 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h9 : 3 ^ 2 ∣ 3 ^ n := Nat.pow_dvd_pow 3 hn2
  have := dvd_trans h9 hdvd
  norm_num at this

theorem frobenius_of_sylow {Γ : Type*} [Group Γ] [Finite Γ] (hcard : Nat.card Γ = 175560)
    {x₀ y₀ : Γ} (hx₀ : orderOf x₀ = 3) (hy₀ : orderOf y₀ = 7) (hxy : x₀ * y₀ = y₀ ^ 4 * x₀)
    {x : Γ} (hx : orderOf x = 3) :
    ∃ F : Subgroup Γ, Nat.card F = 7 ∧ x ∈ Subgroup.normalizer (F : Set Γ) ∧
      ∀ g ∈ F, x * g * x⁻¹ = g → g = 1 := by
  obtain ⟨Q, hQ⟩ := sylow_three_eq hcard hx
  obtain ⟨Q₀, hQ₀⟩ := sylow_three_eq hcard hx₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q₀ Q
  have hxmem : x ∈ (Subgroup.zpowers x₀).map (MulAut.conj g).toMonoidHom := by
    have h1 : x ∈ (Q : Subgroup Γ) := hQ ▸ Subgroup.mem_zpowers x
    rw [← hg] at h1
    change x ∈ (Q₀ : Subgroup Γ).map (MulAut.conj g).toMonoidHom at h1
    rwa [hQ₀] at h1
  obtain ⟨z, hz, hzx⟩ := hxmem
  obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hc : ∀ j : ℤ, x₀ * y₀ ^ j * x₀⁻¹ = y₀ ^ (4 * j) := by
    intro j
    have h4 : x₀ * y₀ * x₀⁻¹ = y₀ ^ 4 := by rw [hxy]; group
    calc x₀ * y₀ ^ j * x₀⁻¹ = (x₀ * y₀ * x₀⁻¹) ^ j := (conj_zpow).symm
      _ = (y₀ ^ 4) ^ j := by rw [h4]
      _ = y₀ ^ (4 * j) := by rw [← zpow_natCast, ← zpow_mul]; norm_num
  have hc2 : ∀ j : ℤ, x₀ ^ 2 * y₀ ^ j * (x₀ ^ 2)⁻¹ = y₀ ^ (16 * j) := by
    intro j
    have : x₀ ^ 2 * y₀ ^ j * (x₀ ^ 2)⁻¹ = x₀ * (x₀ * y₀ ^ j * x₀⁻¹) * x₀⁻¹ := by
      simp only [pow_two, mul_inv_rev, mul_assoc]
    rw [this, hc, hc]; ring_nf
  have hx₀3 : x₀ ^ 3 = 1 := by rw [← hx₀]; exact pow_orderOf_eq_one x₀
  have hcases : x₀ ^ e = 1 ∨ x₀ ^ e = x₀ ∨ x₀ ^ e = x₀ ^ 2 := by
    have h := zpow_mod_orderOf x₀ e
    rw [hx₀] at h
    have hm : e % ((3 : ℕ) : ℤ) = 0 ∨ e % ((3 : ℕ) : ℤ) = 1 ∨ e % ((3 : ℕ) : ℤ) = 2 := by omega
    rcases hm with hm | hm | hm
    · left; rw [← h, hm]; simp
    · right; left; rw [← h, hm]; simp
    · right; right; rw [← h, hm]; simp
  have hx1 : x ≠ 1 := by
    intro h; rw [h] at hx; simp at hx
  have hconj : ∀ y : Γ, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := fun y => rfl
  have hxe : x = g * x₀ ^ e * g⁻¹ := by rw [← hzx, hconj]
  have hne : x₀ ^ e ≠ 1 := by
    intro h; apply hx1; rw [hxe, h]; simp
  have h7 : ∀ j : ℤ, y₀ ^ j = 1 → (7 : ℤ) ∣ j := by
    intro j hj
    have := orderOf_dvd_iff_zpow_eq_one.mpr hj
    rw [hy₀] at this
    exact_mod_cast this
  have hact : ∀ j : ℤ, ∃ m : ℤ, x₀ ^ e * y₀ ^ j * (x₀ ^ e)⁻¹ = y₀ ^ m ∧
      ((7 : ℤ) ∣ m - j → (7 : ℤ) ∣ j) := by
    intro j
    rcases hcases with h | h | h
    · exact absurd h hne
    · refine ⟨4 * j, by rw [h, hc], fun hd => by omega⟩
    · refine ⟨16 * j, by rw [h, hc2], fun hd => by omega⟩
  set F : Subgroup Γ := (Subgroup.zpowers y₀).map (MulAut.conj g).toMonoidHom with hF
  have hFcard : Nat.card F = 7 := by
    rw [hF, Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers, hy₀]
  have hmemF : ∀ j : ℤ, g * y₀ ^ j * g⁻¹ ∈ F := fun j =>
    ⟨y₀ ^ j, Subgroup.zpow_mem_zpowers _ _, hconj _⟩
  have hconjx : ∀ j m : ℤ, x₀ ^ e * y₀ ^ j * (x₀ ^ e)⁻¹ = y₀ ^ m →
      x * (g * y₀ ^ j * g⁻¹) * x⁻¹ = g * y₀ ^ m * g⁻¹ := by
    intro j m hm
    rw [← hm, hxe]; simp only [mul_inv_rev, inv_inv, mul_assoc]
    simp
  have hxF : ∀ h ∈ F, x * h * x⁻¹ ∈ F := by
    intro h hh
    obtain ⟨y, hy, hyh⟩ := hh
    rw [← hyh, hconj]
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨m, hm, -⟩ := hact j
    rw [hconjx j m hm]
    exact hmemF m
  refine ⟨F, hFcard, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hxF h hh, fun hh => ?_⟩
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have h3 := hxF _ (hxF _ hh)
    have : x * (x * (x * h * x⁻¹) * x⁻¹) * x⁻¹ = h := by
      calc x * (x * (x * h * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * h * (x ^ 3)⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
        _ = h := by rw [hx3]; simp
    rwa [this] at h3
  · intro f hf hfix
    obtain ⟨y, hy, hyf⟩ := hf
    rw [← hyf, hconj] at hfix ⊢
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨m, hm, hd⟩ := hact j
    rw [hconjx j m hm] at hfix
    have h2 : y₀ ^ m = y₀ ^ j := by
      have := congrArg (fun t => g⁻¹ * t * g) hfix
      simpa [mul_assoc] using this
    have h3 : y₀ ^ (m - j) = 1 := by rw [zpow_sub, h2, mul_inv_cancel]
    have h4 := hd (h7 _ h3)
    have h5 : y₀ ^ j = 1 := by
      obtain ⟨t, ht⟩ := h4
      rw [ht, zpow_mul]
      have : y₀ ^ (7 : ℤ) = 1 := by
        have := pow_orderOf_eq_one y₀
        rw [hy₀] at this
        exact_mod_cast this
      rw [this, one_zpow]
    rw [h5]; simp

theorem orderOf_wJ : orderOf wJ = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime wJ_pow_seven wJ_ne_one

theorem j1SevenFact :
    CFSG.RankThree.PartTwo.Sec3.J1SevenFact := by
  intro x hx
  have hfin : Finite NativeSporadic.J1 := fam_j1_simplicity.1
  have hcard : Nat.card NativeSporadic.J1 = 175560 := card_J1
  refine frobenius_of_sylow hcard (x₀ := nativeEquiv.symm b) (y₀ := nativeEquiv.symm wJ) ?_ ?_ ?_ hx
  · rw [MulEquiv.orderOf_eq]; exact orderOf_b
  · rw [MulEquiv.orderOf_eq]; exact orderOf_wJ
  · rw [← map_pow, ← map_mul, ← map_mul, b_mul_wJ]

end CFSG.RankThree.PartTwo.Sec3.J1SevenFactProof