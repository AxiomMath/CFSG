module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreBasic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem zpow_emod_three {g : G} (hg : g ^ 3 = 1) (k : ℤ) : g ^ k = g ^ (k % 3) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
  have : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
  rw [this, one_zpow, mul_one]

theorem mem_of_zpow_mem {g : G} (hg : g ^ 3 = 1) {H : Subgroup G} {k : ℤ} (hk : ¬ (3 : ℤ) ∣ k)
    (hH : g ^ k ∈ H) : g ∈ H := by
  rw [zpow_emod_three hg k] at hH
  have h3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h3 | h3
  · rw [h3, zpow_one] at hH; exact hH
  · rw [h3] at hH
    have h4 : g = (g ^ (2 : ℤ)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul]
      have h5 : g ^ ((4 : ℕ) : ℤ) = g * g ^ 3 := by
        rw [zpow_natCast, ← pow_succ']
      rw [hg, mul_one] at h5
      rw [show (2 : ℤ) * ((2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num, h5]
    rw [h4]; exact Subgroup.pow_mem _ hH 2

theorem indep (h : FF84Sec4 b L B K b₁ b₂) (i j k : ℤ)
    (hijk : b ^ i * b₁ ^ j * b₂ ^ k = 1) : (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k := by
  have hb3 : b ^ 3 = 1 := pow3_of_mem h (mem_b h)
  have hb₁3 : b₁ ^ 3 = 1 := pow3_of_mem h (mem_b₁ h)
  have hb₂3 : b₂ ^ 3 = 1 := pow3_of_mem h (mem_b₂ h)
  have hzp : ∀ {g : G}, g ^ 3 = 1 → ∀ {k : ℤ}, (3 : ℤ) ∣ k → g ^ k = 1 := by
    intro g hg k hk
    obtain ⟨t, rfl⟩ := hk
    rw [zpow_mul]
    have : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
    rw [this, one_zpow]
  have hk : (3 : ℤ) ∣ k := by
    by_contra hk
    apply b₂_notin_E h
    refine mem_of_zpow_mem hb₂3 hk ?_
    have : b₂ ^ k = (b ^ i * b₁ ^ j)⁻¹ := eq_inv_of_mul_eq_one_right hijk
    rw [this]
    exact inv_mem (mul_mem (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _))
  rw [hzp hb₂3 hk, mul_one] at hijk
  have hj : (3 : ℤ) ∣ j := by
    by_contra hj
    apply b₁_notin_zpowers_b h
    refine mem_of_zpow_mem hb₁3 hj ?_
    have : b₁ ^ j = (b ^ i)⁻¹ := eq_inv_of_mul_eq_one_right hijk
    rw [this]
    exact inv_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _)
  rw [hzp hb₁3 hj, mul_one] at hijk
  refine ⟨?_, hj, hk⟩
  have : ((orderOf b : ℕ) : ℤ) ∣ i := orderOf_dvd_iff_zpow_eq_one.2 hijk
  rwa [h.hyp.ord] at this

theorem mul_coord (h : FF84Sec4 b L B K b₁ b₂) (a c d a' c' d' : ℤ) :
    (b ^ a * b₁ ^ c * b₂ ^ d) * (b ^ a' * b₁ ^ c' * b₂ ^ d') =
      b ^ (a + a') * b₁ ^ (c + c') * b₂ ^ (d + d') := by
  haveI : IsMulCommutative ↥B := h.mono.1.1.toIsMulCommutative
  let β : ↥B := ⟨b, mem_b h⟩
  let β₁ : ↥B := ⟨b₁, mem_b₁ h⟩
  let β₂ : ↥B := ⟨b₂, mem_b₂ h⟩
  have key : (β ^ a * β₁ ^ c * β₂ ^ d) * (β ^ a' * β₁ ^ c' * β₂ ^ d') =
      β ^ (a + a') * β₁ ^ (c + c') * β₂ ^ (d + d') := by
    simp only [zpow_add]
    ac_rfl
  exact congrArg Subtype.val key

theorem six_coord {x : G} (hx : x ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G)) :
    ∃ a c d : ℤ, x = b ^ a * b₁ ^ c * b₂ ^ d ∧
      ((a = 1 ∧ c = 0 ∧ d = 0) ∨ (a = -1 ∧ c = 0 ∧ d = 0) ∨ (a = 0 ∧ c = 1 ∧ d = 0) ∨
        (a = 0 ∧ c = -1 ∧ d = 0) ∨ (a = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ c = 0 ∧ d = -1)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, 0, by simp, by simp⟩
  · exact ⟨-1, 0, 0, by simp, by simp⟩
  · exact ⟨0, 1, 0, by simp, by simp⟩
  · exact ⟨0, -1, 0, by simp, by simp⟩
  · exact ⟨0, 0, 1, by simp, by simp⟩
  · exact ⟨0, 0, -1, by simp, by simp⟩

theorem xy_cases (h : FF84Sec4 b L B K b₁ b₂) {x y : G}
    (hx : x ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G))
    (hy : y ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G)) (hxy : x * y = b * b₁) :
    (x = b ∧ y = b₁) ∨ (x = b₁ ∧ y = b) := by
  obtain ⟨a, c, d, rfl, ha⟩ := six_coord hx
  obtain ⟨a', c', d', rfl, ha'⟩ := six_coord hy
  rw [mul_coord h] at hxy
  have hc := (comm_of_mem h (mem_b h) (mem_b₁ h)).eq
  have h1 : b ^ (a + a' + -1) * b₁ ^ (c + c' + -1) * b₂ ^ (d + d' + 0) = 1 := by
    calc b ^ (a + a' + -1) * b₁ ^ (c + c' + -1) * b₂ ^ (d + d' + 0)
        = (b ^ (a + a') * b₁ ^ (c + c') * b₂ ^ (d + d')) *
            (b ^ (-1 : ℤ) * b₁ ^ (-1 : ℤ) * b₂ ^ (0 : ℤ)) :=
          (mul_coord h (a + a') (c + c') (d + d') (-1) (-1) 0).symm
      _ = (b * b₁) * (b⁻¹ * b₁⁻¹) := by rw [hxy]; simp
      _ = (b₁ * b) * (b⁻¹ * b₁⁻¹) := by rw [hc]
      _ = 1 := by group
  obtain ⟨h2, h3, h4⟩ := indep h _ _ _ h1
  have hcase : (a = 1 ∧ c = 0 ∧ d = 0 ∧ a' = 0 ∧ c' = 1 ∧ d' = 0) ∨
      (a = 0 ∧ c = 1 ∧ d = 0 ∧ a' = 1 ∧ c' = 0 ∧ d' = 0) := by omega
  rcases hcase with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · left; simp
  · right; simp

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
