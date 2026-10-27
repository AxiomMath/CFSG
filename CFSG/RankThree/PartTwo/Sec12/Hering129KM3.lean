module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KM2

public section

namespace CFSG.RankThree.PartTwo.Sec12

theorem hess_abstract {G : Type} [Group G] {Lh F : Subgroup G} {x₁ x₂ n₁ w : G}
    (hF : F = Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂)
    (hx₁L : x₁ ∈ Lh) (hx₂L : x₂ ∈ Lh)
    (h12 : x₁ * x₂ = x₂ * x₁) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1) (hcard : Nat.card F = 9)
    (hn₁ : n₁ ∈ Lh) (hF1 : n₁ * x₁ * n₁⁻¹ = x₂⁻¹) (hF2 : n₁ * x₂ * n₁⁻¹ = x₁)
    (hw1 : w * x₁ * w⁻¹ = x₁)
    (hw2 : w * x₂ * w⁻¹ = x₂ * x₁ ∨ w * x₂ * w⁻¹ = x₂ * x₁⁻¹)
    (hdet : ∀ m ∈ (Lh ⊔ Subgroup.zpowers w) ⊓ Subgroup.normalizer (F : Set G),
      ∃ a b c d : ℤ, (a * d - b * c) % 3 = 1 ∧ m * x₁ * m⁻¹ = x₁ ^ a * x₂ ^ c ∧
        m * x₂ * m⁻¹ = x₁ ^ b * x₂ ^ d) :
    F ≤ Lh ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ x₁ ∈ F ∧
      (∀ g ∈ F, w * g * w⁻¹ ∈ F) ∧
      F ⊓ (Subgroup.zpowers w ⊔ Subgroup.zpowers x₁) = Subgroup.zpowers x₁ ∧
      (∀ g ∈ F, w * g * w⁻¹ * g⁻¹ ∈ Subgroup.zpowers x₁) ∧
      (∃ g ∈ F, w * g * w⁻¹ * g⁻¹ ≠ 1) ∧
      Nonempty (Sec4.autIn (Lh ⊔ Subgroup.zpowers w) F ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨e, he, hwe⟩ : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ w * x₂ * w⁻¹ = x₂ * x₁ ^ e := by
    rcases hw2 with h | h
    · exact ⟨1, Or.inl rfl, by rw [zpow_one]; exact h⟩
    · exact ⟨-1, Or.inr rfl, by rw [zpow_neg_one]; exact h⟩
  have hx₁F : x₁ ∈ F := hF ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
  have hx₂F : x₂ ∈ F := hF ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)
  have hmem : ∀ g : G, g ∈ F ↔ ∃ i j : ℤ, g = x₁ ^ i * x₂ ^ j := by
    intro g
    refine ⟨fun hg => ?_, ?_⟩
    · rw [hF] at hg
      exact Sec4.exists_zpow_mul_of_mem_sup h12 hg
    · rintro ⟨i, j, rfl⟩
      exact F.mul_mem (F.zpow_mem hx₁F i) (F.zpow_mem hx₂F j)
  have hc : ∀ i j : ℤ, x₂ ^ j * x₁ ^ i = x₁ ^ i * x₂ ^ j := fun i j =>
    (Commute.zpow_zpow h12 i j).eq.symm
  have hwx₁ : w * x₁ = x₁ * w := mul_inv_eq_iff_eq_mul.1 hw1
  have hx₁ne : x₁ ≠ 1 := by
    intro h
    have hF' : F = Subgroup.zpowers x₂ := by
      rw [hF, h, Subgroup.zpowers_one_eq_bot, bot_sup_eq]
    have hle : Nat.card F ≤ 3 := by
      rw [hF', Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x₁ = 3 := orderOf_eq_prime h1 hx₁ne
  have hconj : ∀ i j : ℤ, w * (x₁ ^ i * x₂ ^ j) * w⁻¹ = x₁ ^ (i + e * j) * x₂ ^ j := by
    intro i j
    have e1 : w * x₁ ^ i * w⁻¹ = x₁ ^ i := by rw [← conj_zpow, hw1]
    have e2 : w * x₂ ^ j * w⁻¹ = x₂ ^ j * x₁ ^ (e * j) := by
      rw [← conj_zpow, hwe, ((Commute.symm h12).zpow_right e).mul_zpow j, ← zpow_mul]
    calc w * (x₁ ^ i * x₂ ^ j) * w⁻¹ = (w * x₁ ^ i * w⁻¹) * (w * x₂ ^ j * w⁻¹) := by group
      _ = x₁ ^ i * (x₂ ^ j * x₁ ^ (e * j)) := by rw [e1, e2]
      _ = x₁ ^ i * (x₁ ^ (e * j) * x₂ ^ j) := by rw [hc]
      _ = x₁ ^ (i + e * j) * x₂ ^ j := by rw [← mul_assoc, ← zpow_add]
  have hcomm : ∀ i j : ℤ,
      w * (x₁ ^ i * x₂ ^ j) * w⁻¹ * (x₁ ^ i * x₂ ^ j)⁻¹ = x₁ ^ (e * j) := by
    intro i j
    rw [hconj]
    group
  have hx₁e : x₁ ^ e ≠ 1 := by
    rcases he with rfl | rfl
    · simpa using hx₁ne
    · simpa using hx₁ne
  refine ⟨?_, ?_, hcard, hx₁F, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hF]
    exact sup_le (Subgroup.zpowers_le.2 hx₁L) (Subgroup.zpowers_le.2 hx₂L)
  ·
    refine ⟨?_, ?_⟩
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hcard]; norm_num)
    · intro x hx
      obtain ⟨i, j, rfl⟩ := (hmem x).1 hx
      rw [(Commute.zpow_zpow h12 i j).mul_pow]
      have e3 : ∀ (a : G) (k : ℤ), a ^ 3 = 1 → (a ^ k) ^ 3 = 1 := by
        intro a k ha
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
      rw [e3 x₁ i h1, e3 x₂ j h2, mul_one]
  ·
    intro g hg
    obtain ⟨i, j, rfl⟩ := (hmem g).1 hg
    rw [hconj]
    exact (hmem _).2 ⟨_, _, rfl⟩
  ·
    apply le_antisymm
    · rintro g ⟨hgF, hgW⟩
      obtain ⟨i, j, rfl⟩ := (hmem g).1 hgF
      have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers x₁ ≤ Subgroup.centralizer {w} := by
        refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff.1 hh]
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff.1 hh]
          exact hwx₁
      have hwg : w * (x₁ ^ i * x₂ ^ j) = (x₁ ^ i * x₂ ^ j) * w :=
        Subgroup.mem_centralizer_iff.1 (hle hgW) w rfl
      have h3 : x₁ ^ (e * j) = 1 := by
        rw [← hcomm i j, hwg, mul_inv_cancel_right, mul_inv_cancel]
      have h3' : x₁ ^ j = 1 := by
        rcases he with rfl | rfl
        · simpa using h3
        · simpa using h3
      have h3'' : (3 : ℤ) ∣ j := by
        have := orderOf_dvd_iff_zpow_eq_one.2 h3'
        rw [hord] at this
        exact_mod_cast this
      have hx2 : x₂ ^ j = 1 := by
        rw [Sec4.zpow_emod_three h2 j, Int.emod_eq_zero_of_dvd h3'', zpow_zero]
      rw [hx2, mul_one]
      exact Subgroup.zpow_mem_zpowers x₁ i
    · exact le_inf (Subgroup.zpowers_le.2 hx₁F) le_sup_right
  ·
    intro g hg
    obtain ⟨i, j, rfl⟩ := (hmem g).1 hg
    rw [hcomm]
    exact Subgroup.zpow_mem_zpowers x₁ _
  ·
    refine ⟨x₂, hx₂F, ?_⟩
    have := hcomm 0 1
    simp only [zpow_zero, one_mul, zpow_one, mul_one] at this
    rw [this]
    exact hx₁e
  ·
    subst hF
    rcases hw2 with h | h
    · exact nonempty_autIn_sl23 (Lh ⊔ Subgroup.zpowers w) h12 h1 h2 hcard
        (Subgroup.mem_sup_left hn₁) hF1 hF2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
        hw1 h hdet
    · have e1 : w⁻¹ * x₁ * w⁻¹⁻¹ = x₁ := by
        calc w⁻¹ * x₁ * w⁻¹⁻¹ = w⁻¹ * (x₁ * w) := by group
          _ = w⁻¹ * (w * x₁) := by rw [hwx₁]
          _ = x₁ := by group
      have e2 : w⁻¹ * x₂ * w⁻¹⁻¹ = x₂ * x₁ := by
        calc w⁻¹ * x₂ * w⁻¹⁻¹ = w⁻¹ * (x₂ * x₁⁻¹ * x₁) * w := by group
          _ = w⁻¹ * (w * x₂ * w⁻¹ * x₁) * w := by rw [h]
          _ = x₂ * (w⁻¹ * x₁ * w⁻¹⁻¹) := by group
          _ = x₂ * x₁ := by rw [e1]
      exact nonempty_autIn_sl23 (Lh ⊔ Subgroup.zpowers w) h12 h1 h2 hcard
        (Subgroup.mem_sup_left hn₁) hF1 hF2
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))) e1 e2 hdet

end CFSG.RankThree.PartTwo.Sec12
