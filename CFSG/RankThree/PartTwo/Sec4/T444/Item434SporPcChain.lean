module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporE81

@[expose] def tailGroup {W : Type*} [Group W] (p : ℕ → W) (n i : ℕ) : Subgroup W :=
  Subgroup.closure (p '' {l | i ≤ l ∧ l < n})

theorem tailGroup_of_le {W : Type*} [Group W] (p : ℕ → W) {n i : ℕ} (h : n ≤ i) :
    tailGroup p n i = ⊥ := by
  have : {l | i ≤ l ∧ l < n} = (∅ : Set ℕ) := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
    omega
  rw [tailGroup, this, Set.image_empty, Subgroup.closure_empty]

theorem tailGroup_eq_sup {W : Type*} [Group W] (p : ℕ → W) {n i : ℕ} (h : i < n) :
    tailGroup p n i = Subgroup.zpowers (p i) ⊔ tailGroup p n (i + 1) := by
  have hset : p '' {l | i ≤ l ∧ l < n} = {p i} ∪ p '' {l | i + 1 ≤ l ∧ l < n} := by
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨l, ⟨hl1, hl2⟩, rfl⟩
      rcases Nat.eq_or_lt_of_le hl1 with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨l, ⟨hlt, hl2⟩, rfl⟩
    · rintro (rfl | ⟨l, ⟨hl1, hl2⟩, rfl⟩)
      · exact ⟨i, ⟨le_rfl, h⟩, rfl⟩
      · exact ⟨l, ⟨by omega, hl2⟩, rfl⟩
  rw [tailGroup, hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
  rfl

theorem isPGroup_tailGroup {W : Type*} [Group W] [Finite W] (p : ℕ → W) (n : ℕ)
    (hcube : ∀ i < n, p i ^ 3 ∈ tailGroup p n (i + 1))
    (hconj : ∀ i < n, ∀ j, i < j → j < n → p i * p j * (p i)⁻¹ ∈ tailGroup p n (i + 1)) :
    ∀ i, IsPGroup 3 (tailGroup p n i) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  suffices h : ∀ d i, n - i = d → IsPGroup 3 (tailGroup p n i) from fun i => h _ i rfl
  intro d
  induction d with
  | zero =>
    intro i hi
    rw [tailGroup_of_le p (by omega : n ≤ i)]
    exact IsPGroup.of_bot
  | succ d ih =>
    intro i hi
    have hin : i < n := by omega
    have hN : IsPGroup 3 (tailGroup p n (i + 1)) := ih (i + 1) (by omega)
    rw [tailGroup_eq_sup p hin]
    have hZ : IsPGroup 3 (Subgroup.zpowers (p i)) := by
      obtain ⟨k, hk⟩ := hN ⟨p i ^ 3, hcube i hin⟩
      have hk' : (p i ^ 3) ^ (3 ^ k) = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have e1 : (p i) ^ (3 ^ (k + 1)) = 1 := by rw [pow_succ', pow_mul]; exact hk'
      intro g
      obtain ⟨x, hx⟩ := g
      obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      refine ⟨k + 1, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm t, zpow_mul, zpow_natCast, e1, one_zpow]
    have hconjN : ∀ y ∈ tailGroup p n (i + 1), p i * y * (p i)⁻¹ ∈ tailGroup p n (i + 1) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨l, ⟨hl1, hl2⟩, rfl⟩ := hx
        exact hconj i hin l (by omega) hl2
      | one => simp
      | mul x y _ _ ihx ihy =>
        have : p i * (x * y) * (p i)⁻¹ = (p i * x * (p i)⁻¹) * (p i * y * (p i)⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ ihx ihy
      | inv x _ ihx =>
        have : p i * x⁻¹ * (p i)⁻¹ = (p i * x * (p i)⁻¹)⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ ihx
    have hmem : p i ∈ Subgroup.normalizer (tailGroup p n (i + 1) : Set W) :=
      Subgroup.mem_normalizer_fintype hconjN
    exact hZ.to_sup_of_normal_right' hN ((Subgroup.zpowers_le).2 hmem)

theorem card_le_of_isPGroup {W : Type*} [Group W] {J Q : Subgroup W} [Finite J] (hQJ : Q ≤ J)
    (hQ : IsPGroup 3 Q) : Nat.card Q ≤ 3 ^ (Nat.card J).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Q := Finite.of_injective (Subgroup.inclusion hQJ) (Subgroup.inclusion_injective hQJ)
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card J := Subgroup.card_dvd_of_le hQJ
  rw [hk] at hdvd ⊢
  have hJ : Nat.card J ≠ 0 := Nat.card_pos.ne'
  exact Nat.pow_le_pow_right (by norm_num)
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hJ).1 hdvd)

end CFSG.RankThree.PartTwo.Sec4.Item434SporE81
