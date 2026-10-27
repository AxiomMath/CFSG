module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsGen

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem even_card_of_isPGroup_two {Z : Subgroup G} (hZ : IsPGroup 2 Z) (hne : Z ≠ ⊥) :
    Even (Nat.card Z) := by
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rcases k with _ | k
  · exact absurd (Subgroup.eq_bot_of_card_eq Z (by simpa using hk)) hne
  · rw [hk, pow_succ]
    exact even_two.mul_left _

theorem odd_ncard_nonone {Z : Subgroup G} (hZ : IsPGroup 2 Z) (hne : Z ≠ ⊥) :
    Odd {x : G | x ∈ Z ∧ x ≠ 1}.ncard := by
  have h1 : {x : G | x ∈ Z ∧ x ≠ 1} = (Z : Set G) \ {1} := by
    ext x
    simp
  have h2 := Set.ncard_sdiff_singleton_of_mem (s := (Z : Set G)) Z.one_mem
  have h3 : (Z : Set G).ncard = Nat.card Z := (Nat.card_coe_set_eq (Z : Set G)).symm
  obtain ⟨r, hr⟩ := even_card_of_isPGroup_two hZ hne
  have hpos : 0 < Nat.card Z := Nat.card_pos
  rw [h1, h2, h3]
  exact ⟨r - 1, by omega⟩

theorem odd_ncard_third {Z₁ Z₂ ZS : Subgroup G} (h1 : Z₁ ≤ ZS) (h2 : Z₂ ≤ ZS)
    (h12 : Z₁ ⊓ Z₂ = ⊥) (e1 : Even (Nat.card Z₁)) (e2 : Even (Nat.card Z₂))
    (eS : Even (Nat.card ZS)) : Odd {x : G | x ∈ ZS ∧ x ∉ Z₁ ∧ x ∉ Z₂}.ncard := by
  have hu := Set.ncard_union_add_ncard_inter (Z₁ : Set G) (Z₂ : Set G) (Set.toFinite _)
    (Set.toFinite _)
  have hint : (Z₁ : Set G) ∩ (Z₂ : Set G) = {1} := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have : x ∈ Z₁ ⊓ Z₂ := ⟨hx1, hx2⟩
      rw [h12, Subgroup.mem_bot] at this
      exact this
    · rintro rfl
      exact ⟨Z₁.one_mem, Z₂.one_mem⟩
  rw [hint, Set.ncard_singleton] at hu
  have hsub : (Z₁ : Set G) ∪ (Z₂ : Set G) ⊆ (ZS : Set G) := Set.union_subset h1 h2
  have hd := Set.ncard_sdiff_add_ncard_of_subset hsub (Set.toFinite _)
  have hset : {x : G | x ∈ ZS ∧ x ∉ Z₁ ∧ x ∉ Z₂} =
      (ZS : Set G) \ ((Z₁ : Set G) ∪ (Z₂ : Set G)) := by
    ext x
    simp
  rw [hset]
  have c1 : (Z₁ : Set G).ncard = Nat.card Z₁ := (Nat.card_coe_set_eq (Z₁ : Set G)).symm
  have c2 : (Z₂ : Set G).ncard = Nat.card Z₂ := (Nat.card_coe_set_eq (Z₂ : Set G)).symm
  have cS : (ZS : Set G).ncard = Nat.card ZS := (Nat.card_coe_set_eq (ZS : Set G)).symm
  rw [c1, c2] at hu
  rw [cS] at hd
  obtain ⟨r1, hr1⟩ := e1
  obtain ⟨r2, hr2⟩ := e2
  obtain ⟨rS, hrS⟩ := eS
  exact ⟨(rS - r1 - r2), by omega⟩

theorem exists_conj_mem_centerOf_of_transitive {S T C Z₁ Z₂ : Subgroup G} (hST : S ≤ T)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) (hT : IsPGroup 2 T)
    (hZ₁ : Z₁ ≤ centerOf S) (hZ₂ : Z₂ ≤ centerOf S) (hne₁ : Z₁ ≠ ⊥) (hne₂ : Z₂ ≠ ⊥)
    (hZ₁₂ : Z₁ ⊓ Z₂ = ⊥) (hT₁ : T ≤ Subgroup.normalizer (Z₁ : Set G))
    (hT₂ : T ≤ Subgroup.normalizer (Z₂ : Set G))
    (hC₁ : ∀ x ∈ Z₁, ∀ y ∈ Z₁, x ≠ 1 → y ≠ 1 → ∃ c ∈ C, c * x * c⁻¹ = y)
    (hC₂ : ∀ x ∈ Z₂, ∀ y ∈ Z₂, x ≠ 1 → y ≠ 1 → ∃ c ∈ C, c * x * c⁻¹ = y)
    (hC₃ : ∀ x ∈ centerOf S, ∀ y ∈ centerOf S, x ∉ Z₁ → x ∉ Z₂ → y ∉ Z₁ → y ∉ Z₂ →
      ∃ c ∈ C, c * x * c⁻¹ = y) :
    ∀ u ∈ centerOf S, u ≠ 1 → ∃ c ∈ C, c * u * c⁻¹ ∈ centerOf T := by
  have hS2 : IsPGroup 2 S := hT.to_le hST
  have hcS : centerOf S ≤ S := inf_le_left
  have key : ∀ X : Set G, (∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) → Odd X.ncard →
      X ⊆ (centerOf S : Set G) → (∀ x ∈ X, ∀ y ∈ X, ∃ c ∈ C, c * x * c⁻¹ = y) →
      ∀ u ∈ X, ∃ c ∈ C, c * u * c⁻¹ ∈ centerOf T := by
    intro X hinv hodd hX htrans u hu
    obtain ⟨x₀, hx₀, hfix⟩ := exists_fixed_of_odd_ncard hT hodd hinv
    obtain ⟨c, hc, hcu⟩ := htrans u hu x₀ hx₀
    refine ⟨c, hc, ?_⟩
    rw [hcu]
    refine ⟨hST (hcS (hX hx₀)), Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have := hfix t ht
    calc t * x₀ = t * x₀ * t⁻¹ * t := by group
      _ = x₀ * t := by rw [this]
  have hinvN : ∀ (Z : Subgroup G), T ≤ Subgroup.normalizer (Z : Set G) →
      ∀ t ∈ T, ∀ x : G, t * x * t⁻¹ ∈ Z ↔ x ∈ Z := fun Z hZ t ht x =>
    (Subgroup.mem_normalizer_iff.mp (hZ ht) x).symm
  intro u hu hu1
  by_cases hu₁ : u ∈ Z₁
  · refine key {x | x ∈ Z₁ ∧ x ≠ 1} ?_ (odd_ncard_nonone (hS2.to_le (hZ₁.trans hcS)) hne₁) ?_ ?_
      u ⟨hu₁, hu1⟩
    · rintro t ht x ⟨hx, hx1⟩
      refine ⟨(hinvN Z₁ hT₁ t ht x).mpr hx, fun h => hx1 ?_⟩
      have : t * x * t⁻¹ = 1 := h
      simpa using this
    · exact fun x hx => hZ₁ hx.1
    · intro x hx y hy
      exact hC₁ x hx.1 y hy.1 hx.2 hy.2
  by_cases hu₂ : u ∈ Z₂
  · refine key {x | x ∈ Z₂ ∧ x ≠ 1} ?_ (odd_ncard_nonone (hS2.to_le (hZ₂.trans hcS)) hne₂) ?_ ?_
      u ⟨hu₂, hu1⟩
    · rintro t ht x ⟨hx, hx1⟩
      refine ⟨(hinvN Z₂ hT₂ t ht x).mpr hx, fun h => hx1 ?_⟩
      have : t * x * t⁻¹ = 1 := h
      simpa using this
    · exact fun x hx => hZ₂ hx.1
    · intro x hx y hy
      exact hC₂ x hx.1 y hy.1 hx.2 hy.2
  · refine key {x | x ∈ centerOf S ∧ x ∉ Z₁ ∧ x ∉ Z₂} ?_ ?_ ?_ ?_ u ⟨hu, hu₁, hu₂⟩
    · rintro t ht x ⟨hx, hx1, hx2⟩
      exact ⟨conj_mem_centerOf (hTS ht) hx, fun h => hx1 ((hinvN Z₁ hT₁ t ht x).mp h),
        fun h => hx2 ((hinvN Z₂ hT₂ t ht x).mp h)⟩
    · exact odd_ncard_third hZ₁ hZ₂ hZ₁₂
        (even_card_of_isPGroup_two (hS2.to_le (hZ₁.trans hcS)) hne₁)
        (even_card_of_isPGroup_two (hS2.to_le (hZ₂.trans hcS)) hne₂)
        (even_card_of_isPGroup_two (hS2.to_le hcS) (fun h => hne₁ (by
          rw [eq_bot_iff]; exact (hZ₁.trans h.le))))
    · exact fun x hx => hx.1
    · intro x hx y hy
      exact hC₃ x hx.1 y hy.1 hx.2.1 hx.2.2 hy.2.1 hy.2.2

end CFSG.Quasithin.H13.Sec53F
