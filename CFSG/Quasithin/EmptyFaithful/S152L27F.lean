module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

theorem mem_or_mem_or_inv_mul_mem_of_card_le_two_mul152 {A : Type*} [Group A] [Finite A]
    (B : Subgroup A) (h : Nat.card A ≤ 2 * Nat.card B) (a b : A) :
    a ∈ B ∨ b ∈ B ∨ a⁻¹ * b ∈ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb, hab⟩ := hcon
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup B
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hq : Nat.card (A ⧸ B) ≤ 2 := by
    by_contra hq
    push Not at hq
    have : 2 * Nat.card B < Nat.card (A ⧸ B) * Nat.card B :=
      Nat.mul_lt_mul_of_pos_right hq hBpos
    omega
  let f : Fin 3 → A ⧸ B := ![QuotientGroup.mk (1 : A), QuotientGroup.mk a, QuotientGroup.mk b]
  have h01 : f 0 ≠ f 1 := by
    intro h'
    apply ha
    have := QuotientGroup.eq.mp h'
    simpa using this
  have h02 : f 0 ≠ f 2 := by
    intro h'
    apply hb
    have := QuotientGroup.eq.mp h'
    simpa using this
  have h12 : f 1 ≠ f 2 := by
    intro h'
    exact hab (QuotientGroup.eq.mp h')
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij ‹_› | exact absurd hij.symm ‹_›
  have h3 : Nat.card (Fin 3) ≤ Nat.card (A ⧸ B) := Nat.card_le_card_of_injective f hf
  simp at h3
  omega

variable {G : Type*} [Group G] [Finite G]

theorem commutator_mem_of_card_four152 {T Z ZS : Subgroup G} (hZZS : Z ≤ ZS)
    (hTn : ∀ t ∈ T, ∀ s ∈ ZS, t * s * t⁻¹ ∈ ZS) (hTZ : ∀ t ∈ T, ∀ z ∈ Z, t * z * t⁻¹ = z)
    (hab : ∀ a ∈ ZS, ∀ b ∈ ZS, a * b = b * a)
    (hcase : Z = ZS ∨ (Nat.card Z = 2 ∧ Nat.card ZS = 4)) :
    ∀ t ∈ T, ∀ s ∈ ZS, t * s * t⁻¹ * s⁻¹ ∈ Z := by
  intro t ht s hs
  rcases hcase with hZ | ⟨hZ2, hZS4⟩
  · rw [hZ]
    exact ZS.mul_mem (hTn t ht s hs) (ZS.inv_mem hs)
  · by_cases hsZ : s ∈ Z
    · rw [hTZ t ht s hsZ]; simp
    · have hs' := hTn t ht s hs
      have hs'Z : t * s * t⁻¹ ∉ Z := by
        intro h
        apply hsZ
        have := hTZ t⁻¹ (T.inv_mem ht) _ h
        have e : t⁻¹ * (t * s * t⁻¹) * t⁻¹⁻¹ = s := by group
        rw [e] at this
        rw [this]; exact h
      have hcard : Nat.card ZS ≤ 2 * Nat.card (Z.subgroupOf ZS) := by
        have : Nat.card (Z.subgroupOf ZS) = Nat.card Z :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZZS).toEquiv
        rw [this]; omega
      rcases mem_or_mem_or_inv_mul_mem_of_card_le_two_mul152 (Z.subgroupOf ZS) hcard ⟨s, hs⟩
          ⟨t * s * t⁻¹, hs'⟩ with h | h | h
      · exact absurd (Subgroup.mem_subgroupOf.mp h) hsZ
      · exact absurd (Subgroup.mem_subgroupOf.mp h) hs'Z
      · have h' : s⁻¹ * (t * s * t⁻¹) ∈ Z := Subgroup.mem_subgroupOf.mp h
        have hc := hab _ (ZS.inv_mem hs) _ hs'
        have e : t * s * t⁻¹ * s⁻¹ = s⁻¹ * (t * s * t⁻¹) := hc.symm
        rw [e]; exact h'

theorem card_sup_le_two_mul152 {Vc ZS L : Subgroup G} (hZVc : ZS ≤ Vc) (hZL : ZS ≤ L)
    (hn : Vc ≤ Subgroup.normalizer (L : Set G)) (hcard : Nat.card Vc ≤ 2 * Nat.card ZS) :
    Nat.card ↥(Vc ⊔ L) ≤ 2 * Nat.card L := by
  have hprod : ((Vc ⊔ L : Subgroup G) : Set G) = (Vc : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Vc L hn
  have hmul := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient L (Vc : Set G)
  rw [← hprod] at hmul
  have hc : Nat.card ↥(Vc ⊔ L) =
      Nat.card L * Nat.card (((Vc : Set G).image (↑) : Set (G ⧸ L))) := hmul
  have hcard' : Nat.card Vc ≤ 2 * Nat.card (ZS.subgroupOf Vc) := by
    have : Nat.card (ZS.subgroupOf Vc) = Nat.card ZS :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZVc).toEquiv
    rw [this]; exact hcard
  have hpair : ∀ a ∈ Vc, ∀ b ∈ Vc,
      (a : G ⧸ L) = ((1 : G) : G ⧸ L) ∨ (b : G ⧸ L) = ((1 : G) : G ⧸ L) ∨ (a : G ⧸ L) = b := by
    intro a ha b hb
    have hZ1 : ∀ x ∈ ZS, (x : G ⧸ L) = ((1 : G) : G ⧸ L) := by
      intro x hx
      rw [QuotientGroup.eq]
      simpa using L.inv_mem (hZL hx)
    rcases mem_or_mem_or_inv_mul_mem_of_card_le_two_mul152 (ZS.subgroupOf Vc) hcard'
        ⟨a, ha⟩ ⟨b, hb⟩ with h | h | h
    · exact Or.inl (hZ1 a (Subgroup.mem_subgroupOf.mp h))
    · exact Or.inr (Or.inl (hZ1 b (Subgroup.mem_subgroupOf.mp h)))
    · refine Or.inr (Or.inr ?_)
      rw [QuotientGroup.eq]
      exact hZL (Subgroup.mem_subgroupOf.mp h)
  have himg : Nat.card (((Vc : Set G).image (↑) : Set (G ⧸ L))) ≤ 2 := by
    by_cases hex : ∃ c ∈ Vc, (c : G ⧸ L) ≠ ((1 : G) : G ⧸ L)
    · obtain ⟨c, hc1, hc2⟩ := hex
      have hsub : ((Vc : Set G).image (↑) : Set (G ⧸ L)) ⊆ {((1 : G) : G ⧸ L), (c : G ⧸ L)} := by
        rintro _ ⟨a, ha, rfl⟩
        rcases hpair a ha c hc1 with h | h | h
        · exact Or.inl h
        · exact absurd h hc2
        · exact Or.inr h
      calc Nat.card (((Vc : Set G).image (↑) : Set (G ⧸ L)))
          = Set.ncard ((Vc : Set G).image (↑) : Set (G ⧸ L)) := Nat.card_coe_set_eq _
        _ ≤ Set.ncard ({((1 : G) : G ⧸ L), (c : G ⧸ L)} : Set (G ⧸ L)) := Set.ncard_le_ncard hsub
        _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    · push Not at hex
      have hsub : ((Vc : Set G).image (↑) : Set (G ⧸ L)) ⊆ {((1 : G) : G ⧸ L)} := by
        rintro _ ⟨a, ha, rfl⟩
        exact hex a ha
      calc Nat.card (((Vc : Set G).image (↑) : Set (G ⧸ L)))
          = Set.ncard ((Vc : Set G).image (↑) : Set (G ⧸ L)) := Nat.card_coe_set_eq _
        _ ≤ Set.ncard ({((1 : G) : G ⧸ L)} : Set (G ⧸ L)) := Set.ncard_le_ncard hsub
        _ ≤ 2 := by rw [Set.ncard_singleton]; omega
  rw [hc, mul_comm]
  exact Nat.mul_le_mul_right _ himg

end CFSG.Quasithin
