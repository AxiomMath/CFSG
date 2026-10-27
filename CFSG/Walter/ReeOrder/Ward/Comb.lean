module

public import Mathlib.Data.Finset.Card

public section

namespace CFSG.Walter.Ward

variable {α : Type*} [DecidableEq α]

theorem two_of_three {T X : Finset α} (hT : T.card = 3) (hX : X ⊆ T) (hXc : X.card = 2) :
    ∃ u ∈ T, X = T.erase u := by
  have hd : (T \ X).card = 1 := by rw [Finset.card_sdiff_of_subset hX]; omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hd
  have huT : u ∈ T := (Finset.mem_sdiff.mp (hu ▸ Finset.mem_singleton_self u)).1
  refine ⟨u, huT, ?_⟩
  ext t
  rw [Finset.mem_erase]
  constructor
  · intro ht
    refine ⟨?_, hX ht⟩
    rintro rfl
    exact (Finset.mem_sdiff.mp (hu ▸ Finset.mem_singleton_self t)).2 ht
  · rintro ⟨htu, htT⟩
    by_contra htX
    have : t ∈ T \ X := Finset.mem_sdiff.mpr ⟨htT, htX⟩
    rw [hu, Finset.mem_singleton] at this
    exact htu this

theorem pair_of_card_two {X : Finset α} (h : X.card = 2) :
    ∃ b c, b ≠ c ∧ X = {b, c} := by
  obtain ⟨b, c, hbc, rfl⟩ := Finset.card_eq_two.mp h
  exact ⟨b, c, hbc, rfl⟩

theorem three_sets (S₁ S₂ S₃ : Finset α) (o : α) (h₁ : S₁.card = 4) (h₂ : S₂.card = 4)
    (h₁₂ : (S₁ ∩ S₂).card = 2) (h₁₃ : (S₁ ∩ S₃).card = 2)
    (h₂₃ : (S₂ ∩ S₃).card = 2) (ho₁ : o ∈ S₁) (ho₂ : o ∉ S₂) (ho₃ : o ∉ S₃) :
    (∃ a b c x y : α, S₁ = {o, a, b, c} ∧ S₂ = {b, c, x, y} ∧
      o ≠ a ∧ o ≠ b ∧ o ≠ c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      b ≠ x ∧ b ≠ y ∧ c ≠ x ∧ c ≠ y ∧ x ≠ y ∧
      a ∉ S₂ ∧ a ∉ S₃ ∧ b ∈ S₃ ∧ c ∈ S₃ ∧ x ∉ S₁ ∧ x ∉ S₃ ∧ y ∉ S₁ ∧ y ∉ S₃) ∨
    (∃ a b c x w : α, S₁ = {o, a, b, c} ∧ S₂ = {a, c, x, w} ∧
      o ≠ a ∧ o ≠ b ∧ o ≠ c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ≠ x ∧ a ≠ w ∧ c ≠ x ∧ c ≠ w ∧ x ≠ w ∧
      a ∉ S₃ ∧ b ∉ S₂ ∧ b ∈ S₃ ∧ c ∈ S₃ ∧ x ∉ S₁ ∧ x ∉ S₃ ∧ w ∉ S₁ ∧ w ∈ S₃) := by
  set T := S₁.erase o with hT
  have hTc : T.card = 3 := by rw [hT, Finset.card_erase_of_mem ho₁, h₁]
  have hXT : S₁ ∩ S₂ ⊆ T := by
    intro t ht
    rw [Finset.mem_inter] at ht
    rw [hT, Finset.mem_erase]
    exact ⟨fun h => ho₂ (h ▸ ht.2), ht.1⟩
  have hYT : S₁ ∩ S₃ ⊆ T := by
    intro t ht
    rw [Finset.mem_inter] at ht
    rw [hT, Finset.mem_erase]
    exact ⟨fun h => ho₃ (h ▸ ht.2), ht.1⟩
  obtain ⟨u, huT, hX⟩ := two_of_three hTc hXT h₁₂
  obtain ⟨v, hvT, hY⟩ := two_of_three hTc hYT h₁₃
  have huo : u ≠ o := (Finset.mem_erase.mp huT).1
  have hvo : v ≠ o := (Finset.mem_erase.mp hvT).1
  have hu1 : u ∈ S₁ := (Finset.mem_erase.mp huT).2
  have hv1 : v ∈ S₁ := (Finset.mem_erase.mp hvT).2
  have mem2 : ∀ t ∈ S₁, t ≠ o → (t ∈ S₂ ↔ t ≠ u) := by
    intro t ht hto
    constructor
    · intro h2
      have : t ∈ S₁ ∩ S₂ := Finset.mem_inter.mpr ⟨ht, h2⟩
      rw [hX, Finset.mem_erase] at this
      exact this.1
    · intro htu
      have : t ∈ T.erase u := Finset.mem_erase.mpr ⟨htu, Finset.mem_erase.mpr ⟨hto, ht⟩⟩
      rw [← hX] at this
      exact (Finset.mem_inter.mp this).2
  have mem3 : ∀ t ∈ S₁, t ≠ o → (t ∈ S₃ ↔ t ≠ v) := by
    intro t ht hto
    constructor
    · intro h3
      have : t ∈ S₁ ∩ S₃ := Finset.mem_inter.mpr ⟨ht, h3⟩
      rw [hY, Finset.mem_erase] at this
      exact this.1
    · intro htv
      have : t ∈ T.erase v := Finset.mem_erase.mpr ⟨htv, Finset.mem_erase.mpr ⟨hto, ht⟩⟩
      rw [← hY] at this
      exact (Finset.mem_inter.mp this).2
  have hd2 : (S₂ \ S₁).card = 2 := by
    have h := Finset.card_sdiff_add_card_inter S₂ S₁
    rw [Finset.inter_comm] at h
    omega
  obtain ⟨x₀, y₀, hxy₀, hxyS⟩ := pair_of_card_two hd2
  have hx₀ : x₀ ∈ S₂ ∧ x₀ ∉ S₁ := Finset.mem_sdiff.mp (by rw [hxyS]; simp)
  have hy₀ : y₀ ∈ S₂ ∧ y₀ ∉ S₁ := Finset.mem_sdiff.mp (by rw [hxyS]; simp)
  have hS₂split : ∀ t, t ∈ S₂ ↔ (t ∈ S₁ ∩ S₂ ∨ t = x₀ ∨ t = y₀) := by
    intro t
    constructor
    · intro ht
      by_cases ht1 : t ∈ S₁
      · exact Or.inl (Finset.mem_inter.mpr ⟨ht1, ht⟩)
      · have : t ∈ S₂ \ S₁ := Finset.mem_sdiff.mpr ⟨ht, ht1⟩
        rw [hxyS] at this
        exact Or.inr (by simpa using this)
    · rintro (h | rfl | rfl)
      · exact (Finset.mem_inter.mp h).2
      · exact hx₀.1
      · exact hy₀.1
  by_cases huv : u = v
  ·
    subst huv
    left
    obtain ⟨b, c, hbc, hbcX⟩ := pair_of_card_two h₁₂
    have hb : b ∈ S₁ ∩ S₂ := by rw [hbcX]; simp
    have hc : c ∈ S₁ ∩ S₂ := by rw [hbcX]; simp
    have hbT : b ∈ T.erase u := by rw [← hX]; exact hb
    have hcT : c ∈ T.erase u := by rw [← hX]; exact hc
    have hbu : b ≠ u := (Finset.mem_erase.mp hbT).1
    have hcu : c ≠ u := (Finset.mem_erase.mp hcT).1
    have hbo : b ≠ o := (Finset.mem_erase.mp (Finset.mem_erase.mp hbT).2).1
    have hco : c ≠ o := (Finset.mem_erase.mp (Finset.mem_erase.mp hcT).2).1
    have hb1 : b ∈ S₁ := (Finset.mem_inter.mp hb).1
    have hc1 : c ∈ S₁ := (Finset.mem_inter.mp hc).1
    have hb3 : b ∈ S₃ := (mem3 b hb1 hbo).mpr hbu
    have hc3 : c ∈ S₃ := (mem3 c hc1 hco).mpr hcu
    have h23eq : S₂ ∩ S₃ = {b, c} := by
      have hsub : ({b, c} : Finset α) ⊆ S₂ ∩ S₃ := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hb).2, hb3⟩
        · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hc).2, hc3⟩
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [h₂₃, Finset.card_pair hbc])).symm
    have hx3 : x₀ ∉ S₃ := by
      intro h
      have : x₀ ∈ S₂ ∩ S₃ := Finset.mem_inter.mpr ⟨hx₀.1, h⟩
      rw [h23eq] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hx₀.2 hb1
      · exact hx₀.2 hc1
    have hy3 : y₀ ∉ S₃ := by
      intro h
      have : y₀ ∈ S₂ ∩ S₃ := Finset.mem_inter.mpr ⟨hy₀.1, h⟩
      rw [h23eq] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hy₀.2 hb1
      · exact hy₀.2 hc1
    refine ⟨u, b, c, x₀, y₀, ?_, ?_, huo.symm, hbo.symm, hco.symm, hbu.symm, hcu.symm, hbc,
      fun h => hx₀.2 (h ▸ hb1), fun h => hy₀.2 (h ▸ hb1), fun h => hx₀.2 (h ▸ hc1),
      fun h => hy₀.2 (h ▸ hc1), hxy₀, fun h => ((mem2 u hu1 huo).mp h) rfl,
      fun h => ((mem3 u hu1 huo).mp h) rfl, hb3, hc3, hx₀.2, hx3, hy₀.2, hy3⟩
    ·
      have hsub : ({o, u, b, c} : Finset α) ⊆ S₁ := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [ho₁, hu1, hb1, hc1]
      have hcard : ({o, u, b, c} : Finset α).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [huo.symm, hbo.symm, hco.symm]),
          Finset.card_insert_of_notMem (by simp [hbu.symm, hcu.symm]), Finset.card_pair hbc]
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, h₁])).symm
    · ext t
      rw [hS₂split t, hbcX]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
  ·
    right
    have hd : ((T.erase u).erase v).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm huv, hvT⟩),
        Finset.card_erase_of_mem huT, hTc]
    obtain ⟨c, hcw⟩ := Finset.card_eq_one.mp hd
    have hcmem : c ∈ (T.erase u).erase v := by rw [hcw]; exact Finset.mem_singleton_self c
    have hcv : c ≠ v := (Finset.mem_erase.mp hcmem).1
    have hcu : c ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hcmem).2).1
    have hco : c ≠ o := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp
      hcmem).2).2).1
    have hc1 : c ∈ S₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp
      hcmem).2).2).2
    have hv2 : v ∈ S₂ := (mem2 v hv1 hvo).mpr (Ne.symm huv)
    have hv3 : v ∉ S₃ := fun h => ((mem3 v hv1 hvo).mp h) rfl
    have hu2 : u ∉ S₂ := fun h => ((mem2 u hu1 huo).mp h) rfl
    have hu3 : u ∈ S₃ := (mem3 u hu1 huo).mpr huv
    have hc2 : c ∈ S₂ := (mem2 c hc1 hco).mpr hcu
    have hc3 : c ∈ S₃ := (mem3 c hc1 hco).mpr hcv
    have hXeq : S₁ ∩ S₂ = {v, c} := by
      have hsub : ({v, c} : Finset α) ⊆ S₁ ∩ S₂ := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hv1, hv2⟩
        · exact Finset.mem_inter.mpr ⟨hc1, hc2⟩
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [h₁₂, Finset.card_pair hcv.symm])).symm
    have h23c : c ∈ S₂ ∩ S₃ := Finset.mem_inter.mpr ⟨hc2, hc3⟩
    have hd23 : ((S₂ ∩ S₃).erase c).card = 1 := by rw [Finset.card_erase_of_mem h23c, h₂₃]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hd23
    have hwmem : w ∈ (S₂ ∩ S₃).erase c := by rw [hw]; exact Finset.mem_singleton_self w
    have hwc : w ≠ c := (Finset.mem_erase.mp hwmem).1
    have hw2 : w ∈ S₂ := (Finset.mem_inter.mp (Finset.mem_erase.mp hwmem).2).1
    have hw3 : w ∈ S₃ := (Finset.mem_inter.mp (Finset.mem_erase.mp hwmem).2).2
    have hw1 : w ∉ S₁ := by
      intro h
      have hwo : w ≠ o := fun h' => ho₂ (h' ▸ hw2)
      have hwv : w ≠ v := fun h' => hv3 (h' ▸ hw3)
      have hwu : w ≠ u := fun h' => hu2 (h' ▸ hw2)
      have : w ∈ (T.erase u).erase v :=
        Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hwu, Finset.mem_erase.mpr ⟨hwo, h⟩⟩⟩
      rw [hcw, Finset.mem_singleton] at this
      exact hwc this
    have hwxy : w = x₀ ∨ w = y₀ := by
      rcases (hS₂split w).mp hw2 with h | h | h
      · exact absurd (Finset.mem_inter.mp h).1 hw1
      · exact Or.inl h
      · exact Or.inr h
    have h23eq : S₂ ∩ S₃ = {c, w} := by
      have hsub : ({c, w} : Finset α) ⊆ S₂ ∩ S₃ := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact h23c
        · exact Finset.mem_inter.mpr ⟨hw2, hw3⟩
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [h₂₃, Finset.card_pair hwc.symm])).symm
    obtain ⟨x, hxS₂, hx1, hxw, hS₂eq⟩ : ∃ x, x ∈ S₂ ∧ x ∉ S₁ ∧ x ≠ w ∧
        ∀ t, t ∈ S₂ ↔ (t = v ∨ t = c ∨ t = x ∨ t = w) := by
      rcases hwxy with rfl | rfl
      · refine ⟨y₀, hy₀.1, hy₀.2, Ne.symm hxy₀, fun t => ?_⟩
        rw [hS₂split t, hXeq]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨x₀, hx₀.1, hx₀.2, hxy₀, fun t => ?_⟩
        rw [hS₂split t, hXeq]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
    have hx3 : x ∉ S₃ := by
      intro h
      have : x ∈ S₂ ∩ S₃ := Finset.mem_inter.mpr ⟨hxS₂, h⟩
      rw [h23eq] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hx1 hc1
      · exact hxw rfl
    refine ⟨v, u, c, x, w, ?_, ?_, hvo.symm, huo.symm, hco.symm, Ne.symm huv, Ne.symm hcv,
      Ne.symm hcu, fun h => hx1 (h ▸ hv1), fun h => hw1 (h ▸ hv1),
      fun h => hx1 (h ▸ hc1), fun h => hw1 (h ▸ hc1), hxw, hv3, hu2, hu3, hc3, hx1, hx3, hw1,
      hw3⟩
    · have hsub : ({o, v, u, c} : Finset α) ⊆ S₁ := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [ho₁, hv1, hu1, hc1]
      have hcard : ({o, v, u, c} : Finset α).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hvo.symm, huo.symm, hco.symm]),
          Finset.card_insert_of_notMem (by simp [Ne.symm huv, Ne.symm hcv]),
          Finset.card_pair (Ne.symm hcu)]
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, h₁])).symm
    · ext t
      rw [hS₂eq t]
      simp only [Finset.mem_insert, Finset.mem_singleton]

end CFSG.Walter.Ward
