module

public import CFSG.Quasithin.H13.A6Setting134

public section

namespace CFSG.Quasithin.H13.A6

open Equiv MulAction
open scoped Pointwise

@[expose] def InP1 (σ : Perm (Fin 6)) : Prop :=
  (σ 4 : ℕ) / 2 = 2 ∧ (σ 5 : ℕ) / 2 = 2

instance : DecidablePred InP1 := fun σ =>
  inferInstanceAs (Decidable ((σ 4 : ℕ) / 2 = 2 ∧ (σ 5 : ℕ) / 2 = 2))

@[expose] def InP2 (σ : Perm (Fin 6)) : Prop :=
  ∀ i j : Fin 6, (i : ℕ) / 2 = (j : ℕ) / 2 → (σ i : ℕ) / 2 = (σ j : ℕ) / 2

instance : DecidablePred InP2 := fun σ => by
  unfold InP2
  infer_instance

theorem InP1.inv : ∀ σ : Perm (Fin 6), InP1 σ → InP1 σ⁻¹ := by
  decide +kernel

theorem InP2.inv : ∀ σ : Perm (Fin 6), InP2 σ → InP2 σ⁻¹ := by
  decide +kernel

theorem eq_four_or_five : ∀ i : Fin 6, (i : ℕ) / 2 = 2 → i = 4 ∨ i = 5 := by
  decide

@[expose] def P1sub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | InP1 σ}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨hb4, hb5⟩ := hb
    have key : ∀ i : Fin 6, (i : ℕ) / 2 = 2 → ((a i : Fin 6) : ℕ) / 2 = 2 := fun i hi => by
      rcases eq_four_or_five i hi with rfl | rfl
      · exact ha.1
      · exact ha.2
    exact ⟨key _ hb4, key _ hb5⟩
  inv_mem' := fun {a} ha => InP1.inv a ha

@[expose] def P2sub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | InP2 σ}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => fun i j hij => ha (b i) (b j) (hb i j hij)
  inv_mem' := fun {a} ha => InP2.inv a ha

theorem mem_P1sub {σ : Perm (Fin 6)} : σ ∈ P1sub ↔ InP1 σ := Iff.rfl

theorem mem_P2sub {σ : Perm (Fin 6)} : σ ∈ P2sub ↔ InP2 σ := Iff.rfl

@[expose] def IsSynDuad (s : Finset (Fin 6)) : Prop :=
  s = {0, 1} ∨ s = {2, 3} ∨ s = {4, 5}

instance : DecidablePred IsSynDuad := fun s => by
  unfold IsSynDuad
  infer_instance

@[expose] def BlockFor (σ : Perm (Fin 6)) (s : Finset (Fin 6)) : Prop :=
  s.image σ = s ∨ Disjoint (s.image σ) s

instance (σ : Perm (Fin 6)) : DecidablePred (BlockFor σ) := fun s => by
  unfold BlockFor
  infer_instance

theorem block_cases : ∀ s : Finset (Fin 6), 2 ≤ s.card → s.card ≤ 3 →
    BlockFor (swap 0 1 * swap 2 3) s → BlockFor (swap 0 2 * swap 1 3) s →
    BlockFor (swap 0 1 * swap 4 5) s → IsSynDuad s := by
  decide

theorem inP2_of_duads : ∀ σ : Perm (Fin 6), IsSynDuad (({0, 1} : Finset (Fin 6)).image σ) →
    IsSynDuad (({2, 3} : Finset (Fin 6)).image σ) →
    IsSynDuad (({4, 5} : Finset (Fin 6)).image σ) → InP2 σ := by
  decide +kernel

theorem orbit_zero_facts : (swap (0 : Fin 6) 1 * swap 2 3 : Perm (Fin 6)) 0 = 1 ∧
    (swap (0 : Fin 6) 2 * swap 1 3 : Perm (Fin 6)) 0 = 2 ∧
    ((swap (0 : Fin 6) 1 * swap 2 3) * (swap 0 2 * swap 1 3) : Perm (Fin 6)) 0 = 3 ∧
    (swap (0 : Fin 6) 1 * swap 4 5 : Perm (Fin 6)) 4 = 5 ∧
    (swap (0 : Fin 6) 1 * swap 4 5 : Perm (Fin 6)) 5 = 4 := by
  decide

theorem synDuad_cases : ∀ s : Finset (Fin 6), IsSynDuad s →
    ∀ a : Fin 6, a ∈ s → (a = 0 ∨ a = 1 → s = {0, 1}) ∧ (a = 2 ∨ a = 3 → s = {2, 3}) ∧
      (a = 4 ∨ a = 5 → s = {4, 5}) := by
  decide

section Prim

variable (Y : Subgroup (Perm (Fin 6)))

theorem smul_coe_finset (y : ↥Y) (s : Finset (Fin 6)) :
    y • (s : Set (Fin 6)) = ((s.image (y : Perm (Fin 6)) : Finset (Fin 6)) : Set (Fin 6)) := by
  rw [Finset.coe_image, ← Set.image_smul]
  rfl

theorem blockFor_of_isBlock {B : Set (Fin 6)} (hB : IsBlock Y B) {s : Finset (Fin 6)}
    (hs : (s : Set (Fin 6)) = B) {σ : Perm (Fin 6)} (hσ : σ ∈ Y) : BlockFor σ s := by
  subst hs
  rcases hB.smul_eq_or_disjoint ⟨σ, hσ⟩ with h | h
  · left
    apply Finset.coe_injective
    rw [← smul_coe_finset Y ⟨σ, hσ⟩, h]
  · right
    rw [← Finset.disjoint_coe, ← smul_coe_finset Y ⟨σ, hσ⟩]
    exact h

variable {Y}

theorem isPreprimitive_of (h1 : swap 0 1 * swap 2 3 ∈ Y) (h2 : swap 0 2 * swap 1 3 ∈ Y)
    (h3 : swap 0 1 * swap 4 5 ∈ Y) (hP1 : ¬ ∀ y ∈ Y, InP1 y) (hP2 : ¬ ∀ y ∈ Y, InP2 y) :
    IsPreprimitive Y (Fin 6) := by
  classical
  obtain ⟨o1, o2, o3, o4, o5⟩ := orbit_zero_facts
  have horb : ∀ i : Fin 6, ∃ g : ↥Y, g • (0 : Fin 6) = i := by
    have h03 : ∀ i : Fin 6, (i : ℕ) / 2 ≠ 2 → ∃ g : ↥Y, g • (0 : Fin 6) = i := by
      intro i hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
        fin_cases i <;> simp_all
      rcases this with rfl | rfl | rfl | rfl
      · exact ⟨1, one_smul _ _⟩
      · exact ⟨⟨_, h1⟩, o1⟩
      · exact ⟨⟨_, h2⟩, o2⟩
      · exact ⟨⟨_, Y.mul_mem h1 h2⟩, o3⟩
    push Not at hP1
    obtain ⟨y, hy, hyP⟩ := hP1
    have h45 : ∃ g : ↥Y, g • (0 : Fin 6) = 4 := by
      unfold InP1 at hyP
      by_cases h4 : ((y 4 : Fin 6) : ℕ) / 2 = 2
      · have h5 : ((y 5 : Fin 6) : ℕ) / 2 ≠ 2 := fun h5 => hyP ⟨h4, h5⟩
        obtain ⟨g, hg⟩ := h03 _ h5
        refine ⟨⟨_, h3⟩ * ⟨y, hy⟩⁻¹ * g, ?_⟩
        rw [mul_smul, mul_smul, hg]
        show (swap 0 1 * swap 4 5 : Perm (Fin 6)) (y⁻¹ (y 5)) = 4
        rw [Equiv.Perm.inv_eq_iff_eq.2 rfl, o5]
      · obtain ⟨g, hg⟩ := h03 _ h4
        refine ⟨⟨y, hy⟩⁻¹ * g, ?_⟩
        rw [mul_smul, hg]
        show y⁻¹ (y 4) = 4
        exact Equiv.Perm.inv_eq_iff_eq.2 rfl
    intro i
    by_cases hi : (i : ℕ) / 2 = 2
    · obtain ⟨g, hg⟩ := h45
      have : i = 4 ∨ i = 5 := by
        fin_cases i <;> simp_all
      rcases this with rfl | rfl
      · exact ⟨g, hg⟩
      · refine ⟨⟨_, h3⟩ * g, ?_⟩
        rw [mul_smul, hg]
        exact o4
    · exact h03 i hi
  have hpre : IsPretransitive Y (Fin 6) := ⟨fun x z => by
    obtain ⟨gx, hgx⟩ := horb x
    obtain ⟨gz, hgz⟩ := horb z
    exact ⟨gz * gx⁻¹, by rw [mul_smul, ← hgx, inv_smul_smul, hgz]⟩⟩
  refine { toIsPretransitive := hpre, isTrivialBlock_of_isBlock := fun {B} hB => ?_ }
  by_contra hnt
  unfold IsTrivialBlock at hnt
  push Not at hnt
  obtain ⟨hns, hnu⟩ := hnt
  have hcard2 : 2 ≤ B.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card']
    by_contra hlt
    push Not at hlt
    exact hns.not_subsingleton (Set.ncard_le_one_iff_subsingleton.1 (by omega))
  have hcard3 : B.toFinset.card ≤ 3 := by
    rw [← Set.ncard_eq_toFinset_card']
    by_contra hlt
    push Not at hlt
    exact hnu (hB.eq_univ_of_card_lt (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega))
  have hduad := block_cases _ hcard2 hcard3 (blockFor_of_isBlock Y hB (Set.coe_toFinset B) h1)
    (blockFor_of_isBlock Y hB (Set.coe_toFinset B) h2)
    (blockFor_of_isBlock Y hB (Set.coe_toFinset B) h3)
  have htr : ∀ g : ↥Y, IsSynDuad (g • B).toFinset := by
    intro g
    have hgB := hB.translate g
    refine block_cases _ ?_ ?_ (blockFor_of_isBlock Y hgB (Set.coe_toFinset _) h1)
      (blockFor_of_isBlock Y hgB (Set.coe_toFinset _) h2)
      (blockFor_of_isBlock Y hgB (Set.coe_toFinset _) h3)
    · rw [← Set.ncard_eq_toFinset_card', Set.ncard_smul_set, Set.ncard_eq_toFinset_card']
      exact hcard2
    · rw [← Set.ncard_eq_toFinset_card', Set.ncard_smul_set, Set.ncard_eq_toFinset_card']
      exact hcard3
  obtain ⟨b, hb⟩ : B.Nonempty := hns.nonempty
  have hduads : ∀ a : Fin 6, ∃ g : ↥Y, a ∈ g • B := by
    intro a
    obtain ⟨g, hg⟩ := hpre.exists_smul_eq b a
    exact ⟨g, ⟨b, hb, hg⟩⟩
  have hfin : ∀ (g : ↥Y) (a : Fin 6), a ∈ g • B → a ∈ (g • B).toFinset := fun g a ha =>
    Set.mem_toFinset.2 ha
  obtain ⟨g01, hg01⟩ := hduads 0
  obtain ⟨g23, hg23⟩ := hduads 2
  obtain ⟨g45, hg45⟩ := hduads 4
  have e01 : (g01 • B).toFinset = {0, 1} :=
    (synDuad_cases _ (htr g01) 0 (hfin _ _ hg01)).1 (Or.inl rfl)
  have e23 : (g23 • B).toFinset = {2, 3} :=
    (synDuad_cases _ (htr g23) 2 (hfin _ _ hg23)).2.1 (Or.inl rfl)
  have e45 : (g45 • B).toFinset = {4, 5} :=
    (synDuad_cases _ (htr g45) 4 (hfin _ _ hg45)).2.2 (Or.inl rfl)
  apply hP2
  intro y hy
  have himg : ∀ (g : ↥Y) (s : Finset (Fin 6)), (g • B).toFinset = s →
      IsSynDuad (s.image y) := by
    intro g s hs
    have h := htr (⟨y, hy⟩ * g)
    rw [mul_smul] at h
    have hcoe : ((⟨y, hy⟩ : ↥Y) • (g • B)).toFinset = ((g • B).toFinset).image y := by
      apply Finset.coe_injective
      rw [Set.coe_toFinset, ← smul_coe_finset Y ⟨y, hy⟩, Set.coe_toFinset]
    rw [hcoe, hs] at h
    exact h
  exact inP2_of_duads y (himg _ _ e01) (himg _ _ e23) (himg _ _ e45)

end Prim

theorem overgroup_S6 (Y : Subgroup (Perm (Fin 6))) (hmem : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ Y) :
    (∀ y ∈ Y, InP1 y) ∨ (∀ y ∈ Y, InP2 y) ∨ Y = ⊤ := by
  by_cases hP1 : ∀ y ∈ Y, InP1 y
  · exact Or.inl hP1
  by_cases hP2 : ∀ y ∈ Y, InP2 y
  · exact Or.inr (Or.inl hP2)
  have hD : InD6 (swap 0 1 * swap 2 3) ∧ InD6 (swap 0 2 * swap 1 3) ∧
      InD6 (swap 0 1 * swap 4 5) ∧ InD6 (swap 0 1) := by decide
  have hprim := isPreprimitive_of (hmem _ hD.1) (hmem _ hD.2.1) (hmem _ hD.2.2.1) hP1 hP2
  exact Or.inr (Or.inr (Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hprim
    (swap 0 1) ⟨0, 1, by decide, rfl⟩ (hmem _ hD.2.2.2)))

abbrev ga : Perm (Fin 6) := swap 0 1 * swap 2 3

abbrev gb : Perm (Fin 6) := swap 0 2 * swap 1 3

abbrev gc : Perm (Fin 6) := swap 0 1 * swap 4 5

@[expose] def QA6list : List (Perm (Fin 6)) :=
  [1, ga * gc, gc, ga, gb, gc * gb, gb * gc, ga * gb]

@[expose] def WA6list : List (Perm (Fin 6)) :=
  [swap 3 4 * swap 4 5, swap 1 2 * swap 3 4, swap 1 2 * swap 3 5,
    swap 1 2 * swap 2 4 * swap 3 5 * swap 4 5, swap 1 4 * swap 2 4 * swap 3 5 * swap 4 5,
    swap 1 4 * swap 3 5]

theorem dc_cert : ∀ y : Perm (Fin 6), Equiv.Perm.sign y = 1 → ¬ InP1 y → ¬ InP2 y →
    ∃ q₁ ∈ QA6list, ∃ q₂ ∈ QA6list, q₁ * y * q₂ ∈ WA6list := by
  decide +kernel

theorem three_cycle_words :
    swap (3 : Fin 6) 4 * swap 4 5 = swap 3 5 * swap 3 4 ∧
    ga * gb * (swap 1 2 * swap 3 4) = swap 0 4 * swap 0 3 ∧
    ga * gb * (swap 1 2 * swap 3 5) = swap 0 5 * swap 0 3 ∧
    ga * gc * (swap 1 2 * swap 2 4 * swap 3 5 * swap 4 5) *
      (swap 1 2 * swap 2 4 * swap 3 5 * swap 4 5) = swap 1 3 * swap 1 5 ∧
    ga * gc * (swap 1 4 * swap 2 4 * swap 3 5 * swap 4 5) *
      (swap 1 4 * swap 2 4 * swap 3 5 * swap 4 5) = swap 1 5 * swap 1 2 ∧
    gb * (swap 1 4 * swap 3 5) * gc * (swap 1 4 * swap 3 5) = swap 0 2 * swap 0 4 := by
  decide

theorem exists_isThreeCycle {Y : Subgroup (Perm (Fin 6))} (ha : ga ∈ Y) (hb : gb ∈ Y)
    (hc : gc ∈ Y) {y : Perm (Fin 6)} (hy : y ∈ Y) (hsy : Equiv.Perm.sign y = 1)
    (hy1 : ¬ InP1 y) (hy2 : ¬ InP2 y) : ∃ g ∈ Y, Equiv.Perm.IsThreeCycle g := by
  have hQ : ∀ q ∈ QA6list, q ∈ Y := by
    intro q hq
    simp only [QA6list, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Y.one_mem
    · exact Y.mul_mem ha hc
    · exact hc
    · exact ha
    · exact hb
    · exact Y.mul_mem hc hb
    · exact Y.mul_mem hb hc
    · exact Y.mul_mem ha hb
  obtain ⟨q₁, hq₁, q₂, hq₂, hw⟩ := dc_cert y hsy hy1 hy2
  have hwY : q₁ * y * q₂ ∈ Y := Y.mul_mem (Y.mul_mem (hQ q₁ hq₁) hy) (hQ q₂ hq₂)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := three_cycle_words
  simp only [WA6list, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h | h | h | h | h | h <;> rw [h] at hwY
  · refine ⟨_, hwY, ?_⟩
    rw [c1]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  · refine ⟨_, Y.mul_mem (Y.mul_mem ha hb) hwY, ?_⟩
    rw [c2]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  · refine ⟨_, Y.mul_mem (Y.mul_mem ha hb) hwY, ?_⟩
    rw [c3]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  · refine ⟨_, Y.mul_mem (Y.mul_mem (Y.mul_mem ha hc) hwY) hwY, ?_⟩
    rw [c4]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  · refine ⟨_, Y.mul_mem (Y.mul_mem (Y.mul_mem ha hc) hwY) hwY, ?_⟩
    rw [c5]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  · refine ⟨_, Y.mul_mem (Y.mul_mem (Y.mul_mem hb hwY) hc) hwY, ?_⟩
    rw [c6]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem overgroup_A6 (Y : Subgroup (Perm (Fin 6))) (hYA : Y ≤ alternatingGroup (Fin 6))
    (ha : ga ∈ Y) (hb : gb ∈ Y) (hc : gc ∈ Y) :
    (∀ y ∈ Y, InP1 y) ∨ (∀ y ∈ Y, InP2 y) ∨ Y = alternatingGroup (Fin 6) := by
  by_cases hP1 : ∀ y ∈ Y, InP1 y
  · exact Or.inl hP1
  by_cases hP2 : ∀ y ∈ Y, InP2 y
  · exact Or.inr (Or.inl hP2)
  have hprim := isPreprimitive_of ha hb hc hP1 hP2
  obtain ⟨y, hy, hy1, hy2⟩ : ∃ y ∈ Y, ¬ InP1 y ∧ ¬ InP2 y := by
    push Not at hP1 hP2
    obtain ⟨y₁, hy₁, h₁⟩ := hP1
    obtain ⟨y₂, hy₂, h₂⟩ := hP2
    by_cases h12 : InP2 y₁
    · by_cases h21 : InP1 y₂
      · refine ⟨y₁ * y₂, Y.mul_mem hy₁ hy₂, fun h => h₁ ?_, fun h => h₂ ?_⟩
        · have := P1sub.mul_mem (show y₁ * y₂ ∈ P1sub from h) (P1sub.inv_mem
            (show y₂ ∈ P1sub from h21))
          rwa [mul_inv_cancel_right] at this
        · have := P2sub.mul_mem (P2sub.inv_mem (show y₁ ∈ P2sub from h12))
            (show y₁ * y₂ ∈ P2sub from h)
          rwa [inv_mul_cancel_left] at this
      · exact ⟨y₂, hy₂, h21, h₂⟩
    · exact ⟨y₁, hy₁, h₁, h12⟩
  have hsy : Equiv.Perm.sign y = 1 := Equiv.Perm.mem_alternatingGroup.1 (hYA hy)
  obtain ⟨g, hg, h3⟩ := exists_isThreeCycle ha hb hc hy hsy hy1 hy2
  exact Or.inr (Or.inr (le_antisymm hYA
    (Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hg)))

end CFSG.Quasithin.H13.A6
