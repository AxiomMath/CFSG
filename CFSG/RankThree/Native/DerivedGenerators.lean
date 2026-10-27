module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.RankThree.Native

open scoped commutatorElement

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

section Derived

variable {G : Type*} [Group G] [Finite G]

theorem closure_le_normalizer_closure {S T : Set G}
    (hnorm : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ Subgroup.closure T) :
    Subgroup.closure S ≤ Subgroup.normalizer (Subgroup.closure T : Set G) := by
  rw [Subgroup.closure_le]
  intro s hs
  apply Subgroup.mem_normalizer_fintype
  intro m hm
  induction hm using Subgroup.closure_induction with
  | mem t ht => exact hnorm s hs t ht
  | one => simp
  | mul a b _ _ ha hb =>
    have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
    rw [e]
    exact (Subgroup.closure T).mul_mem ha hb
  | inv a _ ha =>
    have e : s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.closure T).inv_mem ha

theorem commutator_closure_eq_closure {S T : Set G}
    (hT : T ⊆ ((⁅Subgroup.closure S, Subgroup.closure S⁆ : Subgroup G) : Set G))
    (hnorm : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ Subgroup.closure T)
    (hcomm : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ Subgroup.closure T) :
    ⁅Subgroup.closure S, Subgroup.closure S⁆ = Subgroup.closure T := by
  set H := Subgroup.closure S
  set N := Subgroup.closure T
  have hgen : ∀ s ∈ S, s ∈ Subgroup.normalizer (N : Set G) := by
    intro s hs
    apply Subgroup.mem_normalizer_fintype
    intro m hm
    induction hm using Subgroup.closure_induction with
    | mem t ht => exact hnorm s hs t ht
    | one => simp
    | mul a b _ _ ha hb =>
      have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
      rw [e]
      exact N.mul_mem ha hb
    | inv a _ ha =>
      have e : s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
      rw [e]
      exact N.inv_mem ha
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := (Subgroup.closure_le _).2 hgen
  have hconj : ∀ g ∈ H, ∀ m ∈ N, g * m * g⁻¹ ∈ N := fun g hg m hm =>
    (Subgroup.mem_normalizer_iff.1 (hHN hg) m).1 hm
  have hgenH : ∀ s ∈ S, ∀ h ∈ H, ⁅s, h⁆ ∈ N := by
    intro s hs h hh
    induction hh using Subgroup.closure_induction with
    | mem s' hs' => exact hcomm s hs s' hs'
    | one => simp
    | mul a b ha hb iha ihb =>
      have e : ⁅s, a * b⁆ = ⁅s, a⁆ * (a * ⁅s, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem iha (hconj a ha _ ihb)
    | inv a ha iha =>
      have e : ⁅s, a⁻¹⁆ = a⁻¹ * ⁅s, a⁆⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj a⁻¹ (H.inv_mem ha) _ (N.inv_mem iha)
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg h hh
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact hgenH s hs h hh
    | one => simp
    | mul a b ha hb iha ihb =>
      have e : ⁅a * b, h⁆ = a * ⁅b, h⁆ * a⁻¹ * ⁅a, h⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem (hconj a ha _ ihb) iha
    | inv a ha iha =>
      have e : ⁅a⁻¹, h⁆ = a⁻¹ * ⁅a, h⁆⁻¹ * a⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj a⁻¹ (H.inv_mem ha) _ (N.inv_mem iha)
  · exact (Subgroup.closure_le _).2 hT

end Derived

section Simple

variable {α : Type*} [DecidableEq α]

theorem isSimpleGroup_of_faithful_five {D : Subgroup (Equiv.Perm α)} (O : Finset α)
    (hO : O.card = 5) (hpres : ∀ g ∈ D, ∀ p ∈ O, g p ∈ O)
    (hfaith : ∀ g ∈ D, (∀ p ∈ O, g p = p) → g = 1) (hcard : Nat.card D = 60) :
    IsSimpleGroup D := by
  have hiff : ∀ g : D, ∀ p : α, (g : Equiv.Perm α) p ∈ O ↔ p ∈ O := by
    intro g p
    refine ⟨fun h => ?_, fun h => hpres g g.2 p h⟩
    have := hpres (g : Equiv.Perm α)⁻¹ (D.inv_mem g.2) _ h
    simpa using this
  let ρ : D →* Equiv.Perm {p // p ∈ O} :=
    { toFun := fun g => (g : Equiv.Perm α).subtypePerm (hiff g)
      map_one' := rfl
      map_mul' := fun g h => by
        rw [Equiv.Perm.subtypePerm_mul]
        rfl }
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply hfaith g g.2
    intro p hp
    exact congrArg (fun σ : Equiv.Perm {p // p ∈ O} => (σ ⟨p, hp⟩ : α)) hg
  have hcardO : Nat.card {p // p ∈ O} = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hO]
  have hrange : ρ.range = alternatingGroup {p // p ∈ O} := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have h1 := ρ.range.index_mul_card
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, hcard,
      Nat.card_perm, hcardO] at h1
    have h2 : ρ.range.index * 60 = 2 * 60 := by
      rw [h1]
      rfl
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hsimple : IsSimpleGroup (alternatingGroup {p // p ∈ O}) :=
    alternatingGroup.isSimpleGroup (by rw [hcardO])
  have e : D ≃* alternatingGroup {p // p ∈ O} :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact (MulEquiv.isSimpleGroup_congr e).2 hsimple

theorem isSimpleGroup_of_conj_closure {G : Type*} [Group G] {D : Subgroup G}
    (hnt : ∃ g ∈ D, g ≠ 1)
    (hgen : ∀ e ∈ D, e ≠ 1 → D ≤ Subgroup.closure {y | ∃ g ∈ D, g * e * g⁻¹ = y}) :
    IsSimpleGroup D where
  exists_pair_ne := by
    obtain ⟨g, hg, hg1⟩ := hnt
    exact ⟨⟨g, hg⟩, 1, fun h => hg1 (congrArg Subtype.val h)⟩
  eq_bot_or_eq_top_of_normal N hN := by
    by_cases hbot : N = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
      have he1 : ((a : D) : G) ≠ 1 := fun h => ha1 (Subtype.ext (Subtype.ext h))
      have hle : Subgroup.closure {y | ∃ g ∈ D, g * ((a : D) : G) * g⁻¹ = y} ≤
          N.map D.subtype := by
        rw [Subgroup.closure_le]
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨⟨g, hg⟩ * (a : D) * ⟨g, hg⟩⁻¹, hN.conj_mem _ a.2 _, rfl⟩
      rw [eq_top_iff]
      intro d _
      obtain ⟨d', hd', he⟩ := hle (hgen _ (a : D).2 he1 d.2)
      have : d' = d := Subtype.ext he
      rw [← this]
      exact hd'

end Simple

end CFSG.RankThree.Native
