module

public import CFSG.Timmesfeld.Special.Commutator

public section

open scoped commutatorElement

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def SpecialClosure (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → ∀ b ∈ rootSet D e, (d * b) ^ 2 ∈ rootSet D ((d * e) ^ 2)

section SpecialPair

variable {d e : G}

theorem SpecialClosure.mul_sq_mem_rootSet (hD : IsRootInvolutionSet D) (hs : SpecialClosure D)
    (hd : d ∈ D) (he : e ∈ D) (h4 : orderOf (d * e) = 4) {a b : G} (ha : a ∈ rootSet D d)
    (hb : b ∈ rootSet D e) : (a * b) ^ 2 ∈ rootSet D ((d * e) ^ 2) := by
  have h4ae : orderOf (a * e) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hd he ha (mem_rootSet_self he) h4
  have h4ed : orderOf (e * d) = 4 := by rwa [orderOf_mul_comm_eq]
  have h1 : (a * e) ^ 2 ∈ rootSet D ((d * e) ^ 2) := by
    rw [mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one ha.1) (hD.mul_self_eq_one he) h4ae,
      mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he) h4]
    exact hs e he d hd h4ed a ha
  rw [← rootSet_eq_of_mem h1]
  exact hs a ha.1 e he h4ae b hb

theorem exists_mul_sq_eq_of_forall_mem [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4)
    (h1 : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D e, (a * b) ^ 2 ∈ rootSet D ((d * e) ^ 2))
    {a c : G} (ha : a ∈ rootSet D d) (hcz : c ∈ rootSet D ((d * e) ^ 2)) :
    ∃ b ∈ rootSet D e, (a * b) ^ 2 = c := by
  have hz : (d * e) ^ 2 ∈ D := hD.sq_mem hd he h4
  have hsub : (fun b => (a * b) ^ 2) '' rootSet D e ⊆ rootSet D ((d * e) ^ 2) := by
    rintro _ ⟨b, hb, rfl⟩
    exact h1 a ha b hb
  have hcard : (rootSet D ((d * e) ^ 2)).ncard ≤ ((fun b => (a * b) ^ 2) '' rootSet D e).ncard := by
    rw [(mul_sq_injOn hclass hD hc hd he h4 ha).ncard_image, ncard_rootSet_eq hclass he hz]
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  rw [← heq] at hcz
  obtain ⟨b, hb, rfl⟩ := hcz
  exact ⟨b, hb, rfl⟩

theorem exists_mul_sq_eq_of_forall_mem' [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4)
    (h1 : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D e, (a * b) ^ 2 ∈ rootSet D ((d * e) ^ 2))
    {b c : G} (hb : b ∈ rootSet D e) (hcz : c ∈ rootSet D ((d * e) ^ 2)) :
    ∃ a ∈ rootSet D d, (a * b) ^ 2 = c := by
  have h4ed : orderOf (e * d) = 4 := by rwa [orderOf_mul_comm_eq]
  have hcomm : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D e, (a * b) ^ 2 = (b * a) ^ 2 := fun a ha b hb =>
    mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one ha.1) (hD.mul_self_eq_one hb.1)
      (orderOf_mul_eq_four_of_mem_rootSet hD hd he ha hb h4)
  have hz : (d * e) ^ 2 = (e * d) ^ 2 :=
    mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he) h4
  rw [hz] at h1 hcz
  obtain ⟨a, ha, rfl⟩ := exists_mul_sq_eq_of_forall_mem hclass hD hc he hd h4ed
    (fun b hb a ha => hcomm a ha b hb ▸ h1 a ha b hb) hb hcz
  exact ⟨a, ha, hcomm a ha b hb⟩

theorem SpecialClosure.rootSet_of_special [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hs : SpecialClosure D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    (∀ a ∈ rootSet D d, ∀ b ∈ rootSet D e, (a * b) ^ 2 ∈ rootSet D ((d * e) ^ 2)) ∧
    (∀ a ∈ rootSet D d, ∀ c ∈ rootSet D ((d * e) ^ 2), ∃ b ∈ rootSet D e, (a * b) ^ 2 = c) ∧
    (∀ b ∈ rootSet D e, ∀ c ∈ rootSet D ((d * e) ^ 2), ∃ a ∈ rootSet D d, (a * b) ^ 2 = c) := by
  have h1 : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D e, (a * b) ^ 2 ∈ rootSet D ((d * e) ^ 2) :=
    fun a ha b hb => hs.mul_sq_mem_rootSet hD hd he h4 ha hb
  exact ⟨h1, fun a ha c hcz => exists_mul_sq_eq_of_forall_mem hclass hD hc hd he h4 h1 ha hcz,
    fun b hb c hcz => exists_mul_sq_eq_of_forall_mem' hclass hD hc hd he h4 h1 hb hcz⟩

theorem special_pair_rootSet (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hd : d ∈ D) (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    (∀ a ∈ rootSet D d, ∀ b ∈ rootSet D e, (a * b) ^ 2 ∈ rootSet D ((d * e) ^ 2)) ∧
    (∀ a ∈ rootSet D d, ∀ c ∈ rootSet D ((d * e) ^ 2), ∃ b ∈ rootSet D e, (a * b) ^ 2 = c) ∧
    (∀ b ∈ rootSet D e, ∀ c ∈ rootSet D ((d * e) ^ 2), ∃ a ∈ rootSet D d, (a * b) ^ 2 = c) :=
  have := h.finite
  hs.rootSet_of_special h.isClass h.root hc hd he h4

theorem special_pair_central (h : Hyp G D) (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) :
    rootGroup D ((d * e) ^ 2) ≤ Subgroup.centralizer
      ((rootGroup D d ⊔ rootGroup D e ⊔ rootGroup D ((d * e) ^ 2) : Subgroup G) : Set G) :=
  rootGroup_sq_le_centralizer h.root hd he h4

theorem commutatorElement_mem_rootGroup_of_forall_mem (hD : IsRootInvolutionSet D)
    (hc : RootClosure D) (hd : d ∈ D) (he : e ∈ D)
    (h1 : ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D e, (a * b) ^ 2 ∈ rootSet D ((d * e) ^ 2))
    {g g' : G} (hg : g ∈ rootGroup D d) (hg' : g' ∈ rootGroup D e) :
    ⁅g, g'⁆ ∈ rootGroup D ((d * e) ^ 2) := by
  rcases (mem_rootGroup_iff_of_rootClosure hD hc hd).1 hg with rfl | hg
  · simp
  rcases (mem_rootGroup_iff_of_rootClosure hD hc he).1 hg' with rfl | hg'
  · simp
  rw [Special.commutatorElement_eq_mul_sq (hD.mul_self_eq_one hg.1) (hD.mul_self_eq_one hg'.1)]
  exact rootSet_subset_rootGroup _ _ (h1 g hg g' hg')

theorem commutator_rootGroup_eq [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hs : SpecialClosure D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    ⁅rootGroup D d, rootGroup D e⁆ = rootGroup D ((d * e) ^ 2) := by
  obtain ⟨h1, h2, -⟩ := hs.rootSet_of_special hclass hD hc hd he h4
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro g hg g' hg'
    exact commutatorElement_mem_rootGroup_of_forall_mem hD hc hd he h1 hg hg'
  · rw [rootGroup, Subgroup.closure_le]
    intro c hcz
    obtain ⟨b, hb, rfl⟩ := h2 d (mem_rootSet_self hd) c hcz
    rw [← Special.commutatorElement_eq_mul_sq (hD.mul_self_eq_one hd) (hD.mul_self_eq_one hb.1)]
    exact Subgroup.commutator_mem_commutator (rootSet_subset_rootGroup D d (mem_rootSet_self hd))
      (rootSet_subset_rootGroup D e hb)

theorem image_mul_sq_rootGroup_right [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hs : SpecialClosure D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) {a : G} (ha : a ∈ rootSet D d) :
    (fun g => (a * g) ^ 2) '' (rootGroup D e : Set G) = rootGroup D ((d * e) ^ 2) := by
  obtain ⟨h1, h2, -⟩ := hs.rootSet_of_special hclass hD hc hd he h4
  have ha2 : a * a = 1 := hD.mul_self_eq_one ha.1
  ext c
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases (mem_rootGroup_iff_of_rootClosure hD hc he).1 hg with rfl | hg
    · dsimp only
      rw [mul_one, pow_two a, ha2]
      exact (rootGroup D _).one_mem
    · exact rootSet_subset_rootGroup _ _ (h1 a ha g hg)
  · intro hcz
    rcases (mem_rootGroup_iff_of_rootClosure hD hc (hD.sq_mem hd he h4)).1 hcz with rfl | hcz
    · exact ⟨1, (rootGroup D e).one_mem, by dsimp only; rw [mul_one, pow_two a, ha2]⟩
    · obtain ⟨b, hb, rfl⟩ := h2 a ha c hcz
      exact ⟨b, rootSet_subset_rootGroup D e hb, rfl⟩

theorem image_mul_sq_rootGroup_left [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hs : SpecialClosure D) (hd : d ∈ D)
    (he : e ∈ D) (h4 : orderOf (d * e) = 4) {b : G} (hb : b ∈ rootSet D e) :
    (fun g => (g * b) ^ 2) '' (rootGroup D d : Set G) = rootGroup D ((d * e) ^ 2) := by
  obtain ⟨h1, -, h3⟩ := hs.rootSet_of_special hclass hD hc hd he h4
  have hb2 : b * b = 1 := hD.mul_self_eq_one hb.1
  ext c
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases (mem_rootGroup_iff_of_rootClosure hD hc hd).1 hg with rfl | hg
    · dsimp only
      rw [one_mul, pow_two b, hb2]
      exact (rootGroup D _).one_mem
    · exact rootSet_subset_rootGroup _ _ (h1 g hg b hb)
  · intro hcz
    rcases (mem_rootGroup_iff_of_rootClosure hD hc (hD.sq_mem hd he h4)).1 hcz with rfl | hcz
    · exact ⟨1, (rootGroup D d).one_mem, by dsimp only; rw [one_mul, pow_two b, hb2]⟩
    · obtain ⟨a, ha, rfl⟩ := h3 b hb c hcz
      exact ⟨a, rootSet_subset_rootGroup D d ha, rfl⟩

end SpecialPair

end CFSG.Timmesfeld
