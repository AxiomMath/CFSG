module

public import CFSG.Timmesfeld.ARS.Defs
public import CFSG.Timmesfeld.Opposite.Moufang
public import CFSG.Timmesfeld.Special.Gamma

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def rootClass (D : Set G) : Set (Subgroup G) := {A | ∃ d ∈ D, A = rootGroup D d}

@[expose] def RootMoufang (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) →
    ∀ a ∈ rootSet D d, ∃ b ∈ rootSet D c, orderOf (a * b) = 3

namespace Reduction

theorem not_commute_and_odd_of_orderOf_eq_three {a b : G} (h3 : orderOf (a * b) = 3)
    (ha : a * a = 1) (hb : b * b = 1) : ¬ Commute a b ∧ Odd (orderOf (a * b)) := by
  refine ⟨fun hab => ?_, by rw [h3]; decide⟩
  have h2 : (a * b) ^ 2 = 1 := by
    rw [sq, show a * b * (a * b) = a * a * (b * b) by
      rw [mul_assoc, ← mul_assoc b a b, ← hab.eq, mul_assoc, mul_assoc]]
    rw [ha, hb, mul_one]
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h3] at this
  exact absurd this (by decide)

theorem exists_conjSub_eq [Finite G] (h : Hyp G D) (hc : RootClosure D) (hm : RootMoufang D)
    {d c : G} (hd : d ∈ D) (hcD : c ∈ D) (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c)))
    {a : G} (ha : a ∈ rootGroup D d) (ha1 : a ≠ 1) :
    ∃ b ∈ rootGroup D c, b ≠ 1 ∧
      ARS.conjSub (rootGroup D d) b = ARS.conjSub (rootGroup D c) a := by
  have ha' : a ∈ rootSet D d :=
    ((mem_rootGroup_iff_of_rootClosure h.root hc hd).1 ha).resolve_left ha1
  obtain ⟨b, hb, h3⟩ := hm d hd c hcD hdc hodd a ha'
  have haD : a ∈ D := ha'.1
  have hbD : b ∈ D := hb.1
  obtain ⟨hab, hodd'⟩ :=
    not_commute_and_odd_of_orderOf_eq_three h3 (h.root.mul_self_eq_one haD)
      (h.root.mul_self_eq_one hbD)
  refine ⟨b, Subgroup.subset_closure hb, h.root.ne_one hbD, ?_⟩
  have key := (map_conj_rootGroup_eq_iff h.isClass h.root haD hbD hab hodd').2 h3
  rw [rootGroup_eq_of_mem ha', rootGroup_eq_of_mem hb] at key
  exact key

end Reduction

open Reduction in
theorem isRootClass_rootClass (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hm : RootMoufang D) : ARS.IsRootClass (rootClass D) := by
  have := h.finite
  obtain ⟨d₀, hD₀⟩ := h.isClass
  have hd₀ : d₀ ∈ D := by rw [hD₀]; exact IsConj.refl d₀
  refine ⟨⟨rootGroup D d₀, ?_⟩, ?_, ?_, ?_, ?_⟩
  · ext A
    constructor
    · rintro ⟨d, hd, rfl⟩
      have hconj : IsConj d₀ d := by rw [hD₀] at hd; exact hd
      obtain ⟨g, rfl⟩ := isConj_iff.1 hconj
      exact ⟨g, (rootGroup_conj h.isClass g d₀).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g * d₀ * g⁻¹, h.conj_mem g hd₀, (rootGroup_conj h.isClass g d₀).symm⟩
  · rintro A ⟨d, hd, rfl⟩ hA
    have hmem : d ∈ rootGroup D d := Subgroup.subset_closure (mem_rootSet_self hd)
    rw [hA, Subgroup.mem_bot] at hmem
    exact h.root.ne_one hd hmem
  · rintro A ⟨d, hd, rfl⟩ a ha
    exact mul_self_eq_one_of_mem_rootGroup h.root hd ha
  · rintro A ⟨d, hd, rfl⟩ B ⟨e, he, rfl⟩ hAB
    rcases commute_or_orderOf_mul_eq_four_or_odd h.root hd he with hde | h4 | ⟨hodd, hde⟩
    · exact .inl fun a ha b hb => commute_of_mem_rootGroup_of_commute' he ha hb hde
    · refine .inr (.inr ⟨?_, ?_, ?_⟩)
      · rw [commutator_rootGroup_eq h.isClass h.root hc hs hd he h4]
        exact ⟨(d * e) ^ 2, h.root.sq_mem hd he h4, rfl⟩
      · rw [commutator_rootGroup_eq h.isClass h.root hc hs hd he h4]
        intro x hx a ha
        exact (Subgroup.mem_centralizer_iff.1 (special_pair_central h hd he h4 hx) a
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))).symm
      · rw [commutator_rootGroup_eq h.isClass h.root hc hs hd he h4]
        intro x hx b hb
        exact (Subgroup.mem_centralizer_iff.1 (special_pair_central h hd he h4 hx) b
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))).symm
    · refine .inr (.inl ⟨hAB, fun a ha ha1 => ?_, fun b hb hb1 => ?_⟩)
      · exact exists_conjSub_eq h hc hm hd he hde hodd ha ha1
      · have hodd' : Odd (orderOf (e * d)) := by rwa [orderOf_mul_comm_eq]
        exact exists_conjSub_eq h hc hm he hd (fun h' => hde h'.symm) hodd' hb hb1
  · refine eq_top_iff.2 ?_
    rw [← h.gen, Subgroup.closure_le]
    intro x hx
    exact (le_iSup₂ (f := fun A (_ : A ∈ rootClass D) => A) (rootGroup D x) ⟨x, hx, rfl⟩)
      (Subgroup.subset_closure (mem_rootSet_self hx))

theorem isNondegenerate_rootClass (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D) :
    ARS.IsNondegenerate (rootClass D) := by
  have := h.finite
  obtain ⟨d, hd, e, he, h4⟩ := h.nondeg
  refine ⟨rootGroup D d, ⟨d, hd, rfl⟩, rootGroup D e, ⟨e, he, rfl⟩, ?_, ?_, ?_⟩
  · rw [commutator_rootGroup_eq h.isClass h.root hc hs hd he h4]
    exact ⟨(d * e) ^ 2, h.root.sq_mem hd he h4, rfl⟩
  · rw [commutator_rootGroup_eq h.isClass h.root hc hs hd he h4]
    intro x hx a ha
    exact (Subgroup.mem_centralizer_iff.1 (special_pair_central h hd he h4 hx) a
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))).symm
  · rw [commutator_rootGroup_eq h.isClass h.root hc hs hd he h4]
    intro x hx b hb
    exact (Subgroup.mem_centralizer_iff.1 (special_pair_central h hd he h4 hx) b
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))).symm

theorem arsHyp_rootClass (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hm : RootMoufang D) : ARS.Hyp G (rootClass D) where
  finite := h.finite
  root := isRootClass_rootClass h hc hs hm
  nondeg := isNondegenerate_rootClass h hc hs
  center := h.center_eq_bot
  twoCore := h.twoCore

end CFSG.Timmesfeld
