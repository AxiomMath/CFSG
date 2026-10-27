module

public import CFSG.Monster.B.TwoA.Fischer.AffineCayleyGraph

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

omit hS in
theorem ncard_inter_biUnion_hexadFiber {C : Set V}
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    (h77 : (cliqueBlocks lab C).ncard = 77) {P : Set V} (hP : P.Finite) {c : ℕ}
    (hc : ∀ B ∈ cliqueBlocks lab C, (P ∩ hexadFiber lab Y C B).ncard = c) :
    (P ∩ ⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B).ncard = 77 * c := by
  classical
  set Q := P ∩ ⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B with hQdef
  have hQfin : Q.Finite := hP.subset Set.inter_subset_left
  have hℬfin : (cliqueBlocks lab C).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [h77]; norm_num)
  have hmaps : Set.MapsTo (fun x => C ∩ (sliceGraph lab Y).neighborSet x) hQfin.toFinset
      hℬfin.toFinset := by
    intro x hx
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hx ⊢
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hx.2
    change C ∩ (sliceGraph lab Y).neighborSet x ∈ cliqueBlocks lab C
    rw [hxB.2.2]
    exact hB
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ B ∈ hℬfin.toFinset,
      {x ∈ hQfin.toFinset | C ∩ (sliceGraph lab Y).neighborSet x = B}.card = c := by
    intro B hB
    rw [Set.Finite.mem_toFinset] at hB
    rw [← hc B hB, ← Set.ncard_coe_finset]
    congr 1
    ext x
    rw [Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hxP, hxU⟩, hxB⟩
      obtain ⟨B', -, hxB'⟩ := Set.mem_iUnion₂.1 hxU
      exact ⟨hxP, hxB'.1, hxB'.2.1, hxB⟩
    · rintro ⟨hxP, hx⟩
      exact ⟨⟨hxP, Set.mem_iUnion₂.2 ⟨B, hB, hx⟩⟩, hx.2.2⟩
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hℬfin, h77] at h
  rw [Set.ncard_eq_toFinset_card _ hQfin, h]

section Max

variable {C : Set V} (hC : IsSliceMaxClique lab Y C)
  [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
include hC

theorem neighborSet_inter_omega_eq {x : V} (hx : x ∈ hexadFiber lab Y C ∅) :
    (sliceGraph lab Y).neighborSet x ∩ hexadFiber lab Y C ∅ =
      (fun r => act r x) '' labelLayer lab C 2 := by
  ext y
  constructor
  · rintro ⟨hxy, hy⟩
    obtain ⟨r, ⟨hr, rfl⟩, -⟩ := hS.existsUnique_act_eq hC hx hy
    exact ⟨r, (hS.adj_iff_mem_labelLayer_two hC hx hr).1 hxy, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    have hrR := hS.labelLayer_subset hC 2 hr
    exact ⟨(hS.adj_iff_mem_labelLayer_two hC hx hrR).2 hr, hS.act_mem_hexadFiber hrR hx⟩

theorem ncard_image_labelLayer {x : V} (hx : x ∈ hexadFiber lab Y C ∅) (i : ℕ) :
    ((fun r => act r x) '' labelLayer lab C i).ncard = (labelLayer lab C i).ncard :=
  Set.InjOn.ncard_image ((hS.act_injOn hC hx).mono (hS.labelLayer_subset hC i))

theorem exists_fix_image_block {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {B B' : Set V}
    (hB : B ∈ cliqueBlocks lab C) (hB' : B' ∈ cliqueBlocks lab C) :
    ∃ k ∈ setStab act lab Y C ⊓ actStab act x, act k '' B = B' := by
  obtain ⟨_, -, -, -, -, -, hB6, hSt, -⟩ := hS.clique_code_steiner_design hC
  obtain ⟨T, hTB, hT3⟩ := Set.exists_subset_card_eq (s := B) (n := 3)
    (by rw [(hB6 B hB).2]; norm_num)
  obtain ⟨T', hT'B', hT'3⟩ := Set.exists_subset_card_eq (s := B') (n := 3)
    (by rw [(hB6 B' hB').2]; norm_num)
  obtain ⟨k, hk, hkT⟩ := hS.exists_fix_image_eq hC hx (hTB.trans (hB6 B hB).1)
    (hT'B'.trans (hB6 B' hB').1) (by rw [hT3, hT'3]) (by rw [hT3])
  refine ⟨k, hk, ?_⟩
  have hkB : act k '' B ∈ cliqueBlocks lab C :=
    image_mem_cliqueBlocks hS.lab_act (fun z hz => (hk.1.2 z).2 hz)
      (setStabPerm act lab Y C ⟨k, hk.1⟩) (fun _ => rfl) hB
  obtain ⟨B₀, -, huniq⟩ := hSt T' (hT'B'.trans (hB6 B' hB').1) hT'3
  rw [huniq _ ⟨hkB, by rw [← hkT]; exact Set.image_mono hTB⟩, huniq B' ⟨hB', hT'B'⟩]

theorem ncard_neighborSet_inter_hexadFiber {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {B : Set V}
    (hB : B ∈ cliqueBlocks lab C) :
    ((sliceGraph lab Y).neighborSet x ∩ hexadFiber lab Y C B).ncard = 6 := by
  obtain ⟨_, -, -, hcov, -, -, hdUΩ, -, -, -, -, -, -⟩ := hS.clique_hexad_fibers hC
  obtain ⟨_, -, -, -, -, -, -, -, h77, -⟩ := hS.clique_code_steiner_design hC
  set N := (sliceGraph lab Y).neighborSet x with hN
  have hNfin : N.Finite := hS.finite.subset fun _ h => h.2.1
  have hconst : ∀ B' ∈ cliqueBlocks lab C,
      (N ∩ hexadFiber lab Y C B').ncard = (N ∩ hexadFiber lab Y C B).ncard := by
    intro B' hB'
    obtain ⟨k, hk, hkB⟩ := hS.exists_fix_image_block hC hx hB hB'
    have hkx : act k x = x := hk.2
    have e : act k '' (N ∩ hexadFiber lab Y C B) = N ∩ hexadFiber lab Y C B' := by
      rw [Set.image_inter (act k).injective, hN, hS.image_neighborSet hk.1.1, hkx,
        hS.image_hexadFiber hk.1 B, hkB]
    rw [← e, Set.ncard_image_of_injective _ (act k).injective]
  have hU := ncard_inter_biUnion_hexadFiber (Y := Y) h77 hNfin hconst
  have hNC : ∀ y ∈ N, y ∉ C := fun y hy hyC => by
    have h : y ∈ C ∩ (sliceGraph lab Y).neighborSet x := ⟨hyC, hy⟩
    rw [hx.2.2] at h
    exact h
  have hsplit : N = (N ∩ ⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B) ∪
      (N ∩ hexadFiber lab Y C ∅) := by
    ext y
    constructor
    · intro hy
      have hyY : y ∈ Y := hy.2.1
      rw [hcov] at hyY
      rcases hyY with (h | h) | h
      · exact absurd h (hNC y hy)
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have h693 := hS.valency x hx.1
  rw [← hN, hsplit, Set.ncard_union_eq
    (Disjoint.mono Set.inter_subset_right Set.inter_subset_right hdUΩ)
    (hNfin.subset Set.inter_subset_left) (hNfin.subset Set.inter_subset_left), hU,
    hS.neighborSet_inter_omega_eq hC hx, hS.ncard_image_labelLayer hC hx,
    hS.ncard_labelLayer_two hC] at h693
  omega

theorem ncard_neighborSet_inter_omega {B : Set V} (hB : B ∈ cliqueBlocks lab C) {y : V}
    (hy : y ∈ hexadFiber lab Y C B) :
    ((sliceGraph lab Y).neighborSet y ∩ hexadFiber lab Y C ∅).ncard = 192 := by
  classical
  obtain ⟨_, -, hfibB, -, -, -, -, -, -, -, hΩ, -, -⟩ := hS.clique_hexad_fibers hC
  obtain ⟨h32, -, htrans, -, -⟩ := hfibB B hB
  have hΩfin : (hexadFiber lab Y C ∅).Finite := hS.finite.subset fun _ h => h.1
  have hXfin : (hexadFiber lab Y C B).Finite := hS.finite.subset fun _ h => h.1
  have hconst : ∀ y' ∈ hexadFiber lab Y C B,
      ((sliceGraph lab Y).neighborSet y' ∩ hexadFiber lab Y C ∅).ncard =
        ((sliceGraph lab Y).neighborSet y ∩ hexadFiber lab Y C ∅).ncard := by
    intro y' hy'
    obtain ⟨r, hr, hry⟩ := htrans y hy y' hy'
    have hΩr : act r '' hexadFiber lab Y C ∅ = hexadFiber lab Y C ∅ := by
      rw [hS.image_hexadFiber (ptStab_le_setStab C hr) ∅, Set.image_empty]
    have e : act r '' ((sliceGraph lab Y).neighborSet y ∩ hexadFiber lab Y C ∅) =
        (sliceGraph lab Y).neighborSet y' ∩ hexadFiber lab Y C ∅ := by
      rw [Set.image_inter (act r).injective, hS.image_neighborSet hr.1, hΩr, hry]
    rw [← e, Set.ncard_image_of_injective _ (act r).injective]
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (sliceGraph lab Y).Adj (s := hΩfin.toFinset) (t := hXfin.toFinset)
  have h1 : ∀ w ∈ hΩfin.toFinset,
      (Finset.bipartiteAbove (sliceGraph lab Y).Adj hXfin.toFinset w).card = 6 := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    rw [← hS.ncard_neighborSet_inter_hexadFiber hC hw hB, ← Set.ncard_coe_finset]
    congr 1
    ext z
    rw [Finset.mem_coe, Finset.mem_bipartiteAbove, Set.Finite.mem_toFinset]
    exact and_comm
  have h2 : ∀ z ∈ hXfin.toFinset,
      (Finset.bipartiteBelow (sliceGraph lab Y).Adj hΩfin.toFinset z).card =
        ((sliceGraph lab Y).neighborSet y ∩ hexadFiber lab Y C ∅).ncard := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    rw [← hconst z hz, ← Set.ncard_coe_finset]
    congr 1
    ext w
    rw [Finset.mem_coe, Finset.mem_bipartiteBelow, Set.Finite.mem_toFinset]
    exact ⟨fun h => ⟨(sliceGraph lab Y).adj_symm h.2, h.1⟩,
      fun h => ⟨h.2, (sliceGraph lab Y).adj_symm h.1⟩⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hΩfin,
    ← Set.ncard_eq_toFinset_card _ hXfin, hΩ, h32] at key
  omega

end Max

theorem affine_orbit_cayley_graph {C : Set V} (hC : IsSliceMaxClique lab Y C) {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) :
    ∃ _ : CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C)),
      ptStab act lab Y C = labelLayer lab C 0 ∪ labelLayer lab C 1 ∪ labelLayer lab C 2 ∪
        labelLayer lab C 3 ∧
      labelLayer lab C 0 = {1} ∧ labelLayer lab C 1 = lab '' C ∧
      labelLayer lab C 2 = {r | ∃ a ∈ C, ∃ b ∈ C, a ≠ b ∧ r = lab a * lab b} ∧
      hexadFiber lab Y C ∅ = ⋃ i < 4, (fun r => act r x) '' labelLayer lab C i ∧
      ((fun r => act r x) '' labelLayer lab C 0).ncard = 1 ∧
      ((fun r => act r x) '' labelLayer lab C 1).ncard = 22 ∧
      ((fun r => act r x) '' labelLayer lab C 2).ncard = 231 ∧
      ((fun r => act r x) '' labelLayer lab C 3).ncard = 770 ∧
      (∀ y ∈ hexadFiber lab Y C ∅, ∀ y' ∈ hexadFiber lab Y C ∅,
        (∃ k ∈ setStab act lab Y C ⊓ actStab act x, act k y = y') ↔
          ∃ i < 4, y ∈ (fun r => act r x) '' labelLayer lab C i ∧
            y' ∈ (fun r => act r x) '' labelLayer lab C i) ∧
      (∀ r ∈ ptStab act lab Y C, ∀ s ∈ ptStab act lab Y C,
        (sliceGraph lab Y).Adj (act r x) (act s x) ↔ r * s ∈ labelLayer lab C 2) ∧
      (∀ B ∈ cliqueBlocks lab C,
        ((sliceGraph lab Y).neighborSet x ∩ hexadFiber lab Y C B).ncard = 6) ∧
      (∀ B ∈ cliqueBlocks lab C, ∀ y ∈ hexadFiber lab Y C B,
        ((sliceGraph lab Y).neighborSet y ∩ hexadFiber lab Y C ∅).ncard = 192) ∧
      (∀ k ∈ setStab act lab Y C ⊓ actStab act x, Commute (lab x) k) ∧
      (∀ a ∈ C, act (lab x) a = act (lab a) x ∧ act (lab x) (act (lab a) x) = a) ∧
      act (lab x) x = x ∧
      (∀ r ∈ labelLayer lab C 2, act (lab x) (act r x) = act r x) ∧
      (∀ r ∈ labelLayer lab C 3, act (lab x) (act r x) ≠ act r x) ∧
      act (lab x) '' C = (fun a => act (lab a) x) '' C ∧
      act (lab x) '' C ⊆ hexadFiber lab Y C ∅ ∧
      IsSliceMaxClique lab Y (act (lab x) '' C) ∧ (act (lab x) '' C).ncard = 22 := by
  have inst : CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C)) :=
    hS.isElementaryAbelian_closure hC.1.1 hC.1.2
  refine ⟨inst, hS.ptStab_eq_union_labelLayer hC, labelLayer_zero, hS.labelLayer_one hC,
    hS.labelLayer_two hC, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr s hs => hS.adj_act_act_iff hC hx hr hs,
    fun B hB => hS.ncard_neighborSet_inter_hexadFiber hC hx hB,
    fun B hB y hy => hS.ncard_neighborSet_inter_omega hC hB hy,
    fun k hk => hS.commute_lab_of_act_eq hk.2,
    fun a ha => ⟨hS.act_lab_eq_act_lab hC hx ha, hS.act_lab_act_lab hC hx ha⟩,
    (hS.act_lab_eq_iff hx.1 hx.1).2 (Commute.refl _),
    fun r hr => hS.act_lab_eq_of_mem_labelLayer_two hC hx hr,
    fun r hr => hS.act_lab_ne_of_mem_labelLayer_three hC hx hr,
    Set.image_congr fun a ha => hS.act_lab_eq_act_lab hC hx ha, ?_,
    hS.isSliceMaxClique_image (lab_mem_sliceGroup hx.1) hC, ?_⟩
  · ext y
    rw [Set.mem_iUnion₂]
    constructor
    · intro hy
      obtain ⟨r, ⟨hr, rfl⟩, -⟩ := hS.existsUnique_act_eq hC hx hy
      obtain ⟨i, hi, hri⟩ := hS.exists_mem_labelLayer hC hr
      exact ⟨i, by omega, r, hri, rfl⟩
    · rintro ⟨i, -, r, hr, rfl⟩
      exact hS.act_mem_hexadFiber (hS.labelLayer_subset hC i hr) hx
  · rw [hS.ncard_image_labelLayer hC hx, labelLayer_zero, Set.ncard_singleton]
  · rw [hS.ncard_image_labelLayer hC hx, hS.ncard_labelLayer_one hC]
  · rw [hS.ncard_image_labelLayer hC hx, hS.ncard_labelLayer_two hC]
  · rw [hS.ncard_image_labelLayer hC hx, hS.ncard_labelLayer_three hC]
  · intro y hy y' _
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨r, ⟨hr, rfl⟩, -⟩ := hS.existsUnique_act_eq hC hx hy
      obtain ⟨i, hi, hri⟩ := hS.exists_mem_labelLayer hC hr
      exact ⟨i, by omega, ⟨r, hri, rfl⟩, k * r * k⁻¹, conj_mem_labelLayer hS.lab_act hk.1 hri,
        (act_act_eq_conj hk.2 r).symm⟩
    · rintro ⟨i, hi, ⟨r, hr, rfl⟩, r', hr', rfl⟩
      obtain ⟨k, hk, hkr⟩ := hS.exists_conj_eq_of_mem_labelLayer hC hx (by omega) hr hr'
      exact ⟨k, hk, by rw [act_act_eq_conj hk.2, hkr]⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [hS.act_lab_eq_act_lab hC hx ha]
    exact hS.act_mem_hexadFiber
      (hS.closure_le_ptStab hC.1.1 hC.1.2 (Subgroup.subset_closure ⟨a, ha, rfl⟩)) hx
  · rw [Set.ncard_image_of_injective _ (act (lab x)).injective,
      hS.ncard_eq_of_isSliceMaxClique hC]

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
