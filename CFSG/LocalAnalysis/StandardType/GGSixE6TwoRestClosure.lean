module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoJEq
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.EvenOddRadical

private abbrev V := Fin Tag.E6.rank → ℤ

private theorem e6rc_pinnedX_conj_of_isRoot
    {α β : V} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (hne : α ≠ β) (hne' : α ≠ -β) (hadd : IsRoot .E6 (α + β)) :
    pinnedX .E6 F2 α 1 * pinnedX .E6 F2 β 1 * (pinnedX .E6 F2 α 1)⁻¹ =
      pinnedX .E6 F2 (α + β) 1 * pinnedX .E6 F2 β 1 := by
  simpa only [mul_one] using pinnedX_conj_of_isRoot (τ := .E6) (Or.inr (Or.inl rfl)) (gf2_two)
    hα hβ hne hne' hadd (1 : F2) 1

private theorem e6rc_xr_conj_of_isRoot
    {α β : V} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (hne : α ≠ β) (hne' : α ≠ -β) (hadd : IsRoot .E6 (α + β)) :
    xr α * xr β * (xr α)⁻¹ = xr (α + β) * xr β := by
  apply Subtype.ext
  simp only [xr, Subgroup.coe_mul, Subgroup.coe_inv]
  exact e6rc_pinnedX_conj_of_isRoot hα hβ hne hne' hadd

private theorem e6rc_xr_mem_add
    {γ δ : V} (hγ : IsRoot .E6 γ) (hδ : IsRoot .E6 δ)
    (hne : γ ≠ δ) (hne' : γ ≠ -δ) (hadd : IsRoot .E6 (γ + δ))
    {H : Subgroup EC} (hγH : xr γ ∈ H) (hδH : xr δ ∈ H) : xr (γ + δ) ∈ H := by
  have hcomm : xr γ * xr δ * (xr γ)⁻¹ * (xr δ)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hγH hδH) (H.inv_mem hγH)) (H.inv_mem hδH)
  have heq : xr γ * xr δ * (xr γ)⁻¹ * (xr δ)⁻¹ = xr (γ + δ) := by
    rw [e6rc_xr_conj_of_isRoot hγ hδ hne hne' hadd]
    group
  rwa [heq] at hcomm

private theorem e6rc_f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  have hcard : Nat.card F2 = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  by_cases hz : a = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq a hz).trans (huniq 1 one_ne_zero).symm)

private theorem e6rc_xr_mem_rootSpan_subgroupOf
    {S : Set V} {β : V} (hβ : β ∈ S) :
    xr β ∈ (rootSpan .E6 F2 S).subgroupOf (adjointGroup .E6 F2) := by
  rw [Subgroup.mem_subgroupOf]
  exact pinnedX_mem_rootSpan hβ 1

private theorem e6rc_eq_top_of_forall_xr
    (H : Subgroup EC)
    (h : ∀ β, IsRoot .E6 β → xr β ∈ H) : H = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  let f : EC →* ModGL .E6 F2 := Subgroup.subtype (adjointGroup .E6 F2)
  have hxroot : (x : ModGL .E6 F2) ∈ rootSpan .E6 F2 {α | IsRoot .E6 α} := by
    rw [← adjointGroup_eq_rootSpan]
    exact x.property
  have hle : rootSpan .E6 F2 {α | IsRoot .E6 α} ≤ H.map f := by
    refine iSup₂_le ?_
    intro α hα
    rw [rootSubgroup]
    rw [Subgroup.closure_le]
    rintro g ⟨c, rfl⟩
    rcases e6rc_f2_cases c with rfl | rfl
    · rw [pinnedX_zero]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_map_of_mem f (h α hα)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle hxroot)
  have hyx' : y = x := Subtype.ext hyx
  simpa [hyx'] using hy

private theorem e6rc_pinnedX_conj_of_not
    {α β : V} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (hne : α ≠ β) (hne' : α ≠ -β) (h : ¬ IsRoot .E6 (α + β)) :
    pinnedX .E6 F2 α 1 * pinnedX .E6 F2 β 1 * (pinnedX .E6 F2 α 1)⁻¹ =
      pinnedX .E6 F2 β 1 := by
  simpa using pinnedX_conj_of_not (τ := .E6) (Or.inr (Or.inl rfl)) hα hβ hne hne' h (1 : F2) 1

private theorem e6rc_xr_conj_of_not
    {α β : V} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β)
    (hne : α ≠ β) (hne' : α ≠ -β) (h : ¬ IsRoot .E6 (α + β)) :
    xr α * xr β * (xr α)⁻¹ = xr β := by
  apply Subtype.ext
  simp only [xr, Subgroup.coe_mul, Subgroup.coe_inv]
  exact e6rc_pinnedX_conj_of_not hα hβ hne hne' h

private def e6rc_a : V := a5Root 0 4

private def e6rc_b : V := a5Root 1 5

private def e6rc_level (k : ℤ) : Finset V :=
  (rootFinset .E6).filter (fun r => iform r lamE = k)

private def e6rc_step (S : Finset V) : Finset V :=
  S ∪ ((rootFinset .E6).filter (fun r => ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ x ≠ -y ∧ x + y = r))

private theorem e6rc_step_subset_rootFinset {S : Finset V} (hS : S ⊆ rootFinset .E6) :
    e6rc_step S ⊆ rootFinset .E6 := by
  intro r hr
  rcases Finset.mem_union.mp hr with h | h
  · exact hS h
  · exact (Finset.mem_filter.mp h).1

private theorem e6rc_xr_mem_step
    {S : Finset V} (hS : S ⊆ rootFinset .E6) {H : Subgroup EC}
    (hH : ∀ r ∈ S, xr r ∈ H) : ∀ r ∈ e6rc_step S, xr r ∈ H := by
  intro r hr
  rcases Finset.mem_union.mp hr with h | h
  · exact hH r h
  · obtain ⟨hrroot, x, hx, y, hy, hxy, hxy', hsum⟩ := Finset.mem_filter.mp h
    have hrroot2 : x + y ∈ rootFinset .E6 := by rw [← hsum] at hrroot; exact hrroot
    rw [← hsum]
    exact e6rc_xr_mem_add (mem_rootFinset.mp (hS hx)) (mem_rootFinset.mp (hS hy))
      hxy hxy' (mem_rootFinset.mp hrroot2) (hH x hx) (hH y hy)

private theorem e6rc_xr_mem_iter
    {S₀ : Finset V} (hS₀ : S₀ ⊆ rootFinset .E6) {H : Subgroup EC}
    (hH₀ : ∀ r ∈ S₀, xr r ∈ H) :
    ∀ n, (∀ r ∈ (e6rc_step^[n]) S₀, xr r ∈ H) ∧
      ((e6rc_step^[n]) S₀ ⊆ rootFinset .E6) := by
  intro n
  induction n with
  | zero => exact ⟨hH₀, hS₀⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨e6rc_xr_mem_step ih.2 ih.1, e6rc_step_subset_rootFinset ih.2⟩

private theorem e6rc_all_xr_of_iter
    {S₀ : Finset V} (hS₀ : S₀ ⊆ rootFinset .E6) {H : Subgroup EC}
    (hH₀ : ∀ r ∈ S₀, xr r ∈ H) {N : ℕ}
    (hN : ∀ r ∈ rootFinset .E6, r ∈ (e6rc_step^[N]) S₀) :
    ∀ β, IsRoot .E6 β → xr β ∈ H := by
  intro β hβ
  exact (e6rc_xr_mem_iter hS₀ hH₀ N).1 β (hN β (mem_rootFinset.mpr hβ))

private theorem e6rc_isRoot_neg_a : IsRoot .E6 (-e6rc_a) :=
  mem_rootFinset.mp (by
    rw [e6rc_a, ← show a5Root 4 0 = -(a5Root 0 4) by decide]
    exact a5Root_check 4 0 (by decide))

private theorem e6rc_isRoot_neg_b : IsRoot .E6 (-e6rc_b) :=
  mem_rootFinset.mp (by
    rw [e6rc_b, ← show a5Root 5 1 = -(a5Root 1 5) by decide]
    exact a5Root_check 5 1 (by decide))

private theorem e6rc_xr_mem_qE
    {r : V} (hr : r ∈ e6rc_level 1 ∪ e6rc_level 2) : xr r ∈ qE := by
  rcases Finset.mem_union.mp hr with h | h
  · exact e6rc_xr_mem_rootSpan_subgroupOf (S := qRoots)
      ⟨mem_rootFinset.mp (Finset.mem_filter.mp h).1, by
        have := (Finset.mem_filter.mp h).2
        rw [this]; norm_num⟩
  · exact e6rc_xr_mem_rootSpan_subgroupOf (S := qRoots)
      ⟨mem_rootFinset.mp (Finset.mem_filter.mp h).1, by
        have := (Finset.mem_filter.mp h).2
        rw [this]; norm_num⟩

private noncomputable def e6rc_g1 :
    EC := rOne 2 0

private theorem e6rc_g1_mem_j0E :
    e6rc_g1 ∈ j0E :=
  Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl rfl))

private abbrev e6rc_caseA (γ : V) : Prop :=
  (γ - e6rc_a) ∈ rootFinset .E6 ∧ (γ - e6rc_b) ∉ rootFinset .E6 ∧
    γ ≠ e6rc_a ∧ γ ≠ -e6rc_a ∧ γ ≠ e6rc_b ∧ γ ≠ -e6rc_b

private abbrev e6rc_caseB (γ : V) : Prop :=
  (γ - e6rc_a) ∉ rootFinset .E6 ∧ (γ - e6rc_b) ∈ rootFinset .E6 ∧
    γ ≠ e6rc_a ∧ γ ≠ -e6rc_a ∧ γ ≠ e6rc_b ∧ γ ≠ -e6rc_b ∧
    (-e6rc_a ≠ (-e6rc_b) + γ) ∧ (-e6rc_a ≠ -((-e6rc_b) + γ)) ∧
    ((-e6rc_a) + ((-e6rc_b) + γ)) ∉ rootFinset .E6

private theorem e6rc_level1_cases :
    ∀ γ ∈ e6rc_level 1, e6rc_caseA γ ∨ e6rc_caseB γ := by
  decide +kernel

private theorem e6rc_stageA_caseA
    {H : Subgroup EC} {γ : V} (hA : e6rc_caseA γ) (hγroot : IsRoot .E6 γ)
    (hg1 : e6rc_g1 ∈ H) (hxγ : xr γ ∈ H) : xr (γ - e6rc_a) ∈ H := by
  obtain ⟨ha, hb, h1, h2, h3, h4⟩ := hA
  have haI : IsRoot .E6 (γ - e6rc_a) := mem_rootFinset.mp ha
  have hbI : ¬ IsRoot .E6 (γ - e6rc_b) := fun h => hb (mem_rootFinset.mpr h)
  have hne_a : -e6rc_a ≠ γ := fun h => h2 h.symm
  have hne_a' : -e6rc_a ≠ -γ := fun h => h1 (neg_injective h).symm
  have hne_b : -e6rc_b ≠ γ := fun h => h4 h.symm
  have hne_b' : -e6rc_b ≠ -γ := fun h => h3 (neg_injective h).symm
  have hca : xr (-e6rc_a) * xr γ * (xr (-e6rc_a))⁻¹ = xr ((-e6rc_a) + γ) * xr γ :=
    e6rc_xr_conj_of_isRoot e6rc_isRoot_neg_a hγroot hne_a hne_a'
      (by rw [add_comm]; exact haI)
  have hcb : xr (-e6rc_b) * xr γ * (xr (-e6rc_b))⁻¹ = xr γ :=
    e6rc_xr_conj_of_not e6rc_isRoot_neg_b hγroot hne_b hne_b'
      (by rw [add_comm]; exact hbI)
  have hg1eq : e6rc_g1 = xr (-e6rc_a) * xr (-e6rc_b) := by
    rw [e6rc_g1, rOne]
    rw [show a5Root (blk 2 0) (blk 0 0) = -e6rc_a by decide,
      show a5Root (blk 2 1) (blk 0 1) = -e6rc_b by decide]
  have hconj : e6rc_g1 * xr γ * (e6rc_g1)⁻¹ = xr ((-e6rc_a) + γ) * xr γ := by
    rw [hg1eq]
    calc (xr (-e6rc_a) * xr (-e6rc_b)) * xr γ * (xr (-e6rc_a) * xr (-e6rc_b))⁻¹
        = xr (-e6rc_a) * (xr (-e6rc_b) * xr γ * (xr (-e6rc_b))⁻¹) * (xr (-e6rc_a))⁻¹ := by
          group
      _ = xr (-e6rc_a) * xr γ * (xr (-e6rc_a))⁻¹ := by rw [hcb]
      _ = xr ((-e6rc_a) + γ) * xr γ := hca
  have hmem : xr ((-e6rc_a) + γ) ∈ H := by
    have h1' : xr ((-e6rc_a) + γ) * xr γ ∈ H := by
      rw [← hconj]
      exact H.mul_mem (H.mul_mem hg1 hxγ) (H.inv_mem hg1)
    simpa using H.mul_mem h1' (H.inv_mem hxγ)
  simpa [sub_eq_add_neg, add_comm] using hmem

private theorem e6rc_stageA_caseB
    {H : Subgroup EC} {γ : V} (hB : e6rc_caseB γ) (hγroot : IsRoot .E6 γ)
    (hg1 : e6rc_g1 ∈ H) (hxγ : xr γ ∈ H) : xr (γ - e6rc_b) ∈ H := by
  obtain ⟨ha, hb, h1, h2, h3, h4, hne1, hne2, hab⟩ := hB
  have haI : ¬ IsRoot .E6 (γ - e6rc_a) := fun h => ha (mem_rootFinset.mpr h)
  have hbI : IsRoot .E6 (γ - e6rc_b) := mem_rootFinset.mp hb
  have hbI' : IsRoot .E6 ((-e6rc_b) + γ) := by rw [add_comm]; exact hbI
  have habI : ¬ IsRoot .E6 ((-e6rc_a) + ((-e6rc_b) + γ)) :=
    fun h => hab (mem_rootFinset.mpr h)
  have hca : xr (-e6rc_a) * xr γ * (xr (-e6rc_a))⁻¹ = xr γ :=
    e6rc_xr_conj_of_not e6rc_isRoot_neg_a hγroot
      (fun h => h2 h.symm) (fun h => h1 (neg_injective h).symm)
      (by rw [add_comm]; exact haI)
  have hcb : xr (-e6rc_b) * xr γ * (xr (-e6rc_b))⁻¹ = xr ((-e6rc_b) + γ) * xr γ :=
    e6rc_xr_conj_of_isRoot e6rc_isRoot_neg_b hγroot
      (fun h => h4 h.symm) (fun h => h3 (neg_injective h).symm) hbI'
  have hcab : xr (-e6rc_a) * xr ((-e6rc_b) + γ) * (xr (-e6rc_a))⁻¹ = xr ((-e6rc_b) + γ) :=
    e6rc_xr_conj_of_not e6rc_isRoot_neg_a hbI' hne1 hne2 habI
  have hg1eq : e6rc_g1 = xr (-e6rc_a) * xr (-e6rc_b) := by
    rw [e6rc_g1, rOne]
    rw [show a5Root (blk 2 0) (blk 0 0) = -e6rc_a by decide,
      show a5Root (blk 2 1) (blk 0 1) = -e6rc_b by decide]
  have hconj : e6rc_g1 * xr γ * (e6rc_g1)⁻¹ = xr ((-e6rc_b) + γ) * xr γ := by
    rw [hg1eq]
    calc (xr (-e6rc_a) * xr (-e6rc_b)) * xr γ * (xr (-e6rc_a) * xr (-e6rc_b))⁻¹
        = xr (-e6rc_a) * (xr (-e6rc_b) * xr γ * (xr (-e6rc_b))⁻¹) * (xr (-e6rc_a))⁻¹ := by
          group
      _ = xr (-e6rc_a) * (xr ((-e6rc_b) + γ) * xr γ) * (xr (-e6rc_a))⁻¹ := by rw [hcb]
      _ = (xr (-e6rc_a) * xr ((-e6rc_b) + γ) * (xr (-e6rc_a))⁻¹) *
            (xr (-e6rc_a) * xr γ * (xr (-e6rc_a))⁻¹) := by group
      _ = xr ((-e6rc_b) + γ) * xr γ := by rw [hcab, hca]
  have hmem : xr ((-e6rc_b) + γ) ∈ H := by
    have h1' : xr ((-e6rc_b) + γ) * xr γ ∈ H := by
      rw [← hconj]
      exact H.mul_mem (H.mul_mem hg1 hxγ) (H.inv_mem hg1)
    simpa using H.mul_mem h1' (H.inv_mem hxγ)
  simpa [sub_eq_add_neg, add_comm] using hmem

private def e6rc_shiftA (γ : V) : V :=
  if (γ - e6rc_a) ∈ rootFinset .E6 then γ - e6rc_a else γ - e6rc_b

private theorem e6rc_shiftA_mem_rootFinset (γ : V) (hγ : γ ∈ e6rc_level 1) :
    e6rc_shiftA γ ∈ rootFinset .E6 := by
  by_cases h : (γ - e6rc_a) ∈ rootFinset .E6
  · rw [e6rc_shiftA, if_pos h]; exact h
  · rw [e6rc_shiftA, if_neg h]
    rcases e6rc_level1_cases γ hγ with hA | hB
    · exact absurd hA.1 h
    · exact hB.2.1

private theorem e6rc_stageA_mem
    {H : Subgroup EC} (hq : qE ≤ H) (hj0 : j0E ≤ H) (γ : V)
    (hγ : γ ∈ e6rc_level 1) : xr (e6rc_shiftA γ) ∈ H := by
  have hg1 : e6rc_g1 ∈ H := hj0 e6rc_g1_mem_j0E
  have hγroot : IsRoot .E6 γ := mem_rootFinset.mp (Finset.mem_filter.mp hγ).1
  have hxγ : xr γ ∈ H := hq (e6rc_xr_mem_qE (Finset.mem_union_left _ hγ))
  by_cases h : (γ - e6rc_a) ∈ rootFinset .E6
  · rw [e6rc_shiftA, if_pos h]
    rcases e6rc_level1_cases γ hγ with hA | hB
    · exact e6rc_stageA_caseA hA hγroot hg1 hxγ
    · exact absurd h hB.1
  · rw [e6rc_shiftA, if_neg h]
    rcases e6rc_level1_cases γ hγ with hA | hB
    · exact absurd hA.1 h
    · exact e6rc_stageA_caseB hB hγroot hg1 hxγ

private def e6rc_base1 : Finset V :=
  (e6rc_level 1 ∪ e6rc_level 2) ∪ (e6rc_level 1).image e6rc_shiftA

private theorem e6rc_base1_subset : e6rc_base1 ⊆ rootFinset .E6 := by
  intro r hr
  rcases Finset.mem_union.mp hr with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp h
    exact e6rc_shiftA_mem_rootFinset γ hγ

private theorem e6rc_base1_mem
    {H : Subgroup EC} (hq : qE ≤ H) (hj0 : j0E ≤ H) :
    ∀ r ∈ e6rc_base1, xr r ∈ H := by
  intro r hr
  rcases Finset.mem_union.mp hr with h | h
  · exact hq (e6rc_xr_mem_qE h)
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp h
    exact e6rc_stageA_mem hq hj0 γ hγ

private theorem e6rc_item1_all
    {H : Subgroup EC} (hq : qE ≤ H) (hj0 : j0E ≤ H) :
    ∀ β, IsRoot .E6 β → xr β ∈ H :=
  e6rc_all_xr_of_iter e6rc_base1_subset (e6rc_base1_mem hq hj0)
    (N := 1) (by decide +kernel)

private theorem e6rc_word1 {G : Type*} [Group G] (a b a' b' : G)
    (h1 : Commute b a') (h2 : Commute b' a) (h3 : Commute b a) :
    (a * b) * (a' * b') * (a * b) = (a * a' * a) * (b * b' * b) := by
  calc (a * b) * (a' * b') * (a * b)
      = a * (b * a') * (b' * a) * b := by group
    _ = a * (a' * b) * (a * b') * b := by rw [h1.eq, h2.eq]
    _ = a * (a' * (b * a)) * b' * b := by group
    _ = a * (a' * (a * b)) * b' * b := by rw [h3.eq]
    _ = (a * a' * a) * (b * b' * b) := by group

private theorem e6rc_ne_02 : (0 : Fin 6) ≠ 2 := by decide

private theorem e6rc_ne_13 : (1 : Fin 6) ≠ 3 := by decide

private theorem e6rc_ne_24 : (2 : Fin 6) ≠ 4 := by decide

private theorem e6rc_ne_35 : (3 : Fin 6) ≠ 5 := by decide

private theorem e6rc_iota_T
    (a b : Fin 6) (hab : a ≠ b) :
    E6Pilot.slToAdjointE6 F2 (Matrix.SpecialLinearGroup.transvection hab (1 : F2)) =
      xr (a5Root a b) := by
  simpa [xr] using E6Pilot.slToAdjointE6_transvection hab (1 : F2)

private theorem e6rc_rOne_eq_iota
    (k l : Fin 3) (h0 : blk k 0 ≠ blk l 0) (h1 : blk k 1 ≠ blk l 1) :
    rOne k l = E6Pilot.slToAdjointE6 F2
      (Matrix.SpecialLinearGroup.transvection h0 (1 : F2) *
       Matrix.SpecialLinearGroup.transvection h1 (1 : F2)) := by
  rw [rOne, ← e6rc_iota_T (blk k 0) (blk l 0) h0,
    ← e6rc_iota_T (blk k 1) (blk l 1) h1, ← map_mul]

private def e6rc_sigma : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 2 4 * Equiv.swap 3 5

private noncomputable def e6rc_pi :
    EC :=
  (rOne 0 1 * rOne 1 0 * rOne 0 1) * (rOne 1 2 * rOne 2 1 * rOne 1 2)

private theorem e6rc_pi_matrix :
    Matrix.SpecialLinearGroup.transvection e6rc_ne_02 (1 : F2) *
      Matrix.SpecialLinearGroup.transvection e6rc_ne_13 (1 : F2) *
        (Matrix.SpecialLinearGroup.transvection e6rc_ne_02.symm (1 : F2) *
          Matrix.SpecialLinearGroup.transvection e6rc_ne_13.symm (1 : F2)) *
      (Matrix.SpecialLinearGroup.transvection e6rc_ne_02 (1 : F2) *
        Matrix.SpecialLinearGroup.transvection e6rc_ne_13 (1 : F2)) *
    (Matrix.SpecialLinearGroup.transvection e6rc_ne_24 (1 : F2) *
      Matrix.SpecialLinearGroup.transvection e6rc_ne_35 (1 : F2) *
        (Matrix.SpecialLinearGroup.transvection e6rc_ne_24.symm (1 : F2) *
          Matrix.SpecialLinearGroup.transvection e6rc_ne_35.symm (1 : F2)) *
      (Matrix.SpecialLinearGroup.transvection e6rc_ne_24 (1 : F2) *
        Matrix.SpecialLinearGroup.transvection e6rc_ne_35 (1 : F2))) =
      slPerm gf2_two e6rc_sigma := by
  let T02 : Matrix.SpecialLinearGroup (Fin 6) F2 := Matrix.SpecialLinearGroup.transvection e6rc_ne_02 (1 : F2)
  let T20 : Matrix.SpecialLinearGroup (Fin 6) F2 := Matrix.SpecialLinearGroup.transvection e6rc_ne_02.symm (1 : F2)
  let T13 : Matrix.SpecialLinearGroup (Fin 6) F2 := Matrix.SpecialLinearGroup.transvection e6rc_ne_13 (1 : F2)
  let T31 : Matrix.SpecialLinearGroup (Fin 6) F2 := Matrix.SpecialLinearGroup.transvection e6rc_ne_13.symm (1 : F2)
  let T24 : Matrix.SpecialLinearGroup (Fin 6) F2 := Matrix.SpecialLinearGroup.transvection e6rc_ne_24 (1 : F2)
  let T42 : Matrix.SpecialLinearGroup (Fin 6) F2 := Matrix.SpecialLinearGroup.transvection e6rc_ne_24.symm (1 : F2)
  let T35 : Matrix.SpecialLinearGroup (Fin 6) F2 := Matrix.SpecialLinearGroup.transvection e6rc_ne_35 (1 : F2)
  let T53 : Matrix.SpecialLinearGroup (Fin 6) F2 := Matrix.SpecialLinearGroup.transvection e6rc_ne_35.symm (1 : F2)
  have c1 : Commute T13 T20 :=
    commute_transvection_of_ne e6rc_ne_13 e6rc_ne_02.symm (by decide) (by decide) (1 : F2) (1 : F2)
  have c2 : Commute T31 T02 :=
    commute_transvection_of_ne e6rc_ne_13.symm e6rc_ne_02 (by decide) (by decide) (1 : F2) (1 : F2)
  have c3 : Commute T13 T02 :=
    commute_transvection_of_ne e6rc_ne_13 e6rc_ne_02 (by decide) (by decide) (1 : F2) (1 : F2)
  have c4 : Commute T35 T42 :=
    commute_transvection_of_ne e6rc_ne_35 e6rc_ne_24.symm (by decide) (by decide) (1 : F2) (1 : F2)
  have c5 : Commute T53 T24 :=
    commute_transvection_of_ne e6rc_ne_35.symm e6rc_ne_24 (by decide) (by decide) (1 : F2) (1 : F2)
  have c6 : Commute T35 T24 :=
    commute_transvection_of_ne e6rc_ne_35 e6rc_ne_24 (by decide) (by decide) (1 : F2) (1 : F2)
  have hA : (T02 * T13) * (T20 * T31) * (T02 * T13) = (T02 * T20 * T02) * (T13 * T31 * T13) :=
    e6rc_word1 T02 T13 T20 T31 c1 c2 c3
  have hB : (T24 * T35) * (T42 * T53) * (T24 * T35) = (T24 * T42 * T24) * (T35 * T53 * T35) :=
    e6rc_word1 T24 T35 T42 T53 c4 c5 c6
  calc T02 * T13 * (T20 * T31) * (T02 * T13) * (T24 * T35 * (T42 * T53) * (T24 * T35))
      = (T02 * T13) * (T20 * T31) * (T02 * T13) * (T24 * T35) * (T42 * T53) * (T24 * T35) := by
        group
    _ = ((T02 * T13) * (T20 * T31) * (T02 * T13)) *
          ((T24 * T35) * (T42 * T53) * (T24 * T35)) := by group
    _ = ((T02 * T20 * T02) * (T13 * T31 * T13)) *
          ((T24 * T42 * T24) * (T35 * T53 * T35)) := by rw [hA, hB]
    _ = (slPerm gf2_two (Equiv.swap (0 : Fin 6) 2) *
          slPerm gf2_two (Equiv.swap (1 : Fin 6) 3)) *
        (slPerm gf2_two (Equiv.swap (2 : Fin 6) 4) *
          slPerm gf2_two (Equiv.swap (3 : Fin 6) 5)) := by
          rw [← slPerm_swap_eq_transvections gf2_two e6rc_ne_02,
            ← slPerm_swap_eq_transvections gf2_two e6rc_ne_13,
            ← slPerm_swap_eq_transvections gf2_two e6rc_ne_24,
            ← slPerm_swap_eq_transvections gf2_two e6rc_ne_35]
    _ = slPerm gf2_two e6rc_sigma := by
          rw [e6rc_sigma, map_mul, map_mul, map_mul]
          group

private theorem e6rc_pi_eq_iota
    : e6rc_pi = E6Pilot.slToAdjointE6 F2 (slPerm gf2_two e6rc_sigma) := by
  have h01 := e6rc_rOne_eq_iota (0 : Fin 3) 1 e6rc_ne_02 e6rc_ne_13
  have h10 := e6rc_rOne_eq_iota (1 : Fin 3) 0 e6rc_ne_02.symm e6rc_ne_13.symm
  have h12 := e6rc_rOne_eq_iota (1 : Fin 3) 2 e6rc_ne_24 e6rc_ne_35
  have h21 := e6rc_rOne_eq_iota (2 : Fin 3) 1 e6rc_ne_24.symm e6rc_ne_35.symm
  rw [e6rc_pi, h01, h10, h12, h21]
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  exact congrArg (E6Pilot.slToAdjointE6 F2) e6rc_pi_matrix

private theorem e6rc_pi_conj
    (i j : Fin 6) (hij : i ≠ j) :
    e6rc_pi * xr (a5Root i j) * e6rc_pi⁻¹ =
      xr (a5Root (e6rc_sigma i) (e6rc_sigma j)) := by
  have hT : xr (a5Root i j) =
      E6Pilot.slToAdjointE6 F2 (Matrix.SpecialLinearGroup.transvection hij (1 : F2)) :=
    (e6rc_iota_T i j hij).symm
  have hconj := CFSG.LieType.Universal.SpecialLinear.conj_transvection_of_coe_eq_signedPerm (g := slPerm gf2_two e6rc_sigma)
    (π := e6rc_sigma) (ε := fun _ => (1 : F2)) (coe_slPerm gf2_two e6rc_sigma)
    (fun s => by simp) hij (1 : F2)
  have hmat : slPerm gf2_two e6rc_sigma *
        Matrix.SpecialLinearGroup.transvection hij (1 : F2) *
        (slPerm gf2_two e6rc_sigma)⁻¹ =
      Matrix.SpecialLinearGroup.transvection (e6rc_sigma.injective.ne hij) (1 : F2) := by
    simpa using hconj
  calc e6rc_pi * xr (a5Root i j) * e6rc_pi⁻¹
      = E6Pilot.slToAdjointE6 F2 (slPerm gf2_two e6rc_sigma) *
          E6Pilot.slToAdjointE6 F2 (Matrix.SpecialLinearGroup.transvection hij (1 : F2)) *
          (E6Pilot.slToAdjointE6 F2 (slPerm gf2_two e6rc_sigma))⁻¹ := by
          rw [e6rc_pi_eq_iota, hT]
    _ = E6Pilot.slToAdjointE6 F2
          (slPerm gf2_two e6rc_sigma *
            Matrix.SpecialLinearGroup.transvection hij (1 : F2) *
            (slPerm gf2_two e6rc_sigma)⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = E6Pilot.slToAdjointE6 F2
          (Matrix.SpecialLinearGroup.transvection (e6rc_sigma.injective.ne hij) (1 : F2)) := by
          rw [hmat]
    _ = xr (a5Root (e6rc_sigma i) (e6rc_sigma j)) := e6rc_iota_T _ _ _

private theorem e6rc_pi_conj_mem
    {H : Subgroup EC} (hpi : e6rc_pi ∈ H) {i j : Fin 6} (hij : i ≠ j)
    (hijH : xr (a5Root i j) ∈ H) :
    xr (a5Root (e6rc_sigma i) (e6rc_sigma j)) ∈ H := by
  have h := e6rc_pi_conj i j hij
  have hmem : e6rc_pi * xr (a5Root i j) * e6rc_pi⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem hpi hijH) (H.inv_mem hpi)
  rw [h] at hmem
  exact hmem

private theorem e6rc_orbit_mem
    {H : Subgroup EC} (hpi : e6rc_pi ∈ H) (i j : Fin 6) (hij : i ≠ j) (k : ℕ)
    (hijH : xr (a5Root i j) ∈ H) :
    xr (a5Root ((e6rc_sigma ^ k) i) ((e6rc_sigma ^ k) j)) ∈ H := by
  induction k with
  | zero => simpa using hijH
  | succ k ih =>
      have hne : (e6rc_sigma ^ k) i ≠ (e6rc_sigma ^ k) j := (e6rc_sigma ^ k).injective.ne hij
      have hstep := e6rc_pi_conj_mem (H := H) hpi hne ih
      simpa [pow_succ', Equiv.Perm.mul_apply] using hstep

private theorem e6rc_rOne_mem_jE
    (k l : Fin 3) (hkl : k ≠ l) : rOne k l ∈ jE :=
  Subgroup.subset_closure ⟨k, l, hkl, Or.inl rfl⟩

private theorem e6rc_pi_mem_jE :
    e6rc_pi ∈ jE := by
  rw [e6rc_pi]
  exact jE.mul_mem
    (jE.mul_mem (jE.mul_mem (e6rc_rOne_mem_jE 0 1 (by decide))
      (e6rc_rOne_mem_jE 1 0 (by decide))) (e6rc_rOne_mem_jE 0 1 (by decide)))
    (jE.mul_mem (jE.mul_mem (e6rc_rOne_mem_jE 1 2 (by decide))
      (e6rc_rOne_mem_jE 2 1 (by decide))) (e6rc_rOne_mem_jE 1 2 (by decide)))

private theorem e6rc_level2_mem_z0E
    {r : V} (hr : r ∈ e6rc_level 2) : xr r ∈ z0E :=
  e6rc_xr_mem_rootSpan_subgroupOf (S := zRoots)
    ⟨mem_rootFinset.mp (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩

private noncomputable def e6rc_uMu (L : List V) :
    Subgroup EC :=
  (rootSpan .E6 F2 {β | β ∈ L}).subgroupOf (adjointGroup .E6 F2)

private theorem e6rc_mu_mem_uMu
    (L : List V) {r : V} (hr : r ∈ L.toFinset) : xr r ∈ e6rc_uMu L :=
  e6rc_xr_mem_rootSpan_subgroupOf (S := {β | β ∈ L}) (List.mem_toFinset.mp hr)

private def e6rc_pairs1 : List (Fin 6 × Fin 6) :=
  [(0, 4), (0, 5), (1, 4), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5)]

private def e6rc_pairs2 : List (Fin 6 × Fin 6) :=
  [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5)]

private def e6rc_orbitSet (pairs : List (Fin 6 × Fin 6)) : Finset V :=
  (pairs.flatMap (fun p => (List.range 3).map (fun k =>
    a5Root ((e6rc_sigma ^ k) p.1) ((e6rc_sigma ^ k) p.2)))).toFinset

private theorem e6rc_orbitSet_mem {pairs : List (Fin 6 × Fin 6)} {r : V}
    (hr : r ∈ e6rc_orbitSet pairs) :
    ∃ p ∈ pairs, ∃ k < 3, r = a5Root ((e6rc_sigma ^ k) p.1) ((e6rc_sigma ^ k) p.2) := by
  rw [e6rc_orbitSet, List.mem_toFinset] at hr
  rcases List.mem_flatMap.mp hr with ⟨p, hp, hr⟩
  rcases List.mem_map.mp hr with ⟨k, hk, rfl⟩
  exact ⟨p, hp, k, List.mem_range.mp hk, rfl⟩

private theorem e6rc_orbit_mem_set
    {H : Subgroup EC} {pairs : List (Fin 6 × Fin 6)} (hpi : e6rc_pi ∈ H)
    (hpne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (hpairs : ∀ p ∈ pairs, xr (a5Root p.1 p.2) ∈ H) :
    ∀ r ∈ e6rc_orbitSet pairs, xr r ∈ H := by
  intro r hr
  obtain ⟨p, hp, k, hk, rfl⟩ := e6rc_orbitSet_mem hr
  exact e6rc_orbit_mem hpi p.1 p.2 (hpne p hp) k (hpairs p hp)

private def e6rc_base4 (L : List V) (pairs : List (Fin 6 × Fin 6)) : Finset V :=
  e6rc_level 2 ∪ L.toFinset ∪ e6rc_orbitSet pairs

private theorem e6rc_base4_mem
    {H : Subgroup EC} {L : List V} {pairs : List (Fin 6 × Fin 6)}
    (hz : ∀ r ∈ e6rc_level 2, xr r ∈ H)
    (hU : ∀ r ∈ L.toFinset, xr r ∈ H)
    (hpi : e6rc_pi ∈ H) (hpne : ∀ p ∈ pairs, p.1 ≠ p.2)
    (hpairs : ∀ p ∈ pairs, xr (a5Root p.1 p.2) ∈ H) :
    ∀ r ∈ e6rc_base4 L pairs, xr r ∈ H := by
  intro r hr
  rcases Finset.mem_union.mp hr with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact hz r h
    · exact hU r h
  · exact e6rc_orbit_mem_set hpi hpne hpairs r h

private def e6rc_base4_1 : Finset V := e6rc_base4 mu1List e6rc_pairs1

private def e6rc_base4_2 : Finset V := e6rc_base4 mu2List e6rc_pairs2

private theorem e6rc_base4_1_subset : e6rc_base4_1 ⊆ rootFinset .E6 := by decide +kernel

private theorem e6rc_base4_1_closure :
    ∀ r ∈ rootFinset .E6, r ∈ (e6rc_step^[2]) e6rc_base4_1 := by decide +kernel

private theorem e6rc_pairs1_base :
    ∀ p ∈ e6rc_pairs1, a5Root p.1 p.2 ∈ e6rc_level 2 ∪ mu1List.toFinset := by decide +kernel

private theorem e6rc_base4_2_subset : e6rc_base4_2 ⊆ rootFinset .E6 := by decide +kernel

private theorem e6rc_base4_2_closure :
    ∀ r ∈ rootFinset .E6, r ∈ (e6rc_step^[2]) e6rc_base4_2 := by decide +kernel

private theorem e6rc_pairs2_base :
    ∀ p ∈ e6rc_pairs2, a5Root p.1 p.2 ∈ e6rc_level 2 ∪ mu2List.toFinset := by decide +kernel

theorem qE_sup_j0E :
    qE ⊔ j0E = ⊤ := by
  apply e6rc_eq_top_of_forall_xr
  exact e6rc_item1_all le_sup_left le_sup_right

theorem jE_sup_z0E_sup_uMu1 :
    jE ⊔ (z0E ⊔ uMu1) = ⊤ := by
  apply e6rc_eq_top_of_forall_xr
  have hlevel : ∀ r ∈ e6rc_level 2, xr r ∈ (jE ⊔ (z0E ⊔ uMu1) : Subgroup EC) :=
    fun r hr => Subgroup.mem_sup_right (Subgroup.mem_sup_left (e6rc_level2_mem_z0E hr))
  have hmu : ∀ r ∈ mu1List.toFinset, xr r ∈ (jE ⊔ (z0E ⊔ uMu1) : Subgroup EC) :=
    fun r hr => Subgroup.mem_sup_right (Subgroup.mem_sup_right (e6rc_mu_mem_uMu mu1List hr))
  have hbase : ∀ r ∈ e6rc_level 2 ∪ mu1List.toFinset,
      xr r ∈ (jE ⊔ (z0E ⊔ uMu1) : Subgroup EC) := by
    intro r hr
    rcases Finset.mem_union.mp hr with h | h
    · exact hlevel r h
    · exact hmu r h
  have hpairs : ∀ p ∈ e6rc_pairs1, xr (a5Root p.1 p.2) ∈ (jE ⊔ (z0E ⊔ uMu1) : Subgroup EC) :=
    fun p hp => hbase _ (e6rc_pairs1_base p hp)
  exact e6rc_all_xr_of_iter e6rc_base4_1_subset
    (e6rc_base4_mem hlevel hmu (Subgroup.mem_sup_left e6rc_pi_mem_jE) (by decide) hpairs)
    (N := 2) e6rc_base4_1_closure

theorem jE_sup_z0E_sup_uMu2 :
    jE ⊔ (z0E ⊔ uMu2) = ⊤ := by
  apply e6rc_eq_top_of_forall_xr
  have hlevel : ∀ r ∈ e6rc_level 2, xr r ∈ (jE ⊔ (z0E ⊔ uMu2) : Subgroup EC) :=
    fun r hr => Subgroup.mem_sup_right (Subgroup.mem_sup_left (e6rc_level2_mem_z0E hr))
  have hmu : ∀ r ∈ mu2List.toFinset, xr r ∈ (jE ⊔ (z0E ⊔ uMu2) : Subgroup EC) :=
    fun r hr => Subgroup.mem_sup_right (Subgroup.mem_sup_right (e6rc_mu_mem_uMu mu2List hr))
  have hbase : ∀ r ∈ e6rc_level 2 ∪ mu2List.toFinset,
      xr r ∈ (jE ⊔ (z0E ⊔ uMu2) : Subgroup EC) := by
    intro r hr
    rcases Finset.mem_union.mp hr with h | h
    · exact hlevel r h
    · exact hmu r h
  have hpairs : ∀ p ∈ e6rc_pairs2, xr (a5Root p.1 p.2) ∈ (jE ⊔ (z0E ⊔ uMu2) : Subgroup EC) :=
    fun p hp => hbase _ (e6rc_pairs2_base p hp)
  exact e6rc_all_xr_of_iter e6rc_base4_2_subset
    (e6rc_base4_mem hlevel hmu (Subgroup.mem_sup_left e6rc_pi_mem_jE) (by decide) hpairs)
    (N := 2) e6rc_base4_2_closure

end CFSG.StandardType.GGSixE6Two
