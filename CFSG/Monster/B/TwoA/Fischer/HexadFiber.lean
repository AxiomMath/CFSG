module

public import CFSG.Monster.B.TwoA.Fischer.HexadFiberLocal

public section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical CFSG.Monster.B.Classical.UnitarySix
  CFSG.Monster.B.TwoA.Unitary.Clique CFSG.Fischer CFSG.LinearGroups
  CFSG.LieType.Universal.Unitary

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem inter_neighborSet_eq_empty_or_mem {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V} (hxC : x ∉ C) :
    C ∩ (sliceGraph lab Y).neighborSet x = ∅ ∨
      C ∩ (sliceGraph lab Y).neighborSet x ∈ cliqueBlocks lab C := by
  rcases Set.eq_empty_or_nonempty (C ∩ (sliceGraph lab Y).neighborSet x) with h | ⟨u, huC, hux⟩
  · exact Or.inl h
  · right
    obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 huC)
    obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC huC
    obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
    have hxn : x ∈ (sliceGraph lab Y).neighborSet u := (sliceGraph lab Y).adj_symm hux
    have hxW : L.τ ⟨x, hxn⟩ ∉ planePts (smulSub g W0) := by
      rw [← hWe, L.mem_img_iff]
      exact hxC
    rw [show x = ((⟨x, hxn⟩ : (sliceGraph lab Y).neighborSet u) : V) from rfl,
      L.inter_neighborSet_eq hS hC huC hWe ⟨x, hxn⟩ hxC]
    exact ((L.mem_cliqueBlocks_and_mem_iff hS hC huC g hWe _).2
      ⟨_, inf_le_right, finrank_perpSub_inf hW hxW, rfl⟩).1

theorem hexadFiber_of_mem_cliqueBlocks {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {B : Set V}
    (hB : B ∈ cliqueBlocks lab C) :
    (hexadFiber lab Y C B).ncard = 32 ∧
      (∀ x ∈ hexadFiber lab Y C B, ∀ y ∈ hexadFiber lab Y C B,
        ∃ r ∈ ptStab act lab Y C, act r x = y) ∧
      (∀ x ∈ hexadFiber lab Y C B,
        ptStab act lab Y C ⊓ actStab act x = Subgroup.closure (lab '' B) ∧
          Nat.card ↥(ptStab act lab Y C ⊓ actStab act x) = 32) := by
  obtain ⟨T, -, hT6, hBT⟩ := (mem_cliqueBlocks_iff B).1 hB
  obtain ⟨⟨u, huC⟩, huT⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
  have huB : u ∈ B := by
    rw [hBT]
    exact ⟨_, huT, rfl⟩
  obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 huC)
  obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC huC
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  obtain ⟨A, hAW, hA, rfl⟩ := (L.mem_cliqueBlocks_and_mem_iff hS hC huC g hWe B).1 ⟨hB, huB⟩
  have hX := L.hexadFiber_eq hS hC huC hW hWe hAW
  refine ⟨L.ncard_hexadFiber hS hC huC hW hWe hAW hA, ?_, ?_⟩
  · intro x hx y hy
    rw [hX] at hx hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact L.exists_ptStab_act_eq hS hC huC hW hWe hAW hA hz hz'
  · intro x hx
    rw [hX] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact L.ptStab_inf_actStab hS hC huC hW hWe hAW hA z hz

theorem ncard_biUnion_hexadFiber {C : Set V}
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    (h32 : ∀ B ∈ cliqueBlocks lab C, (hexadFiber lab Y C B).ncard = 32)
    (h77 : (cliqueBlocks lab C).ncard = 77) :
    (⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B).ncard = 2464 := by
  classical
  set U := ⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B with hUdef
  have hUY : U ⊆ Y := Set.iUnion₂_subset fun B _ x hx => hx.1
  have hUfin : U.Finite := hS.finite.subset hUY
  have hℬfin : (cliqueBlocks lab C).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [h77]; norm_num)
  have hmaps : Set.MapsTo (fun x => C ∩ (sliceGraph lab Y).neighborSet x) hUfin.toFinset
      hℬfin.toFinset := by
    intro x hx
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hx ⊢
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hx
    change C ∩ (sliceGraph lab Y).neighborSet x ∈ cliqueBlocks lab C
    rw [hxB.2.2]
    exact hB
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ B ∈ hℬfin.toFinset,
      {x ∈ hUfin.toFinset | C ∩ (sliceGraph lab Y).neighborSet x = B}.card = 32 := by
    intro B hB
    rw [Set.Finite.mem_toFinset] at hB
    rw [← h32 B hB, ← Set.ncard_coe_finset]
    congr 1
    ext x
    rw [Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hxU, hxB⟩
      obtain ⟨B', -, hxB'⟩ := Set.mem_iUnion₂.1 hxU
      exact ⟨hxB'.1, hxB'.2.1, hxB⟩
    · intro hx
      exact ⟨Set.mem_iUnion₂.2 ⟨B, hB, hx⟩, hx.2.2⟩
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hℬfin, h77] at h
  rw [Set.ncard_eq_toFinset_card _ hUfin, h]

theorem clique_hexad_fibers {C : Set V} (hC : IsSliceMaxClique lab Y C) :
    ∃ _ : CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C)),
      (∀ x ∈ Y, x ∉ C → C ∩ (sliceGraph lab Y).neighborSet x = ∅ ∨
        C ∩ (sliceGraph lab Y).neighborSet x ∈ cliqueBlocks lab C) ∧
      (∀ B ∈ cliqueBlocks lab C, (hexadFiber lab Y C B).ncard = 32 ∧
        (∀ r ∈ ptStab act lab Y C, ∀ x ∈ hexadFiber lab Y C B,
          act r x ∈ hexadFiber lab Y C B) ∧
        (∀ x ∈ hexadFiber lab Y C B, ∀ y ∈ hexadFiber lab Y C B,
          ∃ r ∈ ptStab act lab Y C, act r x = y) ∧
        (∀ x ∈ hexadFiber lab Y C B,
          ptStab act lab Y C ⊓ actStab act x = Subgroup.closure (lab '' B)) ∧
        Nat.card (Subgroup.closure (lab '' B)) = 32) ∧
      Y = C ∪ (⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B) ∪ hexadFiber lab Y C ∅ ∧
      Disjoint C (⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B) ∧
      Disjoint C (hexadFiber lab Y C ∅) ∧
      Disjoint (⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B) (hexadFiber lab Y C ∅) ∧
      (∀ B ∈ cliqueBlocks lab C, ∀ B' ∈ cliqueBlocks lab C, B ≠ B' →
        Disjoint (hexadFiber lab Y C B) (hexadFiber lab Y C B')) ∧
      C.ncard = 22 ∧
      (⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B).ncard = 2464 ∧
      (hexadFiber lab Y C ∅).ncard = 1024 ∧
      (∀ a ∈ setStab act lab Y C, act a '' hexadFiber lab Y C ∅ = hexadFiber lab Y C ∅) ∧
      (∀ a ∈ setStab act lab Y C, ∀ B ∈ cliqueBlocks lab C,
        act a '' B ∈ cliqueBlocks lab C ∧
          act a '' hexadFiber lab Y C B = hexadFiber lab Y C (act a '' B)) := by
  obtain ⟨inst, -, -, -, -, -, hB6, -, h77, -⟩ := hS.clique_code_steiner_design hC
  refine ⟨inst, ?_⟩
  have h22 : C.ncard = 22 := hS.ncard_eq_of_isSliceMaxClique hC
  have hfib := fun B (hB : B ∈ cliqueBlocks lab C) => hS.hexadFiber_of_mem_cliqueBlocks hC hB
  have h32 : ∀ B ∈ cliqueBlocks lab C, (hexadFiber lab Y C B).ncard = 32 :=
    fun B hB => (hfib B hB).1
  have hU := hS.ncard_biUnion_hexadFiber h32 h77
  set U := ⋃ B ∈ cliqueBlocks lab C, hexadFiber lab Y C B with hUdef
  have hcov : Y = C ∪ U ∪ hexadFiber lab Y C ∅ := by
    apply le_antisymm
    · intro x hxY
      by_cases hxC : x ∈ C
      · exact Or.inl (Or.inl hxC)
      · rcases hS.inter_neighborSet_eq_empty_or_mem hC hxC with h | h
        · exact Or.inr ⟨hxY, hxC, h⟩
        · exact Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨_, h, hxY, hxC, rfl⟩))
    · rintro x ((hx | hx) | hx)
      · exact hC.1.1 hx
      · obtain ⟨B, -, hxB⟩ := Set.mem_iUnion₂.1 hx
        exact hxB.1
      · exact hx.1
  have hdCU : Disjoint C U := by
    rw [Set.disjoint_left]
    intro x hxC hxU
    obtain ⟨B, -, hxB⟩ := Set.mem_iUnion₂.1 hxU
    exact hxB.2.1 hxC
  have hdCΩ : Disjoint C (hexadFiber lab Y C ∅) :=
    Set.disjoint_left.2 fun x hxC hx => hx.2.1 hxC
  have hdUΩ : Disjoint U (hexadFiber lab Y C ∅) := by
    rw [Set.disjoint_left]
    intro x hxU hx
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hxU
    have h6 := (hB6 B hB).2
    rw [← hxB.2.2, hx.2.2, Set.ncard_empty] at h6
    exact absurd h6 (by decide)
  have hYfin := hS.finite
  have hΩ : (hexadFiber lab Y C ∅).ncard = 1024 := by
    have h1 := Set.ncard_union_eq (Disjoint.union_left hdCΩ hdUΩ)
      ((hYfin.subset hC.1.1).union (hYfin.subset (Set.iUnion₂_subset fun B _ x hx => hx.1)))
      (hYfin.subset fun x hx => hx.1)
    rw [Set.ncard_union_eq hdCU (hYfin.subset hC.1.1)
      (hYfin.subset (Set.iUnion₂_subset fun B _ x hx => hx.1)), ← hcov, hS.ncard, h22, hU] at h1
    omega
  refine ⟨fun x _ hxC => hS.inter_neighborSet_eq_empty_or_mem hC hxC, fun B hB => ⟨h32 B hB,
    fun r hr x hx => hS.act_mem_hexadFiber hr hx, (hfib B hB).2.1,
    fun x hx => ((hfib B hB).2.2 x hx).1, ?_⟩, hcov, hdCU, hdCΩ, hdUΩ, ?_, h22, hU, hΩ,
    fun a ha => by rw [hS.image_hexadFiber ha, Set.image_empty], fun a ha B hB =>
      ⟨image_mem_cliqueBlocks hS.lab_act (fun x hx => (ha.2 x).2 hx)
        (setStabPerm act lab Y C ⟨a, ha⟩) (fun _ => rfl) hB, hS.image_hexadFiber ha B⟩⟩
  · obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h32 B hB]; norm_num :
      (hexadFiber lab Y C B).ncard ≠ 0)
    obtain ⟨h1, h2⟩ := (hfib B hB).2.2 x hx
    rw [← h1, h2]
  · intro B _ B' _ hBB'
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hBB' (hx.2.2.symm.trans hx'.2.2)

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
