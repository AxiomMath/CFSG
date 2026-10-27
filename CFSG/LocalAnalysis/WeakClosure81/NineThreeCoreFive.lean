module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeWeylRec

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.ClassicalInvolution.Asc77 Subgroup
open scoped Pointwise commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

private def nine3_permRef (i j : Fin 4) (b : Bool) : Equiv.Perm (Fin 4 × Bool) :=
  Equiv.swap (i, false) (j, b) * Equiv.swap (i, true) (j, !b)

private def nine3_refPerm : Fin 12 → Equiv.Perm (Fin 4 × Bool)
  | 0 => nine3_permRef 0 1 false
  | 1 => nine3_permRef 0 1 true
  | 2 => nine3_permRef 0 2 false
  | 3 => nine3_permRef 0 2 true
  | 4 => nine3_permRef 0 3 false
  | 5 => nine3_permRef 0 3 true
  | 6 => nine3_permRef 1 2 false
  | 7 => nine3_permRef 1 2 true
  | 8 => nine3_permRef 1 3 false
  | 9 => nine3_permRef 1 3 true
  | 10 => nine3_permRef 2 3 false
  | 11 => nine3_permRef 2 3 true

private theorem nine3_refPerm_mem (n : Fin 12) :
    nine3_refPerm n ∈ {σ : Equiv.Perm (Fin 4 × Bool) |
      ∃ (i j : Fin 4) (b : Bool), i ≠ j ∧ σ = nine3_permRef i j b} := by
  fin_cases n <;> exact ⟨_, _, _, by decide, rfl⟩

private def nine3_ref (n : Fin 12) : ↥weylD4 :=
  ⟨nine3_refPerm n, Subgroup.subset_closure (nine3_refPerm_mem n)⟩

private theorem nine3_ref_mem (n : Fin 12) : nine3_ref n ∈ weylD4Refl :=
  nine3_refPerm_mem n

private theorem nine3_refPerm_inj : Function.Injective nine3_refPerm := by
  decide +kernel

private theorem nine3_ref_inj : Function.Injective nine3_ref := fun _ _ h =>
  nine3_refPerm_inj (congrArg Subtype.val h)

private theorem nine3_refPerm_range : ∀ (i j : Fin 4) (b : Bool), i ≠ j →
    ∃ n : Fin 12, nine3_refPerm n = nine3_permRef i j b := by
  decide +kernel

private theorem nine3_ref_surj {x : ↥weylD4} (hx : x ∈ weylD4Refl) :
    ∃ n : Fin 12, nine3_ref n = x := by
  simp only [weylD4Refl, Set.mem_setOf_eq] at hx
  obtain ⟨i, j, b, hij, hxeq⟩ := hx
  obtain ⟨n, hn⟩ := nine3_refPerm_range i j b hij
  exact ⟨n, Subtype.ext (by
    change nine3_refPerm n = (x : Equiv.Perm (Fin 4 × Bool))
    rw [hn, hxeq]
    rfl)⟩

private def nine3_clique : Fin 12 → List (Fin 12)
  | 0 => [0, 1, 10, 11]
  | 1 => [0, 1, 10, 11]
  | 2 => [2, 3, 8, 9]
  | 3 => [2, 3, 8, 9]
  | 4 => [4, 5, 6, 7]
  | 5 => [4, 5, 6, 7]
  | 6 => [4, 5, 6, 7]
  | 7 => [4, 5, 6, 7]
  | 8 => [2, 3, 8, 9]
  | 9 => [2, 3, 8, 9]
  | 10 => [0, 1, 10, 11]
  | 11 => [0, 1, 10, 11]

private theorem nine3_clique_length : ∀ n : Fin 12, (nine3_clique n).length = 4 := by
  decide +kernel

private theorem nine3_clique_nodup : ∀ n : Fin 12, (nine3_clique n).Nodup := by
  decide +kernel

private theorem nine3_clique_mem_of_comm : ∀ m n : Fin 12,
    nine3_ref m * nine3_ref n = nine3_ref n * nine3_ref m → m ∈ nine3_clique n := by
  decide +kernel

private def nine3_negOne : ↥weylD4 :=
  nine3_ref 0 * nine3_ref 1 * nine3_ref 10 * nine3_ref 11

private theorem nine3_clique_prod : ∀ n : Fin 12,
    ((nine3_clique n).map nine3_ref).prod = nine3_negOne := by
  decide +kernel

private theorem nine3_ref_comm_negOne : ∀ n : Fin 12,
    nine3_ref n * nine3_negOne = nine3_negOne * nine3_ref n := by
  decide +kernel

private theorem nine3_ref_closure_top : Subgroup.closure (Set.range nine3_ref) = ⊤ := by
  have hrange : Set.range nine3_ref = weylD4Refl := by
    ext x
    exact ⟨fun hx => by rcases hx with ⟨n, rfl⟩; exact nine3_ref_mem n,
      fun hx => nine3_ref_surj hx⟩
  rw [hrange]
  exact Subgroup.closure_closure_coe_preimage

private theorem nine3_negOne_central : nine3_negOne ∈ Subgroup.center ↥weylD4 := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure (Set.range nine3_ref) := by
    rw [nine3_ref_closure_top]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨n, rfl⟩ := hx
      exact nine3_ref_comm_negOne n
  | one => simp
  | mul x y _ _ ihx ihy =>
      rw [mul_assoc, ihy, ← mul_assoc, ihx, mul_assoc]
  | inv x _ ihx =>
      exact (show Commute x nine3_negOne from ihx).inv_left

theorem nine3OddFrame_four_prod_central {π : Γ →* Equiv.Perm (ZMod 3)} {D : Set Γ}
    (h : Nine3OddFrame 3 4 π D) (hi : Nine3FibreIndep 3 π D) (a : ZMod 3) {l : List Γ}
    (hl : l.Nodup) (hlen : l.length = 4) (hF : ∀ d ∈ l, d ∈ nine3FibreSet π D a) :
    l.prod ∈ Subgroup.center Γ := by
  obtain ⟨e, he⟩ := nine3OddFrame_four_equiv h hi
  have hLnodup : (l.map e).Nodup := List.Nodup.map e.injective hl
  have hLlen : (l.map e).length = 4 := by rw [List.length_map, hlen]
  have hLmem : ∀ x ∈ l.map e, x ∈ weylD4Refl := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    exact (he d).mp (hF d hd).1
  have hLcomm : ∀ x ∈ l.map e, ∀ y ∈ l.map e, Commute x y := by
    intro x hx y hy
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hy
    show e d * e d' = e d' * e d
    rw [← map_mul, ← map_mul,
      h.comm d (hF d hd).1 d' (hF d' hd').1 (by rw [(hF d hd).2, (hF d' hd').2])]
  have hLpairwise : (l.map e).Pairwise Commute :=
    List.pairwise_of_reflexive_of_forall_ne
      (R := Commute) (fun x hx y hy _ => hLcomm x hx y hy)
  have hLpos : 0 < (l.map e).length := by rw [hLlen]; norm_num
  let x0 : ↥weylD4 := (l.map e).get ⟨0, hLpos⟩
  have hx0 : x0 ∈ l.map e := List.get_mem (l.map e) ⟨0, hLpos⟩
  obtain ⟨n, hn⟩ := nine3_ref_surj (hLmem x0 hx0)
  have hMlen : ((nine3_clique n).map nine3_ref).length = 4 := by
    rw [List.length_map, nine3_clique_length n]
  have hMnodup : ((nine3_clique n).map nine3_ref).Nodup :=
    List.Nodup.map nine3_ref_inj (nine3_clique_nodup n)
  have hsubset : (l.map e).toFinset ⊆ ((nine3_clique n).map nine3_ref).toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    obtain ⟨m, hm⟩ := nine3_ref_surj (hLmem x hx)
    have hcommx : Commute (nine3_ref m) (nine3_ref n) := by
      rw [hm, hn]
      exact hLcomm x hx x0 hx0
    exact List.mem_map.mpr ⟨m, nine3_clique_mem_of_comm m n hcommx, hm⟩
  have htoFinset : (l.map e).toFinset = ((nine3_clique n).map nine3_ref).toFinset :=
    Finset.eq_of_subset_of_card_le hsubset (by
      have hM : (((nine3_clique n).map nine3_ref).toFinset).card = 4 := by
        rw [List.card_toFinset, hMnodup.dedup, hMlen]
      have hL : ((l.map e).toFinset).card = 4 := by
        rw [List.card_toFinset, hLnodup.dedup, hLlen]
      rw [hM, hL])
  have hperm : List.Perm (l.map e) ((nine3_clique n).map nine3_ref) :=
    List.perm_of_nodup_nodup_toFinset_eq hLnodup hMnodup htoFinset
  have hLprod : (l.map e).prod = nine3_negOne := by
    rw [List.Perm.prod_eq' hperm hLpairwise, nine3_clique_prod n]
  have hcenter : e l.prod ∈ Subgroup.center ↥weylD4 := by
    rw [map_list_prod e l, hLprod]
    exact nine3_negOne_central
  refine Subgroup.comap_center_le_center e.injective ?_
  rw [Subgroup.mem_comap]
  exact hcenter

end CFSG.LocalAnalysis.WeakClosure81
