module

public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelGen
public import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.SeitzReduction.OmegaPilot
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

private theorem lin_injective : Function.Injective lin :=
  (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 6 ⊕ Fin 6) (ZMod 2)).injective

private theorem lin_genGL_eq {a b c d : Fin 6} {P Q : Finset (Fin 6)}
    (hab : a ≠ b) (hcd : c ≠ d) (h : genMat a b P = genMat c d Q) :
    lin (genGL hab P) = lin (genGL hcd Q) := by
  refine congrArg lin ?_
  apply Units.ext
  rw [coe_genGL, coe_genGL, h]

private theorem commute_genGL {a b c d : Fin 6} {P Q : Finset (Fin 6)}
    (hab : a ≠ b) (hcd : c ≠ d)
    (h : genMat a b P * genMat c d Q = genMat c d Q * genMat a b P) :
    lin (genGL hab P) * lin (genGL hcd Q) = lin (genGL hcd Q) * lin (genGL hab P) := by
  rw [← map_mul, ← map_mul]
  refine congrArg lin ?_
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_genGL, coe_genGL, h]

private theorem closure_commute {G : Type*} [Group G] {S T : Set G}
    (h : ∀ x ∈ S, ∀ y ∈ T, x * y = y * x)
    {x y : G} (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure T) :
    x * y = y * x := by
  have hT : Subgroup.closure T ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro y hy
    change y ∈ Subgroup.centralizer S
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact h x hx y hy
  have hS : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    change x ∈ Subgroup.centralizer (Subgroup.closure T)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.1 (hT hy)) x hx).symm
  exact ((Subgroup.mem_centralizer_iff.1 (hS hx)) y hy).symm

private theorem rootL_commute {a b c d : Fin 6} {P Q : Finset (Fin 6)}
    (hab : a ≠ b) (hcd : c ≠ d)
    (h1 : genMat a b P * genMat c d Q = genMat c d Q * genMat a b P)
    (h2 : genMat a b P * genMat d c Q = genMat d c Q * genMat a b P)
    (h3 : genMat b a P * genMat c d Q = genMat c d Q * genMat b a P)
    (h4 : genMat b a P * genMat d c Q = genMat d c Q * genMat b a P)
    {x y : V12 ≃ₗ[ZMod 2] V12} (hx : x ∈ rootL {a, b} P)
    (hy : y ∈ rootL {c, d} Q) : x * y = y * x := by
  rw [rootL_eq_closure hab P] at hx
  rw [rootL_eq_closure hcd Q] at hy
  refine closure_commute ?_ hx hy
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact commute_genGL hab hcd h1
  · exact commute_genGL hab hcd.symm h2
  · exact commute_genGL hab.symm hcd h3
  · exact commute_genGL hab.symm hcd.symm h4

private theorem rootL_swap_flip {a b : Fin 6} (hab : a ≠ b)
    (h1 : genMat a b {a} = genMat b a {b}) (h2 : genMat b a {a} = genMat a b {b}) :
    rootL {a, b} {a} = rootL {a, b} {b} := by
  rw [rootL_eq_closure hab {a}, rootL_eq_closure hab {b}]
  have e1 : lin (genGL hab {a}) = lin (genGL hab.symm {b}) := lin_genGL_eq hab hab.symm h1
  have e2 : lin (genGL hab.symm {a}) = lin (genGL hab {b}) := lin_genGL_eq hab.symm hab h2
  rw [e1, e2, Set.pair_comm]

private theorem node_zero : node 0 = rootL {0, 1} ∅ := by
  rw [node, show plusNodeSet 6 0 = {0, 1} by decide,
    show plusNodeFlip 6 0 = ∅ by decide]

private theorem node_one : node 1 = rootL {1, 2} ∅ := by
  rw [node, show plusNodeSet 6 1 = {1, 2} by decide,
    show plusNodeFlip 6 1 = ∅ by decide]

private theorem node_two : node 2 = rootL {2, 3} ∅ := by
  rw [node, show plusNodeSet 6 2 = {2, 3} by decide,
    show plusNodeFlip 6 2 = ∅ by decide]

private theorem node_three : node 3 = rootL {3, 4} ∅ := by
  rw [node, show plusNodeSet 6 3 = {3, 4} by decide,
    show plusNodeFlip 6 3 = ∅ by decide]

private theorem node_four : node 4 = rootL {4, 5} ∅ := by
  rw [node, show plusNodeSet 6 4 = {4, 5} by decide,
    show plusNodeFlip 6 4 = ∅ by decide]

private theorem node_five : node 5 = rootL {4, 5} {5} := by
  rw [node, show plusNodeSet 6 5 = {4, 5} by decide,
    show plusNodeFlip 6 5 = {5} by decide]

private theorem rootL_eq_of_disjoint {B P : Finset (Fin 6)} (h : Disjoint B P) :
    rootL B P = rootL B ∅ := by
  rw [rootL, rootL, flipGL_empty, map_conj_one_eq,
    map_flipGL_siegelBlockGL_of_disjoint (K := ZMod 2) h]

private theorem rootL_empty_map_conj_flipGL (B Q : Finset (Fin 6)) :
    (rootL B ∅).map (MulAut.conj (lin (flipGL (ZMod 2) Q))).toMonoidHom = rootL B Q := by
  have hL : rootL B ∅ = (siegelBlockGL (ZMod 2) B).map lin := by
    rw [rootL, flipGL_empty, map_conj_one_eq]
  have hfun : (MulAut.conj (lin (flipGL (ZMod 2) Q))).toMonoidHom.comp lin =
      lin.comp (MulAut.conj (flipGL (ZMod 2) Q)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  rw [hL, rootL, Subgroup.map_map, hfun, Subgroup.map_map]

private theorem commute_rootL_of_disjoint {B B' P Q : Finset (Fin 6)}
    (h : Disjoint B B') {x y : V12 ≃ₗ[ZMod 2] V12}
    (hx : x ∈ rootL B P) (hy : y ∈ rootL B' Q) : x * y = y * x := by
  rw [rootL] at hx hy
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg lin (commute_of_mem_flip_siegelBlockGL (F := ZMod 2) h hx' hy').eq

theorem node_commute {i j : Fin 6} (hij : i ≠ j) (h1 : ¬ edgeD 6 i j)
    (h2 : ¬ edgeD 6 j i) : ∀ a ∈ node i, ∀ b ∈ node j, a * b = b * a := by
  by_cases hf1 : i.val + 2 = 6 ∧ j.val + 1 = 6
  · have hi : i = 4 := Fin.ext (by have := i.isLt; omega)
    have hj : j = 5 := Fin.ext (by have := j.isLt; omega)
    subst hi
    subst hj
    intro a ha b hb
    rw [node_four] at ha
    rw [node_five] at hb
    exact rootL_commute (a := 4) (b := 5) (c := 4) (d := 5) (P := ∅) (Q := {5})
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hb
  by_cases hf2 : j.val + 2 = 6 ∧ i.val + 1 = 6
  · have hi : i = 5 := Fin.ext (by have := i.isLt; omega)
    have hj : j = 4 := Fin.ext (by have := j.isLt; omega)
    subst hi
    subst hj
    intro a ha b hb
    rw [node_five] at ha
    rw [node_four] at hb
    exact rootL_commute (a := 4) (b := 5) (c := 4) (d := 5) (P := {5}) (Q := ∅)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hb
  · intro a ha b hb
    rw [node_eq_map_siegelNode] at ha hb
    rcases ha with ⟨x, hx, rfl⟩
    rcases hb with ⟨y, hy, rfl⟩
    rw [siegelNode] at hx hy
    rw [← map_mul, ← map_mul]
    exact congrArg lin (commute_of_mem_flip_siegelBlockGL
      (disjoint_plusNodeSet hij h1 h2 hf1 hf2) hx hy).eq

theorem node_pair {i j : Fin 6} (h : edgeD 6 i j) :
    ∃ W, LinearBlockStandardPair (ZMod 2) W (node i) (node j) := by
  obtain ⟨θ, hker, h12, h23⟩ := exists_theta_siegelNode (K := ZMod 2) (n := 6) h
  refine ⟨(θ.range).map lin, lin.comp θ, 1, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.range_comp]
  · rw [MonoidHom.ker_comp_of_injective θ lin lin_injective]
    exact hker
  · rw [map_conj_one_inv_eq', ← Subgroup.map_map, h12, node_eq_map_siegelNode]
  · rw [map_conj_one_inv_eq', ← Subgroup.map_map, h23, node_eq_map_siegelNode]

private theorem flip0_eq_rootL : flip0 = rootL {0, 1} {0} := by
  rw [flip0]
  exact (rootL_swap_flip (a := 0) (b := 1) (by decide) (by decide) (by decide)).symm

private theorem flip2_eq_rootL : flip2 = rootL {2, 3} {2} := by
  rw [flip2]
  exact (rootL_swap_flip (a := 2) (b := 3) (by decide) (by decide) (by decide)).symm

theorem flip0_pair_node1 : ∃ W, LinearBlockStandardPair (ZMod 2) W flip0 (node 1) := by
  obtain ⟨W, hW⟩ := node_pair (i := 0) (j := 1) (by decide)
  set φ := (MulAut.conj (lin (flipGL (ZMod 2) {0}))).toMonoidHom
  refine ⟨W.map φ, ?_⟩
  have h := CFSG.ClassicalInvolution.Models.linearBlockStandardPair_map (K := ZMod 2) hW φ
    (MulAut.conj (lin (flipGL (ZMod 2) {0}))).injective
  have h0 : (node 0).map φ = flip0 := by
    rw [node_zero, rootL_empty_map_conj_flipGL, flip0_eq_rootL]
  have h1 : (node 1).map φ = node 1 := by
    rw [node_one, rootL_empty_map_conj_flipGL,
      rootL_eq_of_disjoint (B := {1, 2}) (P := {0}) (by decide)]
  simpa only [h0, h1] using h

theorem flip2_pair_node1 : ∃ W, LinearBlockStandardPair (ZMod 2) W (node 1) flip2 := by
  obtain ⟨W, hW⟩ := node_pair (i := 1) (j := 2) (by decide)
  set φ := (MulAut.conj (lin (flipGL (ZMod 2) {3}))).toMonoidHom
  refine ⟨W.map φ, ?_⟩
  have h := CFSG.ClassicalInvolution.Models.linearBlockStandardPair_map (K := ZMod 2) hW φ
    (MulAut.conj (lin (flipGL (ZMod 2) {3}))).injective
  have h1 : (node 1).map φ = node 1 := by
    rw [node_one, rootL_empty_map_conj_flipGL,
      rootL_eq_of_disjoint (B := {1, 2}) (P := {3}) (by decide)]
  have h2 : (node 2).map φ = flip2 := by
    rw [node_two, rootL_empty_map_conj_flipGL, flip2]
  simpa only [h1, h2] using h

theorem flip2_pair_node3 : ∃ W, LinearBlockStandardPair (ZMod 2) W flip2 (node 3) := by
  obtain ⟨W, hW⟩ := node_pair (i := 2) (j := 3) (by decide)
  set φ := (MulAut.conj (lin (flipGL (ZMod 2) {2}))).toMonoidHom
  refine ⟨W.map φ, ?_⟩
  have h := CFSG.ClassicalInvolution.Models.linearBlockStandardPair_map (K := ZMod 2) hW φ
    (MulAut.conj (lin (flipGL (ZMod 2) {2}))).injective
  have h1 : (node 2).map φ = flip2 := by
    rw [node_two, rootL_empty_map_conj_flipGL, flip2_eq_rootL]
  have h2 : (node 3).map φ = node 3 := by
    rw [node_three, rootL_empty_map_conj_flipGL,
      rootL_eq_of_disjoint (B := {3, 4}) (P := {2}) (by decide)]
  simpa only [h1, h2] using h

private theorem disjoint_planeSet_zero_one {j : Fin 6} (h0 : j ≠ 0) (h1 : j ≠ 1) :
    Disjoint ({0, 1} : Finset (Fin 6)) (plusNodeSet 6 j) := by
  have hj0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hj1 : j.val ≠ 1 := fun h => h1 (Fin.ext h)
  have hjlt := j.isLt
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, mem_plusNodeSet] at hx
  obtain ⟨hx | hx, hxj⟩ := hx
  · rw [hx] at hxj
    omega
  · rw [hx] at hxj
    omega

private theorem disjoint_planeSet_two_three {j : Fin 6} (h1 : j ≠ 1) (h2 : j ≠ 2)
    (h3 : j ≠ 3) : Disjoint ({2, 3} : Finset (Fin 6)) (plusNodeSet 6 j) := by
  have hj1 : j.val ≠ 1 := fun h => h1 (Fin.ext h)
  have hj2 : j.val ≠ 2 := fun h => h2 (Fin.ext h)
  have hj3 : j.val ≠ 3 := fun h => h3 (Fin.ext h)
  have hjlt := j.isLt
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, mem_plusNodeSet] at hx
  obtain ⟨hx | hx, hxj⟩ := hx
  · rw [hx] at hxj
    omega
  · rw [hx] at hxj
    omega

theorem flip0_commute_node {j : Fin 6} (hj : j ≠ 1) :
    ∀ a ∈ flip0, ∀ b ∈ node j, a * b = b * a := by
  by_cases hj0 : j = 0
  · subst hj0
    intro a ha b hb
    rw [node_zero] at hb
    rw [flip0] at ha
    exact rootL_commute (a := 0) (b := 1) (c := 0) (d := 1) (P := {1}) (Q := ∅)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hb
  · intro a ha b hb
    rw [flip0] at ha
    rw [node] at hb
    exact commute_rootL_of_disjoint (B := {0, 1})
      (disjoint_planeSet_zero_one hj0 hj) ha hb

theorem flip2_commute_node {j : Fin 6} (hj1 : j ≠ 1) (hj3 : j ≠ 3) :
    ∀ a ∈ flip2, ∀ b ∈ node j, a * b = b * a := by
  by_cases hj2 : j = 2
  · subst hj2
    intro a ha b hb
    rw [node_two] at hb
    rw [flip2] at ha
    exact rootL_commute (a := 2) (b := 3) (c := 2) (d := 3) (P := {3}) (Q := ∅)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hb
  · intro a ha b hb
    rw [flip2] at ha
    rw [node] at hb
    exact commute_rootL_of_disjoint (B := {2, 3})
      (disjoint_planeSet_two_three hj1 hj2 hj3) ha hb

theorem flip0_commute_flip2 : ∀ a ∈ flip0, ∀ b ∈ flip2, a * b = b * a := by
  intro a ha b hb
  rw [flip0] at ha
  rw [flip2] at hb
  exact commute_rootL_of_disjoint (B := {0, 1}) (B' := {2, 3}) (P := {1}) (Q := {3})
    (by decide) ha hb

end CFSG.StandardType.FrameRoute.FS81.D6M
