module

public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelTorusAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.SeitzReduction.OmegaPilot CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
open QuadraticMap
open scoped Matrix

theorem isFrame_frameList : IsFrame Q12 frameList := by
  rw [show frameList = [framePair 0, framePair 1, framePair 2, framePair 3, framePair 4,
    framePair 5] from rfl]
  refine IsFrame.cons (minusPair_framePair 0)
    (pairPerp_of_mem_map (l := [1, 2, 3, 4, 5]) (by decide)) ?_
  refine IsFrame.cons (minusPair_framePair 1)
    (pairPerp_of_mem_map (l := [2, 3, 4, 5]) (by decide)) ?_
  refine IsFrame.cons (minusPair_framePair 2)
    (pairPerp_of_mem_map (l := [3, 4, 5]) (by decide)) ?_
  refine IsFrame.cons (minusPair_framePair 3)
    (pairPerp_of_mem_map (l := [4, 5]) (by decide)) ?_
  refine IsFrame.cons (minusPair_framePair 4)
    (pairPerp_of_mem_map (l := [5]) (by decide)) ?_
  exact IsFrame.cons (minusPair_framePair 5) (pairPerp_of_mem_map (l := []) (by decide))
    IsFrame.nil

theorem frameRot_pow_three (i : Fin 6) : frameRot i ^ 3 = 1 :=
  rot_pow_three (isFrame_frameList.pair _ (framePair_mem_frameList i))

private theorem flip0_eq : flip0 = rootL ({0, 1} : Finset (Fin 6)) {1} := rfl

private theorem flip2_eq : flip2 = rootL ({2, 3} : Finset (Fin 6)) {3} := rfl

theorem frameRot01_mem :
    frameRot 0 * frameRot 1 ∈ node 0 ∧ frameRot 0 * (frameRot 1)⁻¹ ∈ flip0 := by
  constructor
  · simp only [frameRot_eq_lin_rotGL, ← map_mul, node_zero,
      rootL_eq_closure (a := 0) (b := 1) (by decide) (∅ : Finset (Fin 6))]
    exact lin_mem_closure_of_mat (a := 0) (b := 1) (by decide) (∅ : Finset (Fin 6))
      (M := rotMat 0 * rotMat 1) (by decide +kernel)
      (by rw [Units.val_mul, coe_rotGL, coe_rotGL])
  · simp only [frameRot_eq_lin_rotGL, ← map_inv, ← map_mul, flip0_eq,
      rootL_eq_closure (a := 0) (b := 1) (by decide) ({1} : Finset (Fin 6))]
    exact lin_mem_closure_of_mat (a := 0) (b := 1) (by decide) ({1} : Finset (Fin 6))
      (M := rotMat 0 * (rotMat 1 * rotMat 1)) (by decide +kernel)
      (by rw [Units.val_mul, coe_rotGL, coe_rotGL_inv])

theorem frameRot23_mem :
    frameRot 2 * frameRot 3 ∈ node 2 ∧ frameRot 2 * (frameRot 3)⁻¹ ∈ flip2 := by
  constructor
  · simp only [frameRot_eq_lin_rotGL, ← map_mul, node_two,
      rootL_eq_closure (a := 2) (b := 3) (by decide) (∅ : Finset (Fin 6))]
    exact lin_mem_closure_of_mat (a := 2) (b := 3) (by decide) (∅ : Finset (Fin 6))
      (M := rotMat 2 * rotMat 3) (by decide +kernel)
      (by rw [Units.val_mul, coe_rotGL, coe_rotGL])
  · simp only [frameRot_eq_lin_rotGL, ← map_inv, ← map_mul, flip2_eq,
      rootL_eq_closure (a := 2) (b := 3) (by decide) ({3} : Finset (Fin 6))]
    exact lin_mem_closure_of_mat (a := 2) (b := 3) (by decide) ({3} : Finset (Fin 6))
      (M := rotMat 2 * (rotMat 3 * rotMat 3)) (by decide +kernel)
      (by rw [Units.val_mul, coe_rotGL, coe_rotGL_inv])

theorem frameRot45_mem :
    frameRot 4 * frameRot 5 ∈ node 4 ∧ frameRot 4 * (frameRot 5)⁻¹ ∈ node 5 := by
  constructor
  · simp only [frameRot_eq_lin_rotGL, ← map_mul, node_four,
      rootL_eq_closure (a := 4) (b := 5) (by decide) (∅ : Finset (Fin 6))]
    exact lin_mem_closure_of_mat (a := 4) (b := 5) (by decide) (∅ : Finset (Fin 6))
      (M := rotMat 4 * rotMat 5) (by decide +kernel)
      (by rw [Units.val_mul, coe_rotGL, coe_rotGL])
  · simp only [frameRot_eq_lin_rotGL, ← map_inv, ← map_mul, node_five,
      rootL_eq_closure (a := 4) (b := 5) (by decide) ({5} : Finset (Fin 6))]
    exact lin_mem_closure_of_mat (a := 4) (b := 5) (by decide) ({5} : Finset (Fin 6))
      (M := rotMat 4 * (rotMat 5 * rotMat 5)) (by decide +kernel)
      (by rw [Units.val_mul, coe_rotGL, coe_rotGL_inv])

theorem frameRot_conj_mem (i : Fin 6) {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hX : X = node 0 ∨ X = node 2 ∨ X = node 4 ∨ X = node 5 ∨ X = flip0 ∨ X = flip2) :
    ∀ z ∈ X, frameRot i * z * (frameRot i)⁻¹ ∈ X := by
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [frameRot_conj_node0 i, frameRot_conj_node2 i, frameRot_conj_node4 i,
    frameRot_conj_node5 i, frameRot_conj_flip0 i, frameRot_conj_flip2 i]

private theorem genGL_mul_ne_one_of_mat {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6))
    (h : genMat a b P * genMat b a P ≠ 1) : genGL hab P * genGL hab.symm P ≠ 1 := by
  intro hu
  apply h
  have := congrArg (fun u : GL (Fin 6 ⊕ Fin 6) (ZMod 2) =>
    (u : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2))) hu
  simpa [Units.val_mul, coe_genGL] using this

private theorem genGL_three_ne_one_of_mat {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6))
    (h : genMat a b P * genMat b a P * genMat a b P ≠ 1) :
    genGL hab P * genGL hab.symm P * genGL hab P ≠ 1 := by
  intro hu
  apply h
  have := congrArg (fun u : GL (Fin 6 ⊕ Fin 6) (ZMod 2) =>
    (u : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2))) hu
  simpa [Units.val_mul, coe_genGL] using this

private theorem word_three_mem {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6)) :
    lin (genGL hab P * genGL hab.symm P * genGL hab P) ∈ rootL {a, b} P := by
  rw [rootL_eq_closure hab P, map_mul, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    (Subgroup.subset_closure (Set.mem_insert _ _))

theorem exists_inv_closure {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hX : X = node 0 ∨ X = node 2 ∨ X = node 4 ∨ X = node 5 ∨ X = flip0 ∨ X = flip2)
    {h : V12 ≃ₗ[ZMod 2] V12} (hh : h ∈ X) (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1) :
    ∃ s ∈ X, s * s = 1 ∧ s * h * s⁻¹ = h⁻¹ ∧ X = Subgroup.closure {h, s} := by
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [node_zero, rootL_eq_closure (a := 0) (b := 1) (by decide) (∅ : Finset (Fin 6))]
      at hh ⊢
    exact exists_inv_of_mem_closure_pair
      (g₁ := lin (genGL (by decide : (0 : Fin 6) ≠ 1) (∅ : Finset (Fin 6))))
      (g₂ := lin (genGL (by decide : (0 : Fin 6) ≠ 1).symm (∅ : Finset (Fin 6))))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_pow_three (by rw [coe_genGL, coe_genGL]; decide +kernel))
      (by rw [← map_mul]
          exact lin_ne_one (genGL_mul_ne_one_of_mat (by decide) (∅ : Finset (Fin 6))
            (by decide +kernel)))
      hh hh1 hh3
  · rw [node_two, rootL_eq_closure (a := 2) (b := 3) (by decide) (∅ : Finset (Fin 6))]
      at hh ⊢
    exact exists_inv_of_mem_closure_pair
      (g₁ := lin (genGL (by decide : (2 : Fin 6) ≠ 3) (∅ : Finset (Fin 6))))
      (g₂ := lin (genGL (by decide : (2 : Fin 6) ≠ 3).symm (∅ : Finset (Fin 6))))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_pow_three (by rw [coe_genGL, coe_genGL]; decide +kernel))
      (by rw [← map_mul]
          exact lin_ne_one (genGL_mul_ne_one_of_mat (by decide) (∅ : Finset (Fin 6))
            (by decide +kernel)))
      hh hh1 hh3
  · rw [node_four, rootL_eq_closure (a := 4) (b := 5) (by decide) (∅ : Finset (Fin 6))]
      at hh ⊢
    exact exists_inv_of_mem_closure_pair
      (g₁ := lin (genGL (by decide : (4 : Fin 6) ≠ 5) (∅ : Finset (Fin 6))))
      (g₂ := lin (genGL (by decide : (4 : Fin 6) ≠ 5).symm (∅ : Finset (Fin 6))))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_pow_three (by rw [coe_genGL, coe_genGL]; decide +kernel))
      (by rw [← map_mul]
          exact lin_ne_one (genGL_mul_ne_one_of_mat (by decide) (∅ : Finset (Fin 6))
            (by decide +kernel)))
      hh hh1 hh3
  · rw [node_five, rootL_eq_closure (a := 4) (b := 5) (by decide) ({5} : Finset (Fin 6))]
      at hh ⊢
    exact exists_inv_of_mem_closure_pair
      (g₁ := lin (genGL (by decide : (4 : Fin 6) ≠ 5) ({5} : Finset (Fin 6))))
      (g₂ := lin (genGL (by decide : (4 : Fin 6) ≠ 5).symm ({5} : Finset (Fin 6))))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_pow_three (by rw [coe_genGL, coe_genGL]; decide +kernel))
      (by rw [← map_mul]
          exact lin_ne_one (genGL_mul_ne_one_of_mat (by decide) ({5} : Finset (Fin 6))
            (by decide +kernel)))
      hh hh1 hh3
  · rw [flip0_eq, rootL_eq_closure (a := 0) (b := 1) (by decide) ({1} : Finset (Fin 6))]
      at hh ⊢
    exact exists_inv_of_mem_closure_pair
      (g₁ := lin (genGL (by decide : (0 : Fin 6) ≠ 1) ({1} : Finset (Fin 6))))
      (g₂ := lin (genGL (by decide : (0 : Fin 6) ≠ 1).symm ({1} : Finset (Fin 6))))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_pow_three (by rw [coe_genGL, coe_genGL]; decide +kernel))
      (by rw [← map_mul]
          exact lin_ne_one (genGL_mul_ne_one_of_mat (by decide) ({1} : Finset (Fin 6))
            (by decide +kernel)))
      hh hh1 hh3
  · rw [flip2_eq, rootL_eq_closure (a := 2) (b := 3) (by decide) ({3} : Finset (Fin 6))]
      at hh ⊢
    exact exists_inv_of_mem_closure_pair
      (g₁ := lin (genGL (by decide : (2 : Fin 6) ≠ 3) ({3} : Finset (Fin 6))))
      (g₂ := lin (genGL (by decide : (2 : Fin 6) ≠ 3).symm ({3} : Finset (Fin 6))))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_mul_self (by rw [coe_genGL]; decide +kernel))
      (lin_pow_three (by rw [coe_genGL, coe_genGL]; decide +kernel))
      (by rw [← map_mul]
          exact lin_ne_one (genGL_mul_ne_one_of_mat (by decide) ({3} : Finset (Fin 6))
            (by decide +kernel)))
      hh hh1 hh3

@[expose] noncomputable def wm2 : V12 ≃ₗ[ZMod 2] V12 :=
  lin (genGL (by decide : (2 : Fin 6) ≠ 3) (∅ : Finset (Fin 6)) *
    genGL (by decide : (2 : Fin 6) ≠ 3).symm (∅ : Finset (Fin 6)) *
    genGL (by decide : (2 : Fin 6) ≠ 3) (∅ : Finset (Fin 6)))

@[expose] noncomputable def wc0 : V12 ≃ₗ[ZMod 2] V12 :=
  lin (genGL (by decide : (2 : Fin 6) ≠ 3) ({3} : Finset (Fin 6)) *
    genGL (by decide : (2 : Fin 6) ≠ 3).symm ({3} : Finset (Fin 6)) *
    genGL (by decide : (2 : Fin 6) ≠ 3) ({3} : Finset (Fin 6)))

@[expose] noncomputable def wmu0 : V12 ≃ₗ[ZMod 2] V12 :=
  lin (genGL (by decide : (0 : Fin 6) ≠ 1) (∅ : Finset (Fin 6)) *
    genGL (by decide : (0 : Fin 6) ≠ 1).symm (∅ : Finset (Fin 6)) *
    genGL (by decide : (0 : Fin 6) ≠ 1) (∅ : Finset (Fin 6)))

@[expose] noncomputable def wphi0 : V12 ≃ₗ[ZMod 2] V12 :=
  lin (genGL (by decide : (0 : Fin 6) ≠ 1) ({1} : Finset (Fin 6)) *
    genGL (by decide : (0 : Fin 6) ≠ 1).symm ({1} : Finset (Fin 6)) *
    genGL (by decide : (0 : Fin 6) ≠ 1) ({1} : Finset (Fin 6)))

@[expose] noncomputable def wmu4 : V12 ≃ₗ[ZMod 2] V12 :=
  lin (genGL (by decide : (4 : Fin 6) ≠ 5) (∅ : Finset (Fin 6)) *
    genGL (by decide : (4 : Fin 6) ≠ 5).symm (∅ : Finset (Fin 6)) *
    genGL (by decide : (4 : Fin 6) ≠ 5) (∅ : Finset (Fin 6)))

@[expose] noncomputable def wmu5 : V12 ≃ₗ[ZMod 2] V12 :=
  lin (genGL (by decide : (4 : Fin 6) ≠ 5) ({5} : Finset (Fin 6)) *
    genGL (by decide : (4 : Fin 6) ≠ 5).symm ({5} : Finset (Fin 6)) *
    genGL (by decide : (4 : Fin 6) ≠ 5) ({5} : Finset (Fin 6)))

theorem wm2_mem : wm2 ∈ node 2 := by
  simp only [wm2, node_two]
  exact word_three_mem (by decide) (∅ : Finset (Fin 6))

theorem wc0_mem : wc0 ∈ flip2 := by
  simp only [wc0]
  exact word_three_mem (by decide) ({3} : Finset (Fin 6))

theorem wc0_ne_one : wc0 ≠ 1 := by
  simp only [wc0]
  exact lin_ne_one (genGL_three_ne_one_of_mat (by decide) ({3} : Finset (Fin 6))
    (by decide +kernel))

theorem wmu0_mem : wmu0 ∈ node 0 := by
  simp only [wmu0, node_zero]
  exact word_three_mem (by decide) (∅ : Finset (Fin 6))

theorem wphi0_mem : wphi0 ∈ flip0 := by
  simp only [wphi0]
  exact word_three_mem (by decide) ({1} : Finset (Fin 6))

theorem wmu4_mem : wmu4 ∈ node 4 := by
  simp only [wmu4, node_four]
  exact word_three_mem (by decide) (∅ : Finset (Fin 6))

theorem wmu5_mem : wmu5 ∈ node 5 := by
  simp only [wmu5, node_five]
  exact word_three_mem (by decide) ({5} : Finset (Fin 6))

private theorem wmu0_wphi0 :
    wmu0 * wphi0 = lin (flipGL (ZMod 2) ({0, 1} : Finset (Fin 6))) := by
  simp only [wmu0, wphi0]
  rw [← map_mul]
  exact congrArg lin (by
    apply Units.ext
    simp only [Units.val_mul, genMat_word_mul, coe_flipGL]
    decide +kernel)

private theorem wm2_wc0 : wm2 * wc0 = lin (flipGL (ZMod 2) ({2, 3} : Finset (Fin 6))) := by
  simp only [wm2, wc0]
  rw [← map_mul]
  exact congrArg lin (by
    apply Units.ext
    simp only [Units.val_mul, genMat_word_mul, coe_flipGL]
    decide +kernel)

private theorem wmu4_wmu5 :
    wmu4 * wmu5 = lin (flipGL (ZMod 2) ({4, 5} : Finset (Fin 6))) := by
  simp only [wmu4, wmu5]
  rw [← map_mul]
  exact congrArg lin (by
    apply Units.ext
    simp only [Units.val_mul, genMat_word_mul, coe_flipGL]
    decide +kernel)

private theorem node_one : node 1 = rootL ({1, 2} : Finset (Fin 6)) ∅ := by
  unfold node
  rw [show plusNodeSet 6 1 = ({1, 2} : Finset (Fin 6)) from by decide,
    show plusNodeFlip 6 1 = (∅ : Finset (Fin 6)) from by decide]

private theorem node_three : node 3 = rootL ({3, 4} : Finset (Fin 6)) ∅ := by
  unfold node
  rw [show plusNodeSet 6 3 = ({3, 4} : Finset (Fin 6)) from by decide,
    show plusNodeFlip 6 3 = (∅ : Finset (Fin 6)) from by decide]

theorem witness_node1 : ∀ z ∈ node 1,
    (wmu0 * wphi0 * wm2 * wc0) * z * (wmu0 * wphi0 * wm2 * wc0)⁻¹ ∈ node 1 := by
  have hw : wmu0 * wphi0 * wm2 * wc0 =
      lin (flipGL (ZMod 2) ({0, 1, 2, 3} : Finset (Fin 6))) := by
    rw [show wmu0 * wphi0 * wm2 * wc0 = (wmu0 * wphi0) * (wm2 * wc0) by
        rw [mul_assoc (wmu0 * wphi0) wm2 wc0],
      wmu0_wphi0, wm2_wc0, ← map_mul]
    exact congrArg lin (by
      apply Units.ext
      simp only [Units.val_mul, coe_flipGL]
      decide +kernel)
  intro z hz
  rw [node_one, rootL_eq_closure (a := 1) (b := 2) (by decide)
    (∅ : Finset (Fin 6))] at hz
  rw [hw, node_one, rootL_eq_closure (a := 1) (b := 2) (by decide)
    (∅ : Finset (Fin 6))]
  refine CFSG.Glauberman.conj_mem_closure
    (lin (flipGL (ZMod 2) ({0, 1, 2, 3} : Finset (Fin 6)))) z hz ?_
  intro w hwmem
  rcases hwmem with rfl | rfl
  · have hid : flipGL (ZMod 2) ({0, 1, 2, 3} : Finset (Fin 6)) *
        genGL (by decide : (1 : Fin 6) ≠ 2) (∅ : Finset (Fin 6)) *
        (flipGL (ZMod 2) ({0, 1, 2, 3} : Finset (Fin 6)))⁻¹ =
        genGL (by decide : (1 : Fin 6) ≠ 2).symm (∅ : Finset (Fin 6)) := by
      apply Units.ext
      simp only [flipGL_inv, Units.val_mul, Units.val_one, coe_genGL, coe_flipGL]
      decide +kernel
    rw [← map_inv, ← map_mul, ← map_mul, hid]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · have hid : flipGL (ZMod 2) ({0, 1, 2, 3} : Finset (Fin 6)) *
        genGL (by decide : (1 : Fin 6) ≠ 2).symm (∅ : Finset (Fin 6)) *
        (flipGL (ZMod 2) ({0, 1, 2, 3} : Finset (Fin 6)))⁻¹ =
        genGL (by decide : (1 : Fin 6) ≠ 2) (∅ : Finset (Fin 6)) := by
      apply Units.ext
      simp only [flipGL_inv, Units.val_mul, Units.val_one, coe_genGL, coe_flipGL]
      decide +kernel
    rw [← map_inv, ← map_mul, ← map_mul, hid]
    exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem witness_node3 : ∀ z ∈ node 3,
    (wmu4 * wmu5 * wm2 * wc0) * z * (wmu4 * wmu5 * wm2 * wc0)⁻¹ ∈ node 3 := by
  have hw : wmu4 * wmu5 * wm2 * wc0 =
      lin (flipGL (ZMod 2) ({2, 3, 4, 5} : Finset (Fin 6))) := by
    rw [show wmu4 * wmu5 * wm2 * wc0 = (wmu4 * wmu5) * (wm2 * wc0) by
        rw [mul_assoc (wmu4 * wmu5) wm2 wc0],
      wmu4_wmu5, wm2_wc0, ← map_mul]
    exact congrArg lin (by
      apply Units.ext
      simp only [Units.val_mul, coe_flipGL]
      decide +kernel)
  intro z hz
  rw [node_three, rootL_eq_closure (a := 3) (b := 4) (by decide)
    (∅ : Finset (Fin 6))] at hz
  rw [hw, node_three, rootL_eq_closure (a := 3) (b := 4) (by decide)
    (∅ : Finset (Fin 6))]
  refine CFSG.Glauberman.conj_mem_closure
    (lin (flipGL (ZMod 2) ({2, 3, 4, 5} : Finset (Fin 6)))) z hz ?_
  intro w hwmem
  rcases hwmem with rfl | rfl
  · have hid : flipGL (ZMod 2) ({2, 3, 4, 5} : Finset (Fin 6)) *
        genGL (by decide : (3 : Fin 6) ≠ 4) (∅ : Finset (Fin 6)) *
        (flipGL (ZMod 2) ({2, 3, 4, 5} : Finset (Fin 6)))⁻¹ =
        genGL (by decide : (3 : Fin 6) ≠ 4).symm (∅ : Finset (Fin 6)) := by
      apply Units.ext
      simp only [flipGL_inv, Units.val_mul, Units.val_one, coe_genGL, coe_flipGL]
      decide +kernel
    rw [← map_inv, ← map_mul, ← map_mul, hid]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · have hid : flipGL (ZMod 2) ({2, 3, 4, 5} : Finset (Fin 6)) *
        genGL (by decide : (3 : Fin 6) ≠ 4).symm (∅ : Finset (Fin 6)) *
        (flipGL (ZMod 2) ({2, 3, 4, 5} : Finset (Fin 6)))⁻¹ =
        genGL (by decide : (3 : Fin 6) ≠ 4) (∅ : Finset (Fin 6)) := by
      apply Units.ext
      simp only [flipGL_inv, Units.val_mul, Units.val_one, coe_genGL, coe_flipGL]
      decide +kernel
    rw [← map_inv, ← map_mul, ← map_mul, hid]
    exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem witness_plane : ∀ v ∈ planeSpan ({2} : Finset (Fin 6)),
    (wm2 * wc0) v ∈ planeSpan ({2} : Finset (Fin 6)) := by
  intro v hv
  rw [wm2_wc0]
  rw [mem_planeSpan] at hv ⊢
  intro i hi
  simp only [lin, MulEquiv.coe_toMonoidHom, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
    coe_flipGL, Matrix.permMatrix_mulVec, Function.comp_apply]
  by_cases h : i = 3
  · subst h
    have h3 : (3 : Fin 6) ∉ ({2} : Finset (Fin 6)) := by decide
    simp [flipPerm_apply, flipPermFun, (hv 3 h3).1, (hv 3 h3).2]
  · have hi2 : i ∉ ({2, 3} : Finset (Fin 6)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨by simpa using hi, h⟩
    simp [flipPerm_apply, flipPermFun, hi2, (hv i hi).1, (hv i hi).2]

end CFSG.StandardType.FrameRoute.FS81.D6M
