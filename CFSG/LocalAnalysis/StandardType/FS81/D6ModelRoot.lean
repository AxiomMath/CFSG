module

public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelRootAux2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalGroups.Orthogonal CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.GF2n.Smith81 CFSG.SeitzReduction.OmegaPilot

theorem lin_flipGL_mem_O12 (P : Finset (Fin 6)) :
    lin (flipGL (ZMod 2) P) ∈ TauCeti.QuadraticMap.orthogonalGroup Q12 := by
  have hC : isometryClosure (ZMod 2) 6 ≤
      (TauCeti.QuadraticMap.orthogonalGroup Q12).comap lin :=
    (CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadPlus (n := 6) (K := ZMod 2))).le
  exact hC (Subgroup.subset_closure (flipGL_isometry P))

theorem lin_flipGL_mem_planeSpan (P S : Finset (Fin 6)) {v : V12}
    (hv : v ∈ planeSpan S) : lin (flipGL (ZMod 2) P) v ∈ planeSpan S := by
  rw [mem_planeSpan] at hv ⊢
  intro i hi
  have h1 := (hv i hi).1
  have h2 := (hv i hi).2
  constructor
  · rw [lin, MulEquiv.coe_toMonoidHom, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
      coe_flipGL, Matrix.permMatrix_mulVec, Function.comp_apply]
    by_cases h : i ∈ P <;> simp [flipPerm_apply, flipPermFun, h, h1, h2]
  · rw [lin, MulEquiv.coe_toMonoidHom, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
      coe_flipGL, Matrix.permMatrix_mulVec, Function.comp_apply]
    by_cases h : i ∈ P <;> simp [flipPerm_apply, flipPermFun, h, h1, h2]

theorem rootL_eq_map_conj (B P : Finset (Fin 6)) :
    rootL B P = (rootL B ∅).map (MulAut.conj (lin (flipGL (ZMod 2) P))).toMonoidHom := by
  have hB : rootL B ∅ = (siegelBlockGL (ZMod 2) B).map lin := by
    rw [rootL, flipGL_empty, map_conj_one_eq]
  rw [hB, rootL]
  exact CFSG.StandardType.FrameRoute.FS81.SuppAux.map_conj_map lin (flipGL (ZMod 2) P)
    (siegelBlockGL (ZMod 2) B)

private theorem lin_flipGL_mul_self (P : Finset (Fin 6)) :
    lin (flipGL (ZMod 2) P) * lin (flipGL (ZMod 2) P) = 1 := by
  rw [← map_mul]
  simpa [flipGL_inv P] using congrArg lin (mul_inv_cancel (flipGL (ZMod 2) P))

theorem rootL_apply_eq_self {a b : Fin 6} (hab : a ≠ b) {P : Finset (Fin 6)}
    {z : V12 ≃ₗ[ZMod 2] V12} (hz : z ∈ rootL {a, b} P) {v : V12}
    (hv : v ∈ planeSpan ({a, b} : Finset (Fin 6))ᶜ) : z v = v := by
  have hff := lin_flipGL_mul_self P
  have hfinv : (lin (flipGL (ZMod 2) P))⁻¹ = lin (flipGL (ZMod 2) P) :=
    inv_eq_of_mul_eq_one_right hff
  rw [rootL_eq_map_conj ({a, b} : Finset (Fin 6)) P] at hz
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hz
  change ((MulAut.conj (lin (flipGL (ZMod 2) P))) t) v = v
  rw [MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfinv]
  rw [rootL_apply_eq_self_empty hab
    (lin_flipGL_mem_planeSpan P _ hv) t ht]
  rw [← LinearEquiv.mul_apply, hff, LinearEquiv.coe_one, id]

theorem rootL_apply_mem {a b : Fin 6} (hab : a ≠ b) {P S : Finset (Fin 6)}
    (hS : ({a, b} : Finset (Fin 6)) ⊆ S) {z : V12 ≃ₗ[ZMod 2] V12}
    (hz : z ∈ rootL {a, b} P) {v : V12} (hv : v ∈ planeSpan S) : z v ∈ planeSpan S := by
  have hff := lin_flipGL_mul_self P
  have hfinv : (lin (flipGL (ZMod 2) P))⁻¹ = lin (flipGL (ZMod 2) P) :=
    inv_eq_of_mul_eq_one_right hff
  rw [rootL_eq_map_conj ({a, b} : Finset (Fin 6)) P] at hz
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hz
  change ((MulAut.conj (lin (flipGL (ZMod 2) P))) t) v ∈ planeSpan S
  rw [MulAut.conj_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfinv]
  exact lin_flipGL_mem_planeSpan P S
    (rootL_apply_mem_empty hab hS t ht (lin (flipGL (ZMod 2) P) v)
      (lin_flipGL_mem_planeSpan P S hv))

theorem subCommSpace_rootL {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6)) :
    subCommSpace (rootL {a, b} P) = planeSpan {a, b} := by
  rw [rootL_eq_map_conj ({a, b} : Finset (Fin 6)) P, subCommSpace_map_conj,
    subCommSpace_rootL_empty hab]
  have hle : (planeSpan ({a, b} : Finset (Fin 6))).map
      (lin (flipGL (ZMod 2) P) : V12 →ₗ[ZMod 2] V12) ≤ planeSpan {a, b} := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    exact lin_flipGL_mem_planeSpan P _ hu
  exact Submodule.eq_of_le_of_finrank_eq hle
    (LinearEquiv.finrank_map_eq (lin (flipGL (ZMod 2) P)) _)

private theorem isRootS3Like_map_conj {o : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (ho : IsRootS3Like Q12 o) {f : V12 ≃ₗ[ZMod 2] V12}
    (hf : f ∈ TauCeti.QuadraticMap.orthogonalGroup Q12) :
    IsRootS3Like Q12 (o.map (MulAut.conj f).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rintro s ⟨t, ht, rfl⟩ hss hs1
    change IsTypeA Q12 ((MulAut.conj f) t) 2
    change ((MulAut.conj f) t) * ((MulAut.conj f) t) = 1 at hss
    change ((MulAut.conj f) t) ≠ 1 at hs1
    rw [MulAut.conj_apply] at hss hs1
    have htt : t * t = 1 := by
      calc t * t = f⁻¹ * ((f * t * f⁻¹) * (f * t * f⁻¹)) * f := by group
        _ = f⁻¹ * 1 * f := by rw [hss]
        _ = 1 := by group
    have ht1 : t ≠ 1 := by
      intro h
      apply hs1
      rw [h]
      group
    have hA := ho.typeA t ht htt ht1
    rw [MulAut.conj_apply]
    exact isTypeA_conj hA hf
  · rintro s ⟨t, ht, rfl⟩ s' ⟨t', ht', rfl⟩ hss hs's hs1 hs'1 hne
    change commSpace ((MulAut.conj f) t) ⊓ commSpace ((MulAut.conj f) t') = ⊥
    change ((MulAut.conj f) t) * ((MulAut.conj f) t) = 1 at hss
    change ((MulAut.conj f) t') * ((MulAut.conj f) t') = 1 at hs's
    change ((MulAut.conj f) t) ≠ 1 at hs1
    change ((MulAut.conj f) t') ≠ 1 at hs'1
    change ((MulAut.conj f) t) ≠ ((MulAut.conj f) t') at hne
    rw [MulAut.conj_apply] at hss hs's hs1 hs'1 hne
    have htt : t * t = 1 := by
      calc t * t = f⁻¹ * ((f * t * f⁻¹) * (f * t * f⁻¹)) * f := by group
        _ = f⁻¹ * 1 * f := by rw [hss]
        _ = 1 := by group
    have htt' : t' * t' = 1 := by
      calc t' * t' = f⁻¹ * ((f * t' * f⁻¹) * (f * t' * f⁻¹)) * f := by group
        _ = f⁻¹ * 1 * f := by rw [hs's]
        _ = 1 := by group
    have ht1 : t ≠ 1 := by
      intro h
      apply hs1
      rw [h]
      group
    have ht'1 : t' ≠ 1 := by
      intro h
      apply hs'1
      rw [h]
      group
    have hne' : t ≠ t' := by
      intro h
      apply hne
      rw [h, MulAut.conj_apply]
    have hdisj := ho.disj t ht t' ht' htt htt' ht1 ht'1 hne'
    rw [MulAut.conj_apply, MulAut.conj_apply, commSpace_conj, commSpace_conj]
    rw [← Submodule.map_inf (f : V12 →ₗ[ZMod 2] V12) f.injective, hdisj]
    simp

theorem isRootS3Like_rootL {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6)) :
    IsRootS3Like Q12 (rootL {a, b} P) := by
  rw [rootL_eq_map_conj ({a, b} : Finset (Fin 6)) P]
  exact isRootS3Like_map_conj (isRootS3Like_rootL_empty hab) (lin_flipGL_mem_O12 P)

theorem plusNodeSet_six : plusNodeSet 6 0 = {0, 1} ∧ plusNodeSet 6 1 = {1, 2} ∧
    plusNodeSet 6 2 = {2, 3} ∧ plusNodeSet 6 3 = {3, 4} ∧ plusNodeSet 6 4 = {4, 5} ∧
    plusNodeSet 6 5 = {4, 5} := by
  decide

theorem subCommSpace_node (j : Fin 6) : subCommSpace (node j) = planeSpan (plusNodeSet 6 j) := by
  fin_cases j
  · change subCommSpace (node (0 : Fin 6)) = planeSpan (plusNodeSet 6 (0 : Fin 6))
    rw [node, show plusNodeSet 6 (0 : Fin 6) = {0, 1} by decide,
      show plusNodeFlip 6 (0 : Fin 6) = ∅ by decide]
    exact subCommSpace_rootL (by decide) ∅
  · change subCommSpace (node (1 : Fin 6)) = planeSpan (plusNodeSet 6 (1 : Fin 6))
    rw [node, show plusNodeSet 6 (1 : Fin 6) = {1, 2} by decide,
      show plusNodeFlip 6 (1 : Fin 6) = ∅ by decide]
    exact subCommSpace_rootL (by decide) ∅
  · change subCommSpace (node (2 : Fin 6)) = planeSpan (plusNodeSet 6 (2 : Fin 6))
    rw [node, show plusNodeSet 6 (2 : Fin 6) = {2, 3} by decide,
      show plusNodeFlip 6 (2 : Fin 6) = ∅ by decide]
    exact subCommSpace_rootL (by decide) ∅
  · change subCommSpace (node (3 : Fin 6)) = planeSpan (plusNodeSet 6 (3 : Fin 6))
    rw [node, show plusNodeSet 6 (3 : Fin 6) = {3, 4} by decide,
      show plusNodeFlip 6 (3 : Fin 6) = ∅ by decide]
    exact subCommSpace_rootL (by decide) ∅
  · change subCommSpace (node (4 : Fin 6)) = planeSpan (plusNodeSet 6 (4 : Fin 6))
    rw [node, show plusNodeSet 6 (4 : Fin 6) = {4, 5} by decide,
      show plusNodeFlip 6 (4 : Fin 6) = ∅ by decide]
    exact subCommSpace_rootL (by decide) ∅
  · change subCommSpace (node (5 : Fin 6)) = planeSpan (plusNodeSet 6 (5 : Fin 6))
    rw [node, show plusNodeSet 6 (5 : Fin 6) = {4, 5} by decide,
      show plusNodeFlip 6 (5 : Fin 6) = {5} by decide]
    exact subCommSpace_rootL (by decide) {5}

theorem isRootS3Like_node (j : Fin 6) : IsRootS3Like Q12 (node j) := by
  fin_cases j
  · change IsRootS3Like Q12 (node (0 : Fin 6))
    rw [node, show plusNodeSet 6 (0 : Fin 6) = {0, 1} by decide,
      show plusNodeFlip 6 (0 : Fin 6) = ∅ by decide]
    exact isRootS3Like_rootL (by decide) ∅
  · change IsRootS3Like Q12 (node (1 : Fin 6))
    rw [node, show plusNodeSet 6 (1 : Fin 6) = {1, 2} by decide,
      show plusNodeFlip 6 (1 : Fin 6) = ∅ by decide]
    exact isRootS3Like_rootL (by decide) ∅
  · change IsRootS3Like Q12 (node (2 : Fin 6))
    rw [node, show plusNodeSet 6 (2 : Fin 6) = {2, 3} by decide,
      show plusNodeFlip 6 (2 : Fin 6) = ∅ by decide]
    exact isRootS3Like_rootL (by decide) ∅
  · change IsRootS3Like Q12 (node (3 : Fin 6))
    rw [node, show plusNodeSet 6 (3 : Fin 6) = {3, 4} by decide,
      show plusNodeFlip 6 (3 : Fin 6) = ∅ by decide]
    exact isRootS3Like_rootL (by decide) ∅
  · change IsRootS3Like Q12 (node (4 : Fin 6))
    rw [node, show plusNodeSet 6 (4 : Fin 6) = {4, 5} by decide,
      show plusNodeFlip 6 (4 : Fin 6) = ∅ by decide]
    exact isRootS3Like_rootL (by decide) ∅
  · change IsRootS3Like Q12 (node (5 : Fin 6))
    rw [node, show plusNodeSet 6 (5 : Fin 6) = {4, 5} by decide,
      show plusNodeFlip 6 (5 : Fin 6) = {5} by decide]
    exact isRootS3Like_rootL (by decide) {5}

theorem node_apply_eq_self (j : Fin 6) {z : V12 ≃ₗ[ZMod 2] V12} (hz : z ∈ node j) {v : V12}
    (hv : v ∈ planeSpan (plusNodeSet 6 j)ᶜ) : z v = v := by
  fin_cases j
  · change z ∈ node (0 : Fin 6) at hz
    change v ∈ planeSpan (plusNodeSet 6 (0 : Fin 6))ᶜ at hv
    rw [node, show plusNodeSet 6 (0 : Fin 6) = {0, 1} by decide,
      show plusNodeFlip 6 (0 : Fin 6) = ∅ by decide] at hz
    rw [show plusNodeSet 6 (0 : Fin 6) = {0, 1} by decide] at hv
    exact rootL_apply_eq_self (by decide) hz hv
  · change z ∈ node (1 : Fin 6) at hz
    change v ∈ planeSpan (plusNodeSet 6 (1 : Fin 6))ᶜ at hv
    rw [node, show plusNodeSet 6 (1 : Fin 6) = {1, 2} by decide,
      show plusNodeFlip 6 (1 : Fin 6) = ∅ by decide] at hz
    rw [show plusNodeSet 6 (1 : Fin 6) = {1, 2} by decide] at hv
    exact rootL_apply_eq_self (by decide) hz hv
  · change z ∈ node (2 : Fin 6) at hz
    change v ∈ planeSpan (plusNodeSet 6 (2 : Fin 6))ᶜ at hv
    rw [node, show plusNodeSet 6 (2 : Fin 6) = {2, 3} by decide,
      show plusNodeFlip 6 (2 : Fin 6) = ∅ by decide] at hz
    rw [show plusNodeSet 6 (2 : Fin 6) = {2, 3} by decide] at hv
    exact rootL_apply_eq_self (by decide) hz hv
  · change z ∈ node (3 : Fin 6) at hz
    change v ∈ planeSpan (plusNodeSet 6 (3 : Fin 6))ᶜ at hv
    rw [node, show plusNodeSet 6 (3 : Fin 6) = {3, 4} by decide,
      show plusNodeFlip 6 (3 : Fin 6) = ∅ by decide] at hz
    rw [show plusNodeSet 6 (3 : Fin 6) = {3, 4} by decide] at hv
    exact rootL_apply_eq_self (by decide) hz hv
  · change z ∈ node (4 : Fin 6) at hz
    change v ∈ planeSpan (plusNodeSet 6 (4 : Fin 6))ᶜ at hv
    rw [node, show plusNodeSet 6 (4 : Fin 6) = {4, 5} by decide,
      show plusNodeFlip 6 (4 : Fin 6) = ∅ by decide] at hz
    rw [show plusNodeSet 6 (4 : Fin 6) = {4, 5} by decide] at hv
    exact rootL_apply_eq_self (by decide) hz hv
  · change z ∈ node (5 : Fin 6) at hz
    change v ∈ planeSpan (plusNodeSet 6 (5 : Fin 6))ᶜ at hv
    rw [node, show plusNodeSet 6 (5 : Fin 6) = {4, 5} by decide,
      show plusNodeFlip 6 (5 : Fin 6) = {5} by decide] at hz
    rw [show plusNodeSet 6 (5 : Fin 6) = {4, 5} by decide] at hv
    exact rootL_apply_eq_self (by decide) hz hv

theorem node_apply_mem (j : Fin 6) {S : Finset (Fin 6)} (hS : plusNodeSet 6 j ⊆ S)
    {z : V12 ≃ₗ[ZMod 2] V12} (hz : z ∈ node j) {v : V12} (hv : v ∈ planeSpan S) :
    z v ∈ planeSpan S := by
  fin_cases j
  · change z ∈ node (0 : Fin 6) at hz
    change plusNodeSet 6 (0 : Fin 6) ⊆ S at hS
    rw [node, show plusNodeSet 6 (0 : Fin 6) = {0, 1} by decide,
      show plusNodeFlip 6 (0 : Fin 6) = ∅ by decide] at hz
    rw [show plusNodeSet 6 (0 : Fin 6) = {0, 1} by decide] at hS
    exact rootL_apply_mem (by decide) hS hz hv
  · change z ∈ node (1 : Fin 6) at hz
    change plusNodeSet 6 (1 : Fin 6) ⊆ S at hS
    rw [node, show plusNodeSet 6 (1 : Fin 6) = {1, 2} by decide,
      show plusNodeFlip 6 (1 : Fin 6) = ∅ by decide] at hz
    rw [show plusNodeSet 6 (1 : Fin 6) = {1, 2} by decide] at hS
    exact rootL_apply_mem (by decide) hS hz hv
  · change z ∈ node (2 : Fin 6) at hz
    change plusNodeSet 6 (2 : Fin 6) ⊆ S at hS
    rw [node, show plusNodeSet 6 (2 : Fin 6) = {2, 3} by decide,
      show plusNodeFlip 6 (2 : Fin 6) = ∅ by decide] at hz
    rw [show plusNodeSet 6 (2 : Fin 6) = {2, 3} by decide] at hS
    exact rootL_apply_mem (by decide) hS hz hv
  · change z ∈ node (3 : Fin 6) at hz
    change plusNodeSet 6 (3 : Fin 6) ⊆ S at hS
    rw [node, show plusNodeSet 6 (3 : Fin 6) = {3, 4} by decide,
      show plusNodeFlip 6 (3 : Fin 6) = ∅ by decide] at hz
    rw [show plusNodeSet 6 (3 : Fin 6) = {3, 4} by decide] at hS
    exact rootL_apply_mem (by decide) hS hz hv
  · change z ∈ node (4 : Fin 6) at hz
    change plusNodeSet 6 (4 : Fin 6) ⊆ S at hS
    rw [node, show plusNodeSet 6 (4 : Fin 6) = {4, 5} by decide,
      show plusNodeFlip 6 (4 : Fin 6) = ∅ by decide] at hz
    rw [show plusNodeSet 6 (4 : Fin 6) = {4, 5} by decide] at hS
    exact rootL_apply_mem (by decide) hS hz hv
  · change z ∈ node (5 : Fin 6) at hz
    change plusNodeSet 6 (5 : Fin 6) ⊆ S at hS
    rw [node, show plusNodeSet 6 (5 : Fin 6) = {4, 5} by decide,
      show plusNodeFlip 6 (5 : Fin 6) = {5} by decide] at hz
    rw [show plusNodeSet 6 (5 : Fin 6) = {4, 5} by decide] at hS
    exact rootL_apply_mem (by decide) hS hz hv

end CFSG.StandardType.FrameRoute.FS81.D6M
