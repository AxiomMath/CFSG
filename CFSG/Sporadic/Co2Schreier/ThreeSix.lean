module

public import CFSG.Sporadic.Co2Schreier.ThreeBasic
public import CFSG.Sporadic.Co2Schreier.SixGroup

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu
open scoped Matrix

@[expose] def rowMat (rows : List ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun j k => if (rows.getD j 0).testBit k then 1 else 0

theorem p0SixOK_spec {k : ℕ} {rows : List ℕ} (h : p0SixOK k rows = true) :
    ∀ j < 6, sixImage enumP0.elems[k]! j = xorBits sixPacked (colBits rows j) := by
  intro j hj
  have h' : (sixImage enumP0.elems[k]! j == xorBits sixPacked (colBits rows j)) = true :=
    allLt_spec (p := fun j =>
      sixImage enumP0.elems[k]! j == xorBits sixPacked (colBits rows j)) h (i := j) hj
  simpa using h'

theorem linC_sixVec_of_image
    {c : locC} {t : Array ℕ} (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) {rows : List ℕ}
    (h : ∀ j < 6, sixImage t j = xorBits sixPacked (colBits rows j)) (k : Fin 6) :
    linC c (sixVec k) = ∑ j : Fin 6, rowMat rows j k • sixVec j := by
  rw [linC_sixVec, ← toVecD_sixImage ht k, h k k.2, ← sum_sixVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [colBits_testBit, rowMat, Matrix.of_apply]
  simp only [j.2, decide_true, Bool.true_and]
  split_ifs <;> simp

theorem sixAction_basis_of_image
    {c : locC} {t : Array ℕ} (ht : Rep 2300 t (c : Equiv.Perm (Fin 2300))) {rows : List ℕ}
    (h : ∀ j < 6, sixImage t j = xorBits sixPacked (colBits rows j)) (k : Fin 6) :
    sixAction c (sixBasis k) = ∑ j : Fin 6, rowMat rows j k • sixBasis j := by
  apply Subtype.ext
  rw [sixAction_apply, sixBasis_apply, linC_sixVec_of_image ht h, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, sixBasis_apply]

theorem toMatrix_sixAction_eltE
    {k : ℕ} (hk : k < 81) {rows : List ℕ}
    (h : p0SixOK k rows = true) :
    LinearMap.toMatrix sixBasis sixBasis
      (sixAction ⟨eltE enumP0 k, locP0_le_C (eltE_mem_locP0 hk)⟩ : V6 →ₗ[ZMod 2] V6) =
      rowMat rows := by
  ext j m
  rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe,
    sixAction_basis_of_image
      (c := ⟨eltE enumP0 k, locP0_le_C (eltE_mem_locP0 hk)⟩) (enumP0_facts.rep hk)
      (p0SixOK_spec h) m,
    Module.Basis.repr_sum_self]

@[expose] def threeM1 : Matrix (Fin 6) (Fin 6) (ZMod 2) := rowMat [1, 55, 49, 61, 63, 32]

@[expose] def threeM2 : Matrix (Fin 6) (Fin 6) (ZMod 2) := rowMat [43, 34, 5, 14, 54, 45]

@[expose] def threeM3 : Matrix (Fin 6) (Fin 6) (ZMod 2) := rowMat [1, 57, 30, 20, 2, 7]

@[expose] def threeW : Fin 6 → Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ![(1 : Matrix (Fin 6) (Fin 6) (ZMod 2)), threeM1, threeM2, threeM3, threeM1 * threeM3,
    threeM2 * threeM3]

@[expose] def threeC (w : Fin 6 → ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => (threeW j *ᵥ w) i

@[expose] def threeBinv : Matrix (Fin 6) (Fin 6) (ZMod 2) := rowMat [41, 46, 12, 18, 62, 38]

theorem threeC_e0 : threeC (Pi.single 0 1) = rowMat [63, 26, 38, 34, 18, 28] := by
  decide +kernel

theorem threeB_mul_Binv : rowMat [63, 26, 38, 34, 18, 28] * threeBinv = 1 := by
  decide +kernel

theorem threeC_mul_Binv_involution :
    ∀ w : Fin 6 → ZMod 2, (threeC w * threeBinv) * (threeC w * threeBinv) = 1 →
      threeC w * threeBinv = 1 := by
  decide +kernel

theorem eq_one_of_commute_rowMat {X : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (h1 : X * rowMat [1, 55, 49, 61, 63, 32] = rowMat [1, 55, 49, 61, 63, 32] * X)
    (h2 : X * rowMat [43, 34, 5, 14, 54, 45] = rowMat [43, 34, 5, 14, 54, 45] * X)
    (h3 : X * rowMat [1, 57, 30, 20, 2, 7] = rowMat [1, 57, 30, 20, 2, 7] * X)
    (hX : X * X = 1) : X = 1 := by
  have hW : ∀ j, X * threeW j = threeW j * X := by
    intro j
    fin_cases j
    · simpa [threeW] using (Matrix.mul_one X).trans (Matrix.one_mul X).symm
    · simpa [threeW, threeM1] using h1
    · simpa [threeW, threeM2] using h2
    · simpa [threeW, threeM3] using h3
    · simpa [threeW, threeM1, threeM3] using (Commute.mul_right h1 h3).eq
    · simpa [threeW, threeM2, threeM3] using (Commute.mul_right h2 h3).eq
  have hcol : X * threeC (Pi.single 0 1) = threeC (X *ᵥ Pi.single 0 1) := by
    ext i j
    have h := congrFun (congrFun (hW j) i) 0
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    simpa [threeC, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using h
  have hXe : X = threeC (X *ᵥ Pi.single 0 1) * threeBinv := by
    calc
      X = X * 1 := (Matrix.mul_one X).symm
      _ = X * (rowMat [63, 26, 38, 34, 18, 28] * threeBinv) := by rw [threeB_mul_Binv]
      _ = (X * rowMat [63, 26, 38, 34, 18, 28]) * threeBinv := by rw [Matrix.mul_assoc]
      _ = (X * threeC (Pi.single 0 1)) * threeBinv := by rw [threeC_e0]
      _ = (threeC (X *ᵥ Pi.single 0 1)) * threeBinv := by rw [hcol]
  have hXX : (threeC (X *ᵥ Pi.single 0 1) * threeBinv) *
      (threeC (X *ᵥ Pi.single 0 1) * threeBinv) = 1 := by
    rw [← hXe]
    exact hX
  rw [hXe]
  exact threeC_mul_Binv_involution _ hXX

theorem toMatrix_sixAction_mul
    (a b : locC) :
    LinearMap.toMatrix sixBasis sixBasis (sixAction a : V6 →ₗ[ZMod 2] V6) *
      LinearMap.toMatrix sixBasis sixBasis (sixAction b : V6 →ₗ[ZMod 2] V6) =
    LinearMap.toMatrix sixBasis sixBasis (sixAction (a * b) : V6 →ₗ[ZMod 2] V6) := by
  rw [← LinearMap.toMatrix_mul, ← LinearEquiv.coe_toLinearMap_mul, ← map_mul]

theorem mem_locQ_of_commute
    {u : Equiv.Perm (Fin 2300)} (hu : u ∈ locC) (hu2 : u * u = 1)
    (h56 : u * eltE enumP0 56 = eltE enumP0 56 * u)
    (h1 : u * eltE enumP0 1 = eltE enumP0 1 * u)
    (h20 : u * eltE enumP0 20 = eltE enumP0 20 * u) : u ∈ locQ := by
  let c : locC := ⟨u, hu⟩
  let f56 : locC := ⟨eltE enumP0 56, locP0_le_C (eltE_mem_locP0 (by norm_num))⟩
  let f1 : locC := ⟨eltE enumP0 1, locP0_le_C (eltE_mem_locP0 (by norm_num))⟩
  let f20 : locC := ⟨eltE enumP0 20, locP0_le_C (eltE_mem_locP0 (by norm_num))⟩
  let X : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    LinearMap.toMatrix sixBasis sixBasis (sixAction c : V6 →ₗ[ZMod 2] V6)
  have hmat56 : LinearMap.toMatrix sixBasis sixBasis
      (sixAction f56 : V6 →ₗ[ZMod 2] V6) = rowMat [1, 55, 49, 61, 63, 32] :=
    toMatrix_sixAction_eltE (by norm_num) p0Six_check.1
  have hmat1 : LinearMap.toMatrix sixBasis sixBasis
      (sixAction f1 : V6 →ₗ[ZMod 2] V6) = rowMat [43, 34, 5, 14, 54, 45] :=
    toMatrix_sixAction_eltE (by norm_num) p0Six_check.2.1
  have hmat20 : LinearMap.toMatrix sixBasis sixBasis
      (sixAction f20 : V6 →ₗ[ZMod 2] V6) = rowMat [1, 57, 30, 20, 2, 7] :=
    toMatrix_sixAction_eltE (by norm_num) p0Six_check.2.2
  have hc56 : c * f56 = f56 * c := Subtype.ext (by simpa [c, f56] using h56)
  have hc1 : c * f1 = f1 * c := Subtype.ext (by simpa [c, f1] using h1)
  have hc20 : c * f20 = f20 * c := Subtype.ext (by simpa [c, f20] using h20)
  have hX56 : X * rowMat [1, 55, 49, 61, 63, 32] =
      rowMat [1, 55, 49, 61, 63, 32] * X := by
    simp only [X]
    rw [← hmat56, toMatrix_sixAction_mul, toMatrix_sixAction_mul, hc56]
  have hX1 : X * rowMat [43, 34, 5, 14, 54, 45] =
      rowMat [43, 34, 5, 14, 54, 45] * X := by
    simp only [X]
    rw [← hmat1, toMatrix_sixAction_mul, toMatrix_sixAction_mul, hc1]
  have hX20 : X * rowMat [1, 57, 30, 20, 2, 7] =
      rowMat [1, 57, 30, 20, 2, 7] * X := by
    simp only [X]
    rw [← hmat20, toMatrix_sixAction_mul, toMatrix_sixAction_mul, hc20]
  have hcc : c * c = 1 := Subtype.ext (by simpa [c] using hu2)
  have hXsq : X * X = 1 := by
    simp only [X]
    rw [toMatrix_sixAction_mul, hcc, map_one]
    simpa using (LinearMap.toMatrix_one sixBasis)
  have hXeq : X = 1 := eq_one_of_commute_rowMat hX56 hX1 hX20 hXsq
  have hlin : (sixAction c : V6 →ₗ[ZMod 2] V6) = 1 := by
    refine (LinearMap.toMatrix sixBasis sixBasis).injective ?_
    rw [LinearMap.toMatrix_one]
    simpa [X] using hXeq
  have hsix : sixAction c = 1 := by
    apply LinearEquiv.toLinearMap_injective
    simpa [Module.End.one_eq_id] using hlin
  have hker : c ∈ sixAction.ker := MonoidHom.mem_ker.2 hsix
  rw [sixAction_ker] at hker
  simpa [c] using (Subgroup.mem_subgroupOf.1 hker)

theorem eq_one_or_eq_locZ_of_mem_locQ
    {u : Equiv.Perm (Fin 2300)} (hu : u ∈ locQ)
    (h56 : u * eltE enumP0 56 = eltE enumP0 56 * u) : u = 1 ∨ u = locZ := by
  obtain ⟨k, hk, hku⟩ := enumQ_facts.exists_elt repTuple_q (x := u) (by simpa [locQ] using hu)
  have hcomm : eltE enumQ k * eltE enumP0 56 = eltE enumP0 56 * eltE enumQ k := by
    rw [hku]
    exact h56
  have hmem : k ∈ qCentIdx56 := by
    rw [qCentIdx56, List.mem_filter, List.mem_range]
    exact ⟨hk, (commA_iff (enumQ_facts.rep hk)
      (enumP0_facts.rep (by norm_num : 56 < 81))).2 hcomm⟩
  rw [qCent_check] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · left
    rw [← hku]
    exact enumQ_facts.elt_zero
  · right
    rw [← hku]
    exact eltE_Q_z

end CFSG.Sporadic.Co2Schreier
