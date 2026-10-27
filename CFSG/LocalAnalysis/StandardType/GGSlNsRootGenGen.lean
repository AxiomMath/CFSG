module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenDefs
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRepCases

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane CFSG.Assembly TableB Multiplicative
open scoped commutatorElement

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r : ℕ}

noncomputable def coord (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) (a : Fin (rootPB g).dim) : Fin n :=
  ε.symm (Sum.inl (a, i))

noncomputable def fixedCoord (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (z : Fin r) : Fin n :=
  ε.symm (Sum.inr z)

theorem coord_inl_ne_coord_inl {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {i j : Fin s} (hij : i ≠ j) (a b : Fin (rootPB g).dim) :
    coord ε i a ≠ coord ε j b := by
  intro h
  have h' := ε.symm.injective h
  exact hij (Prod.mk_inj.mp (Sum.inl.inj h')).2

theorem coord_inl_ne_coord_inl_of_ne {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {i : Fin s} {a b : Fin (rootPB g).dim} (hab : a ≠ b) :
    coord ε i a ≠ coord ε i b := by
  intro h
  exact hab (Prod.mk_inj.mp (Sum.inl.inj (ε.symm.injective h))).1

theorem coord_inl_ne_fixed {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    (i : Fin s) (a : Fin (rootPB g).dim) (z : Fin r) :
    coord ε i a ≠ fixedCoord ε z := by
  intro h
  exact Sum.inl_ne_inr (ε.symm.injective h)

theorem coord_mem_blockCoords {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    (i : Fin s) (a : Fin (rootPB g).dim) : coord ε i a ∈ blockCoords ε i := by
  rw [coord]
  exact (mem_blockCoords_inl (ε := ε) (x := ε.symm (Sum.inl (a, i))) (a := a)
    (m := i) (by simp)).mpr rfl

theorem fixed_mem_blockCoords {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    (i : Fin s) (z : Fin r) : fixedCoord ε z ∈ blockCoords ε i :=
  mem_blockCoords_inr (ε := ε) (x := fixedCoord ε z) (z := z) (by simp [fixedCoord])

noncomputable def blockUnit (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i j : Fin s) : Matrix (Fin n) (Fin n) K :=
  ∑ a : Fin (rootPB g).dim, single (coord ε i a) (coord ε j a) 1

private theorem one_add_mul_one_add_mul_one_sub_mul_one_sub {R : Type*} [Ring R] {X E : R}
    (hX : X * X = 0) (hEX : E * X = 0) (hE : E * E = 0) :
    (1 + X) * (1 + E) * (1 - X) * (1 - E) = 1 + X * E := by
  have h : (1 + X) * (1 + E) * (1 - X) * (1 - E) =
      1 + X * E - X * X - E * X - X * E * X - E * E - X * E * E
        + X * X * E + E * X * E + X * E * X * E := by
    noncomm_ring
  have h1 : X * E * X = 0 := by rw [mul_assoc, hEX, mul_zero]
  have h2 : X * E * E = 0 := by rw [mul_assoc, hE, mul_zero]
  have h3 : X * X * E = 0 := by rw [hX, zero_mul]
  have h4 : E * X * E = 0 := by rw [hEX, zero_mul]
  have h5 : X * E * X * E = 0 := by rw [mul_assoc X E X, hEX, mul_zero, zero_mul]
  rw [h]
  simp [hX, hEX, hE, h1, h2, h3, h4, h5]

theorem blockUnit_mul_self {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {i j : Fin s} (hij : i ≠ j) :
    blockUnit (K := K) ε i j * blockUnit ε i j = 0 := by
  unfold blockUnit
  rw [Matrix.sum_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [Matrix.single_mul_single_of_ne]
  intro h
  exact hij.symm (Prod.mk_inj.mp (Sum.inl.inj (ε.symm.injective h))).2

theorem blockUnit_mul_single {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {i j : Fin s} (b c : Fin (rootPB g).dim) (t : K) :
    blockUnit (K := K) ε i j * single (coord ε j b) (coord ε j c) t =
      single (coord ε i b) (coord ε j c) t := by
  unfold blockUnit
  rw [Matrix.sum_mul]
  rw [Finset.sum_eq_single b]
  · rw [Matrix.single_mul_single_same, one_mul]
  · intro a _ hab
    rw [Matrix.single_mul_single_of_ne]
    intro h
    exact hab (Prod.mk_inj.mp (Sum.inl.inj (ε.symm.injective h))).1
  · intro hb
    exact absurd (Finset.mem_univ b) hb

theorem single_mul_blockUnit {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {i j : Fin s} (b c : Fin (rootPB g).dim) (t : K) :
    single (coord ε i b) (coord ε i c) t * blockUnit (K := K) ε i j =
      single (coord ε i b) (coord ε j c) t := by
  unfold blockUnit
  rw [Matrix.mul_sum]
  rw [Finset.sum_eq_single c]
  · rw [Matrix.single_mul_single_same, mul_one]
  · intro a _ hac
    rw [Matrix.single_mul_single_of_ne]
    intro h
    exact hac.symm (Prod.mk_inj.mp (Sum.inl.inj (ε.symm.injective h))).1
  · intro hc
    exact absurd (Finset.mem_univ c) hc

theorem blockUnit_mul_single_of_ne {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {i j k : Fin s} (hkj : k ≠ j) (b c : Fin (rootPB g).dim) (t : K) :
    blockUnit (K := K) ε i j * single (coord ε k b) (coord ε k c) t = 0 := by
  unfold blockUnit
  rw [Matrix.sum_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.single_mul_single_of_ne]
  intro h
  exact hkj.symm (Prod.mk_inj.mp (Sum.inl.inj (ε.symm.injective h))).2

theorem single_mul_blockUnit_of_ne {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
    {i j k : Fin s} (hki : k ≠ i) (b c : Fin (rootPB g).dim) (t : K) :
    single (coord ε k b) (coord ε k c) t * blockUnit (K := K) ε i j = 0 := by
  unfold blockUnit
  rw [Matrix.mul_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Matrix.single_mul_single_of_ne]
  intro h
  exact hki (Prod.mk_inj.mp (Sum.inl.inj (ε.symm.injective h))).2

theorem frameCoords_symm_single_coord
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (a : Fin (rootPB g).dim) (i : Fin s) :
    (frameCoords g ε).symm (Pi.single (coord ε i a) 1) =
      ((Pi.single i ((rootPB g).basis a) : Fin s → AdjoinRoot g), (0 : Fin r → K)) := by
  rw [LinearEquiv.symm_apply_eq]
  exact (frameCoords_single_basis ε a i).symm

theorem frameForm_add (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (u v : Matrix (Fin n) (Fin n) K) :
    frameForm g ε (u + v) = frameForm g ε u + frameForm g ε v := by
  refine LinearMap.ext fun x => ?_
  simp [frameForm_apply, Matrix.add_mulVec]

theorem frameForm_sub (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (u v : Matrix (Fin n) (Fin n) K) :
    frameForm g ε (u - v) = frameForm g ε u - frameForm g ε v := by
  refine LinearMap.ext fun x => ?_
  simp [frameForm_apply, Matrix.sub_mulVec]

theorem frameForm_blockUnit_apply
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (i j : Fin s)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    frameForm g ε (blockUnit (K := K) ε i j) x =
      ((Pi.single i (x.1 j) : Fin s → AdjoinRoot g), (0 : Fin r → K)) := by
  rw [frameForm_apply]
  have hX : blockUnit (K := K) ε i j *ᵥ frameCoords g ε x =
      ∑ a : Fin (rootPB g).dim,
        frameCoords g ε x (coord ε j a) • Pi.single (coord ε i a) (1 : K) := by
    rw [blockUnit, Matrix.sum_mulVec]
    simp [Matrix.single_mulVec_eq]
  rw [hX, map_sum]
  have hcoeff : ∀ a : Fin (rootPB g).dim,
      frameCoords g ε x (coord ε j a) = (rootPB g).basis.repr (x.1 j) a := by
    intro a
    rw [frameCoords_apply]
    simp [coord]
  simp_rw [hcoeff, map_smul, frameCoords_symm_single_coord]
  have hsum : (∑ a : Fin (rootPB g).dim,
      (rootPB g).basis.repr (x.1 j) a • (rootPB g).basis a) = x.1 j :=
    (rootPB g).basis.sum_repr (x.1 j)
  refine Prod.ext ?_ ?_
  · funext k
    rw [Prod.fst_sum]
    simp only [Prod.smul_fst, Finset.sum_apply, Pi.smul_apply]
    by_cases hk : k = i
    · subst hk
      simp only [Pi.single_eq_same, smul_eq_mul, mul_one]
      exact hsum
    · simp [hk]
  · rw [Prod.snd_sum]
    simp [Prod.smul_snd]

theorem frameForm_blockUnit
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (i j : Fin s) :
    frameForm g ε (blockUnit (K := K) ε i j) =
      (LinearMap.inl K _ _ ∘ₗ LinearMap.single K (fun _ => AdjoinRoot g) i ∘ₗ
        LinearMap.proj j ∘ₗ LinearMap.fst K _ _) := by
  refine LinearMap.ext fun x => ?_
  exact frameForm_blockUnit_apply ε i j x

theorem frameForm_one_add_blockUnit
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (i j : Fin s) :
    frameForm g ε (1 + blockUnit (K := K) ε i j) =
      LinearMap.id + (LinearMap.inl K _ _ ∘ₗ LinearMap.single K (fun _ => AdjoinRoot g) i ∘ₗ
        LinearMap.proj j ∘ₗ LinearMap.fst K _ _) := by
  rw [frameForm_add, frameForm_one, frameForm_blockUnit]

theorem thetaMat_transvection_one
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j) :
    thetaMat g ε (Matrix.transvection i j (1 : AdjoinRoot g)) =
      1 + blockUnit (K := K) ε i j := by
  apply frameForm_injective g ε
  rw [frameForm_thetaMat, frameForm_one_add_blockUnit]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.add_apply, LinearMap.id_apply, blockAct_apply]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add]
    funext k
    simp [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq,
      Pi.single_apply, smul_eq_mul, LinearMap.comp_apply]
  · simp [LinearMap.comp_apply]

theorem thetaMat_transvection_neg_one
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j) :
    thetaMat g ε (Matrix.transvection i j (-1 : AdjoinRoot g)) =
      1 - blockUnit (K := K) ε i j := by
  apply frameForm_injective g ε
  rw [frameForm_thetaMat, frameForm_sub, frameForm_one, frameForm_blockUnit]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, LinearMap.id_apply, blockAct_apply]
  rw [show Matrix.transvection i j (-1 : AdjoinRoot g) = 1 - single i j (1 : AdjoinRoot g) by
    rw [Matrix.transvection, sub_eq_add_neg, Matrix.single_neg]]
  refine Prod.ext ?_ ?_
  · funext k
    simp [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, Pi.single_apply,
      smul_eq_mul]
  · simp

theorem coe_theta_transvection_one
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j) :
    ((theta g ε (SpecialLinearGroup.transvection hij (1 : AdjoinRoot g)) :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + blockUnit (K := K) ε i j := by
  rw [coe_theta, CFSG.LinearGroups.coe_transvection]
  exact thetaMat_transvection_one ε hij

theorem coe_theta_transvection_neg_one
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j) :
    ((theta g ε (SpecialLinearGroup.transvection hij (-1 : AdjoinRoot g)) :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 - blockUnit (K := K) ε i j := by
  rw [coe_theta, CFSG.LinearGroups.coe_transvection]
  exact thetaMat_transvection_neg_one ε hij

theorem transvection_mem_zeroBlock
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i : Fin s} {x y : Fin n}
    (hx : x ∈ blockCoords ε i) (hy : y ∈ blockCoords ε i) (hxy : x ≠ y) (t : K) :
    SpecialLinearGroup.transvection hxy t ∈ zeroBlock g ε i := by
  rw [zeroBlock]
  exact SLRep.transvection_mem_coordBlockSL hx hy hxy t

theorem theta_transvection_one_mem_pairBlock
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j) :
    theta g ε (SpecialLinearGroup.transvection hij (1 : AdjoinRoot g)) ∈
      pairBlock g ε i j := by
  rw [pairBlock, Subgroup.mem_map]
  exact ⟨_, SLRep.transvection_mem_coordBlockSL (by simp) (by simp) hij 1, rfl⟩

private theorem transvection_proof_irrel {x y : Fin n} (h h' : x ≠ y) (t : K) :
    SpecialLinearGroup.transvection h t = SpecialLinearGroup.transvection h' t :=
  Subtype.ext rfl

theorem transvection_mem_of_three_index {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    {x y z : Fin n} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (t : K)
    (hA : SpecialLinearGroup.transvection hxy t ∈ H)
    (hB : SpecialLinearGroup.transvection hyz (1 : K) ∈ H) :
    SpecialLinearGroup.transvection hxz t ∈ H := by
  have h := SpecialLinearGroup.commutatorElement_transvection hxy hyz hxz t 1
  rw [mul_one] at h
  rw [← h]
  exact H.commutator_le_self (Subgroup.commutator_mem_commutator hA hB)

theorem cross_transvection_mem {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (hN : theta g ε (SpecialLinearGroup.transvection hij (1 : AdjoinRoot g)) ∈ H)
    (hZ : zeroBlock g ε j ≤ H) {b c : Fin (rootPB g).dim} (hbc : b ≠ c) (t : K) :
    SpecialLinearGroup.transvection (coord_inl_ne_coord_inl (ε := ε) hij b c) t ∈ H := by
  have hbcj : coord ε j b ≠ coord ε j c := coord_inl_ne_coord_inl_of_ne hbc
  let N : SpecialLinearGroup (Fin n) K :=
    theta g ε (SpecialLinearGroup.transvection hij (1 : AdjoinRoot g))
  let E : Matrix (Fin n) (Fin n) K := single (coord ε j b) (coord ε j c) t
  let T : SpecialLinearGroup (Fin n) K := SpecialLinearGroup.transvection hbcj t
  have hT : T ∈ H := by
    dsimp [T]
    exact hZ (transvection_mem_zeroBlock ε (coord_mem_blockCoords j b)
      (coord_mem_blockCoords j c) hbcj t)
  have hcomm : ⁅N, T⁆ =
      SpecialLinearGroup.transvection (coord_inl_ne_coord_inl (ε := ε) hij b c) t := by
    apply Subtype.ext
    have hNmat : ((N : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 + blockUnit (K := K) ε i j := coe_theta_transvection_one ε hij
    have hNinv_eq : N⁻¹ = theta g ε
        (SpecialLinearGroup.transvection hij (-1 : AdjoinRoot g)) := by
      dsimp [N]
      rw [← map_inv, SpecialLinearGroup.transvection_inv]
    have hNinv : ((N⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 - blockUnit (K := K) ε i j := by
      rw [hNinv_eq]
      exact coe_theta_transvection_neg_one ε hij
    have hTmat : ((T : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + E := by
      dsimp [T, E]
      exact CFSG.LinearGroups.coe_transvection hbcj t
    have hTinv_eq : T⁻¹ = SpecialLinearGroup.transvection hbcj (-t) := by
      dsimp [T]
      rw [SpecialLinearGroup.transvection_inv]
    have hTinv : ((T⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 - E := by
      rw [hTinv_eq, CFSG.LinearGroups.coe_transvection]
      simp [E, Matrix.single_neg, sub_eq_add_neg]
    have hXX : blockUnit (K := K) ε i j * blockUnit ε i j = 0 := blockUnit_mul_self hij
    have hEX : E * blockUnit (K := K) ε i j = 0 := by
      dsimp [E]
      exact single_mul_blockUnit_of_ne (i := i) (j := j) (k := j) hij.symm b c t
    have hEE : E * E = 0 := by
      dsimp [E]
      rw [Matrix.single_mul_single_of_ne]
      exact coord_inl_ne_coord_inl_of_ne (Ne.symm hbc)
    change (N : Matrix (Fin n) (Fin n) K) * (T : Matrix (Fin n) (Fin n) K) *
        ((N⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((T⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
    rw [hNmat, hTmat, hNinv, hTinv,
      one_add_mul_one_add_mul_one_sub_mul_one_sub (X := blockUnit (K := K) ε i j) (E := E)
        hXX hEX hEE,
      blockUnit_mul_single b c t,
      CFSG.LinearGroups.coe_transvection (coord_inl_ne_coord_inl hij b c) t]
  rw [← hcomm]
  exact H.commutator_le_self (Subgroup.commutator_mem_commutator hN hT)

theorem cross_transvection_mem' {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (hN : theta g ε (SpecialLinearGroup.transvection hij.symm (1 : AdjoinRoot g)) ∈ H)
    (hZ : zeroBlock g ε j ≤ H) {b c : Fin (rootPB g).dim} (hbc : b ≠ c) (t : K) :
    SpecialLinearGroup.transvection (coord_inl_ne_coord_inl (ε := ε) hij.symm b c) t ∈ H := by
  have hbcj : coord ε j b ≠ coord ε j c := coord_inl_ne_coord_inl_of_ne hbc
  let N : SpecialLinearGroup (Fin n) K :=
    theta g ε (SpecialLinearGroup.transvection hij.symm (1 : AdjoinRoot g))
  let E : Matrix (Fin n) (Fin n) K := single (coord ε j b) (coord ε j c) t
  let T : SpecialLinearGroup (Fin n) K := SpecialLinearGroup.transvection hbcj t
  have hT : T ∈ H := by
    dsimp [T]
    exact hZ (transvection_mem_zeroBlock ε (coord_mem_blockCoords j b)
      (coord_mem_blockCoords j c) hbcj t)
  have hcomm : ⁅T, N⁆ =
      SpecialLinearGroup.transvection (coord_inl_ne_coord_inl (ε := ε) hij.symm b c) t := by
    apply Subtype.ext
    have hNmat : ((N : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 + blockUnit (K := K) ε j i := coe_theta_transvection_one ε hij.symm
    have hNinv_eq : N⁻¹ = theta g ε
        (SpecialLinearGroup.transvection hij.symm (-1 : AdjoinRoot g)) := by
      dsimp [N]
      rw [← map_inv, SpecialLinearGroup.transvection_inv]
    have hNinv : ((N⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 - blockUnit (K := K) ε j i := by
      rw [hNinv_eq]
      exact coe_theta_transvection_neg_one ε hij.symm
    have hTmat : ((T : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + E := by
      dsimp [T, E]
      exact CFSG.LinearGroups.coe_transvection hbcj t
    have hTinv_eq : T⁻¹ = SpecialLinearGroup.transvection hbcj (-t) := by
      dsimp [T]
      rw [SpecialLinearGroup.transvection_inv]
    have hTinv : ((T⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 - E := by
      rw [hTinv_eq, CFSG.LinearGroups.coe_transvection]
      simp [E, Matrix.single_neg, sub_eq_add_neg]
    have hXX : blockUnit (K := K) ε j i * blockUnit ε j i = 0 := blockUnit_mul_self hij.symm
    have hXE : blockUnit (K := K) ε j i * E = 0 := by
      dsimp [E]
      exact blockUnit_mul_single_of_ne (i := j) (j := i) (k := j) hij.symm b c t
    have hEE : E * E = 0 := by
      dsimp [E]
      rw [Matrix.single_mul_single_of_ne]
      exact coord_inl_ne_coord_inl_of_ne (Ne.symm hbc)
    change (T : Matrix (Fin n) (Fin n) K) * (N : Matrix (Fin n) (Fin n) K) *
        ((T⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((N⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
    rw [hNmat, hTmat, hNinv, hTinv,
      one_add_mul_one_add_mul_one_sub_mul_one_sub (X := E) (E := blockUnit (K := K) ε j i)
        hEE hXE hXX,
      single_mul_blockUnit b c t,
      CFSG.LinearGroups.coe_transvection (coord_inl_ne_coord_inl hij.symm b c) t]
  rw [← hcomm]
  exact H.commutator_le_self (Subgroup.commutator_mem_commutator hT hN)

theorem cross_transvection_mem_any {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hdim : 2 ≤ (rootPB g).dim)
    {i j : Fin s} (hij : i ≠ j)
    (hN : theta g ε (SpecialLinearGroup.transvection hij (1 : AdjoinRoot g)) ∈ H)
    (hZ : zeroBlock g ε j ≤ H) {b c : Fin (rootPB g).dim} (t : K) :
    SpecialLinearGroup.transvection (coord_inl_ne_coord_inl (ε := ε) hij b c) t ∈ H := by
  by_cases hbc : b = c
  · subst hbc
    obtain ⟨c', hc'⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin (rootPB g).dim)
      (by rw [Fintype.card_fin]; omega) b
    have hbc' : b ≠ c' := Ne.symm hc'
    have hc'b : c' ≠ b := hc'
    have hA : SpecialLinearGroup.transvection
        (coord_inl_ne_coord_inl (ε := ε) hij b c') t ∈ H :=
      cross_transvection_mem ε hij hN hZ hbc' t
    have hB : SpecialLinearGroup.transvection
        (coord_inl_ne_coord_inl_of_ne (ε := ε) (i := j) (a := c') (b := b) hc'b) (1 : K) ∈ H := by
      refine hZ (transvection_mem_zeroBlock ε (coord_mem_blockCoords j c')
        (coord_mem_blockCoords j b)
        (coord_inl_ne_coord_inl_of_ne (i := j) (a := c') (b := b) hc'b) 1)
    exact transvection_mem_of_three_index (coord_inl_ne_coord_inl hij b c')
      (coord_inl_ne_coord_inl_of_ne (i := j) (a := c') (b := b) hc'b)
      (coord_inl_ne_coord_inl hij b b) t hA hB
  · exact cross_transvection_mem ε hij hN hZ hbc t

theorem cross_transvection_mem_any' {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hdim : 2 ≤ (rootPB g).dim)
    {i j : Fin s} (hij : i ≠ j)
    (hN : theta g ε (SpecialLinearGroup.transvection hij.symm (1 : AdjoinRoot g)) ∈ H)
    (hZ : zeroBlock g ε j ≤ H) {b c : Fin (rootPB g).dim} (t : K) :
    SpecialLinearGroup.transvection (coord_inl_ne_coord_inl (ε := ε) hij.symm b c) t ∈ H := by
  by_cases hbc : b = c
  · subst hbc
    obtain ⟨c', hc'⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin (rootPB g).dim)
      (by rw [Fintype.card_fin]; omega) b
    have hbc' : b ≠ c' := Ne.symm hc'
    have hc'b : c' ≠ b := hc'
    have hA : SpecialLinearGroup.transvection
        (coord_inl_ne_coord_inl_of_ne (ε := ε) (i := j) (a := b) (b := c') hbc') t ∈ H := by
      refine hZ (transvection_mem_zeroBlock ε (coord_mem_blockCoords j b)
        (coord_mem_blockCoords j c')
        (coord_inl_ne_coord_inl_of_ne (i := j) (a := b) (b := c') hbc') t)
    have hB : SpecialLinearGroup.transvection
        (coord_inl_ne_coord_inl (ε := ε) hij.symm c' b) (1 : K) ∈ H :=
      cross_transvection_mem' ε hij hN hZ hc'b 1
    exact transvection_mem_of_three_index
      (coord_inl_ne_coord_inl_of_ne (i := j) (a := b) (b := c') hbc')
      (coord_inl_ne_coord_inl hij.symm c' b) (coord_inl_ne_coord_inl hij.symm b b) t hA hB
  · exact cross_transvection_mem' ε hij hN hZ hbc t

theorem transvection_mem_of_mem_blockCoords_excluded
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hdim : 2 ≤ (rootPB g).dim)
    (hs : 2 ≤ s) (m₀ : Fin s) {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hN : ∀ (i j : Fin s) (hij : i ≠ j),
      theta g ε (SpecialLinearGroup.transvection (i := i) (j := j) hij
        (1 : AdjoinRoot g)) ∈ H)
    (hzero : ∀ i : Fin s, i ≠ m₀ → zeroBlock g ε i ≤ H)
    {x y : Fin n} (hx : x ∈ blockCoords ε m₀) (hy : y ∈ blockCoords ε m₀)
    (hxy : x ≠ y) (t : K) :
    SpecialLinearGroup.transvection hxy t ∈ H := by
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin s)
    (by rw [Fintype.card_fin]; omega) m₀
  let a0 : Fin (rootPB g).dim := ⟨0, by omega⟩
  let w : Fin n := coord ε j a0
  have hw : w ∈ blockCoords ε j := coord_mem_blockCoords j a0
  have hxw : x ≠ w := by
    rcases hxm : ε x with ⟨a', i⟩ | z
    · have hx' : x = coord ε i a' := by rw [coord, ← hxm, Equiv.symm_apply_apply]
      have hi : i = m₀ := (mem_blockCoords_inl (ε := ε) hxm).mp hx
      subst i
      subst x
      exact coord_inl_ne_coord_inl hj.symm a' a0
    · have hx' : x = fixedCoord ε z := by rw [fixedCoord, ← hxm, Equiv.symm_apply_apply]
      subst hx'
      exact (coord_inl_ne_fixed j a0 z).symm
  have hwy : w ≠ y := by
    rcases hym : ε y with ⟨b', i⟩ | z
    · have hy' : y = coord ε i b' := by rw [coord, ← hym, Equiv.symm_apply_apply]
      have hi : i = m₀ := (mem_blockCoords_inl (ε := ε) hym).mp hy
      subst i
      subst y
      exact coord_inl_ne_coord_inl hj a0 b'
    · have hy' : y = fixedCoord ε z := by rw [fixedCoord, ← hym, Equiv.symm_apply_apply]
      subst hy'
      exact coord_inl_ne_fixed j a0 z
  have hA : SpecialLinearGroup.transvection hxw t ∈ H := by
    rcases hxm : ε x with ⟨a', i⟩ | z
    · have hx' : x = coord ε i a' := by rw [coord, ← hxm, Equiv.symm_apply_apply]
      have hi : i = m₀ := (mem_blockCoords_inl (ε := ε) hxm).mp hx
      subst i
      subst x
      rw [transvection_proof_irrel hxw
        (coord_inl_ne_coord_inl (i := m₀) (j := j) hj.symm a' a0) t]
      exact cross_transvection_mem_any (i := m₀) (j := j) ε hdim hj.symm
        (hN m₀ j hj.symm) (hzero j hj) t
    · have hx' : x = fixedCoord ε z := by rw [fixedCoord, ← hxm, Equiv.symm_apply_apply]
      subst hx'
      exact hzero j hj (transvection_mem_zeroBlock ε (fixed_mem_blockCoords j z) hw hxw t)
  have hB : SpecialLinearGroup.transvection hwy (1 : K) ∈ H := by
    rcases hym : ε y with ⟨b', i⟩ | z
    · have hy' : y = coord ε i b' := by rw [coord, ← hym, Equiv.symm_apply_apply]
      have hi : i = m₀ := (mem_blockCoords_inl (ε := ε) hym).mp hy
      subst i
      subst y
      rw [transvection_proof_irrel hwy
        (coord_inl_ne_coord_inl (i := j) (j := m₀) hj a0 b') 1]
      exact cross_transvection_mem_any' (i := m₀) (j := j) ε hdim hj.symm
        (hN j m₀ hj) (hzero j hj) 1
    · have hy' : y = fixedCoord ε z := by rw [fixedCoord, ← hym, Equiv.symm_apply_apply]
      subst hy'
      exact hzero j hj (transvection_mem_zeroBlock ε hw (fixed_mem_blockCoords j z) hwy 1)
  have hcomm := SpecialLinearGroup.commutatorElement_transvection hxw hwy hxy t 1
  rw [mul_one] at hcomm
  rw [← hcomm]
  exact H.commutator_le_self (Subgroup.commutator_mem_commutator hA hB)

theorem transvection_mem_of_avoid_zero
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hdim : 2 ≤ (rootPB g).dim)
    (hs : 2 ≤ s) (m₀ : Fin s) {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hpair : ∀ (i j : Fin s), i ≠ j → pairBlock g ε i j ≤ H)
    (hzero : ∀ i : Fin s, i ≠ m₀ → zeroBlock g ε i ≤ H)
    {x y : Fin n} (hxy : x ≠ y) (t : K) :
    SpecialLinearGroup.transvection hxy t ∈ H := by
  have hN : ∀ (i j : Fin s) (hij : i ≠ j),
      theta g ε (SpecialLinearGroup.transvection (i := i) (j := j) hij
        (1 : AdjoinRoot g)) ∈ H :=
    fun i j hij => hpair i j hij (theta_transvection_one_mem_pairBlock ε hij)
  rcases hx : ε x with ⟨a, i⟩ | zx
  · rcases hy : ε y with ⟨b, j⟩ | zy
    ·
      have hx' : x = coord ε i a := by rw [coord, ← hx, Equiv.symm_apply_apply]
      have hy' : y = coord ε j b := by rw [coord, ← hy, Equiv.symm_apply_apply]
      by_cases hij : i = j
      · subst j
        subst x
        subst y
        by_cases him : i = m₀
        · subst i
          exact transvection_mem_of_mem_blockCoords_excluded ε hdim hs m₀ hN hzero
            (coord_mem_blockCoords m₀ a) (coord_mem_blockCoords m₀ b) hxy t
        · exact hzero i him (transvection_mem_zeroBlock ε (coord_mem_blockCoords i a)
            (coord_mem_blockCoords i b) hxy t)
      · subst x
        subst y
        by_cases him : i = m₀
        · subst i
          have hjm : j ≠ m₀ := by intro h; exact hij (h ▸ rfl)
          rw [transvection_proof_irrel hxy (coord_inl_ne_coord_inl hij a b) t]
          exact cross_transvection_mem_any (i := m₀) (j := j) ε hdim hij
            (hN m₀ j hij) (hzero j hjm) t
        · by_cases hjm : j = m₀
          · subst j
            rw [transvection_proof_irrel hxy (coord_inl_ne_coord_inl him a b) t]
            exact cross_transvection_mem_any' (i := m₀) (j := i) ε hdim (Ne.symm him)
              (hN i m₀ him) (hzero i him) t
          · rw [transvection_proof_irrel hxy (coord_inl_ne_coord_inl hij a b) t]
            exact cross_transvection_mem_any (i := i) (j := j) ε hdim hij
              (hN i j hij) (hzero j hjm) t
    ·
      have hxm : x ∈ blockCoords ε i := (mem_blockCoords_inl (ε := ε) hx).mpr rfl
      have hyf : y ∈ blockCoords ε i := mem_blockCoords_inr (ε := ε) (i := i) (x := y) hy
      by_cases him : i = m₀
      · subst i
        exact transvection_mem_of_mem_blockCoords_excluded ε hdim hs m₀ hN hzero
          hxm hyf hxy t
      · exact hzero i him (transvection_mem_zeroBlock ε hxm hyf hxy t)
  · rcases hy : ε y with ⟨b, j⟩ | zy
    ·
      have hxf : x ∈ blockCoords ε j := mem_blockCoords_inr (ε := ε) (i := j) (x := x) hx
      have hym : y ∈ blockCoords ε j := (mem_blockCoords_inl (ε := ε) hy).mpr rfl
      by_cases hjm : j = m₀
      · subst j
        exact transvection_mem_of_mem_blockCoords_excluded ε hdim hs m₀ hN hzero
          hxf hym hxy t
      · exact hzero j hjm (transvection_mem_zeroBlock ε hxf hym hxy t)
    ·
      exact transvection_mem_of_mem_blockCoords_excluded ε hdim hs m₀ hN hzero
        (mem_blockCoords_inr (ε := ε) (i := m₀) (x := x) hx)
        (mem_blockCoords_inr (ε := ε) (i := m₀) (x := y) hy) hxy t

theorem iSup_blocks_avoid_zero_eq_top
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (hdim : 2 ≤ (rootPB g).dim) (hs : 2 ≤ s) (m₀ : Fin s) :
    (⨆ (i : Fin s) (j : Fin s) (_ : i ≠ j), pairBlock g ε i j) ⊔
      (⨆ (i : Fin s) (_ : i ≠ m₀), zeroBlock g ε i) = ⊤ := by
  let H : Subgroup (SpecialLinearGroup (Fin n) K) :=
    (⨆ (i : Fin s) (j : Fin s) (_ : i ≠ j), pairBlock g ε i j) ⊔
      (⨆ (i : Fin s) (_ : i ≠ m₀), zeroBlock g ε i)
  change H = ⊤
  have hpair : ∀ (i j : Fin s), i ≠ j → pairBlock g ε i j ≤ H := by
    intro i j hij x hx
    exact Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem j
      (Subgroup.mem_iSup_of_mem hij hx)))
  have hzero : ∀ (i : Fin s), i ≠ m₀ → zeroBlock g ε i ≤ H := by
    intro i hi x hx
    exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hi hx))
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := n) (K := K),
    Subgroup.closure_le]
  rintro A ⟨x, y, hxy, c, rfl⟩
  exact transvection_mem_of_avoid_zero ε hdim hs m₀ hpair hzero hxy c

theorem transvection_mem_of_all_blocks
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hdim : 2 ≤ (rootPB g).dim)
    (hs : 1 ≤ s) {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hpair : ∀ (i j : Fin s), i ≠ j → pairBlock g ε i j ≤ H)
    (hzero : ∀ i : Fin s, zeroBlock g ε i ≤ H)
    {x y : Fin n} (hxy : x ≠ y) (t : K) :
    SpecialLinearGroup.transvection hxy t ∈ H := by
  rcases hx : ε x with ⟨a, i⟩ | zx
  · rcases hy : ε y with ⟨b, j⟩ | zy
    · by_cases hij : i = j
      · subst j
        exact hzero i (transvection_mem_zeroBlock ε
          ((mem_blockCoords_inl (ε := ε) hx).mpr rfl)
          ((mem_blockCoords_inl (ε := ε) hy).mpr rfl) hxy t)
      · have hx' : x = coord ε i a := by rw [coord, ← hx, Equiv.symm_apply_apply]
        have hy' : y = coord ε j b := by rw [coord, ← hy, Equiv.symm_apply_apply]
        subst x
        subst y
        rw [transvection_proof_irrel hxy (coord_inl_ne_coord_inl hij a b) t]
        exact cross_transvection_mem_any (i := i) (j := j) ε hdim hij
          (hpair i j hij (theta_transvection_one_mem_pairBlock ε hij)) (hzero j) t
    · exact hzero i (transvection_mem_zeroBlock ε
        ((mem_blockCoords_inl (ε := ε) hx).mpr rfl)
        (mem_blockCoords_inr (ε := ε) (i := i) (x := y) hy) hxy t)
  · rcases hy : ε y with ⟨b, j⟩ | zy
    · exact hzero j (transvection_mem_zeroBlock ε
        (mem_blockCoords_inr (ε := ε) (i := j) (x := x) hx)
        ((mem_blockCoords_inl (ε := ε) hy).mpr rfl) hxy t)
    · let i : Fin s := ⟨0, by omega⟩
      exact hzero i (transvection_mem_zeroBlock ε
        (mem_blockCoords_inr (ε := ε) (i := i) (x := x) hx)
        (mem_blockCoords_inr (ε := ε) (i := i) (x := y) hy) hxy t)

theorem iSup_blocks_eq_top
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (hdim : 2 ≤ (rootPB g).dim) (hs : 1 ≤ s) :
    (⨆ (i : Fin s) (j : Fin s) (_ : i ≠ j), pairBlock g ε i j) ⊔
      (⨆ i, zeroBlock g ε i) = ⊤ := by
  let H : Subgroup (SpecialLinearGroup (Fin n) K) :=
    (⨆ (i : Fin s) (j : Fin s) (_ : i ≠ j), pairBlock g ε i j) ⊔
      (⨆ i, zeroBlock g ε i)
  change H = ⊤
  have hpair : ∀ (i j : Fin s), i ≠ j → pairBlock g ε i j ≤ H := by
    intro i j hij x hx
    exact Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem j
      (Subgroup.mem_iSup_of_mem hij hx)))
  have hzero : ∀ i : Fin s, zeroBlock g ε i ≤ H := by
    intro i x hx
    exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem i hx)
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := n) (K := K),
    Subgroup.closure_le]
  rintro A ⟨x, y, hxy, c, rfl⟩
  exact transvection_mem_of_all_blocks ε hdim hs hpair hzero hxy c

theorem transvection_mem_of_avoid_pair
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hdim : 2 ≤ (rootPB g).dim)
    (hs : 3 ≤ s) {i₀ j₀ : Fin s} (hij₀ : i₀ ≠ j₀)
    {H : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hpair : ∀ (i j : Fin s), i ≠ j → ({i, j} : Finset (Fin s)) ≠ {i₀, j₀} →
      pairBlock g ε i j ≤ H)
    (hzero : ∀ i : Fin s, zeroBlock g ε i ≤ H)
    {x y : Fin n} (hxy : x ≠ y) (t : K) :
    SpecialLinearGroup.transvection hxy t ∈ H := by
  have hN : ∀ (i j : Fin s) (hij : i ≠ j) (_ : ({i, j} : Finset (Fin s)) ≠ {i₀, j₀}),
      theta g ε (SpecialLinearGroup.transvection (i := i) (j := j) hij
        (1 : AdjoinRoot g)) ∈ H :=
    fun i j hij hne => hpair i j hij hne (theta_transvection_one_mem_pairBlock ε hij)
  rcases hx : ε x with ⟨a, i⟩ | zx
  · rcases hy : ε y with ⟨b, j⟩ | zy
    · by_cases hij : i = j
      · subst j
        exact hzero i (transvection_mem_zeroBlock ε
          ((mem_blockCoords_inl (ε := ε) hx).mpr rfl)
          ((mem_blockCoords_inl (ε := ε) hy).mpr rfl) hxy t)
      · have hx' : x = coord ε i a := by rw [coord, ← hx, Equiv.symm_apply_apply]
        have hy' : y = coord ε j b := by rw [coord, ← hy, Equiv.symm_apply_apply]
        subst x
        subst y
        by_cases hne : ({i, j} : Finset (Fin s)) = {i₀, j₀}
        ·
          obtain ⟨l, hli₀, hlj₀⟩ := Fin.exists_ne_and_ne_of_two_lt i₀ j₀ (by omega)
          have hl : l ∉ ({i₀, j₀} : Finset (Fin s)) := by
            simp [Finset.mem_insert, Finset.mem_singleton, hli₀, hlj₀]
          have hli : l ≠ i := by
            intro h
            have : l ∈ ({i₀, j₀} : Finset (Fin s)) := by
              rw [← hne]
              simp [h]
            exact hl this
          have hlj : l ≠ j := by
            intro h
            have : l ∈ ({i₀, j₀} : Finset (Fin s)) := by
              rw [← hne]
              simp [h]
            exact hl this
          let a0 : Fin (rootPB g).dim := ⟨0, by omega⟩
          have hne_il : ({i, l} : Finset (Fin s)) ≠ {i₀, j₀} := by
            intro h
            have : l ∈ ({i₀, j₀} : Finset (Fin s)) := by
              rw [← h]
              simp
            exact hl this
          have hne_lj : ({l, j} : Finset (Fin s)) ≠ {i₀, j₀} := by
            intro h
            have : l ∈ ({i₀, j₀} : Finset (Fin s)) := by
              rw [← h]
              simp
            exact hl this
          have hA : SpecialLinearGroup.transvection
              (coord_inl_ne_coord_inl (ε := ε) (Ne.symm hli) a a0) t ∈ H :=
            cross_transvection_mem_any (i := i) (j := l) ε hdim (Ne.symm hli)
              (hN i l (Ne.symm hli) hne_il) (hzero l) t
          have hB : SpecialLinearGroup.transvection
              (coord_inl_ne_coord_inl (ε := ε) hlj a0 b) (1 : K) ∈ H :=
            cross_transvection_mem_any (i := l) (j := j) ε hdim hlj
              (hN l j hlj hne_lj) (hzero j) 1
          rw [transvection_proof_irrel hxy (coord_inl_ne_coord_inl hij a b) t]
          exact transvection_mem_of_three_index (coord_inl_ne_coord_inl (Ne.symm hli) a a0)
            (coord_inl_ne_coord_inl hlj a0 b) (coord_inl_ne_coord_inl hij a b) t hA hB
        · rw [transvection_proof_irrel hxy (coord_inl_ne_coord_inl hij a b) t]
          exact cross_transvection_mem_any (i := i) (j := j) ε hdim hij
            (hN i j hij hne) (hzero j) t
    · exact hzero i (transvection_mem_zeroBlock ε
        ((mem_blockCoords_inl (ε := ε) hx).mpr rfl)
        (mem_blockCoords_inr (ε := ε) (i := i) (x := y) hy) hxy t)
  · rcases hy : ε y with ⟨b, j⟩ | zy
    · exact hzero j (transvection_mem_zeroBlock ε
        (mem_blockCoords_inr (ε := ε) (i := j) (x := x) hx)
        ((mem_blockCoords_inl (ε := ε) hy).mpr rfl) hxy t)
    · let i : Fin s := ⟨0, by omega⟩
      exact hzero i (transvection_mem_zeroBlock ε
        (mem_blockCoords_inr (ε := ε) (i := i) (x := x) hx)
        (mem_blockCoords_inr (ε := ε) (i := i) (x := y) hy) hxy t)

theorem iSup_blocks_avoid_pair_eq_top
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (hdim : 2 ≤ (rootPB g).dim) (hs : 3 ≤ s) (i₀ j₀ : Fin s) :
    (⨆ (i : Fin s) (j : Fin s)
      (_ : i ≠ j ∧ ({i, j} : Finset (Fin s)) ≠ {i₀, j₀}), pairBlock g ε i j) ⊔
      (⨆ i, zeroBlock g ε i) = ⊤ := by
  let H : Subgroup (SpecialLinearGroup (Fin n) K) :=
    (⨆ (i : Fin s) (j : Fin s)
      (_ : i ≠ j ∧ ({i, j} : Finset (Fin s)) ≠ {i₀, j₀}), pairBlock g ε i j) ⊔
      (⨆ i, zeroBlock g ε i)
  change H = ⊤
  have hpair : ∀ (i j : Fin s), i ≠ j → ({i, j} : Finset (Fin s)) ≠ {i₀, j₀} →
      pairBlock g ε i j ≤ H := by
    intro i j hij hne x hx
    exact Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem j
      (Subgroup.mem_iSup_of_mem ⟨hij, hne⟩ hx)))
  have hzero : ∀ i : Fin s, zeroBlock g ε i ≤ H := by
    intro i x hx
    exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem i hx)
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := n) (K := K),
    Subgroup.closure_le]
  rintro A ⟨x, y, hxy, c, rfl⟩
  by_cases hij₀ : i₀ = j₀
  · have hpair' : ∀ (i j : Fin s), i ≠ j → pairBlock g ε i j ≤ H := by
      intro i j hij
      refine hpair i j hij ?_
      intro h
      have h2 : ({i, j} : Finset (Fin s)).card = 2 := Finset.card_pair hij
      have h1 : ({i₀, j₀} : Finset (Fin s)).card ≤ 1 := by
        rw [hij₀]
        simp
      rw [h] at h2
      omega
    exact transvection_mem_of_all_blocks ε hdim (by omega) hpair' hzero hxy c
  · exact transvection_mem_of_avoid_pair ε hdim hs hij₀ hpair hzero hxy c
