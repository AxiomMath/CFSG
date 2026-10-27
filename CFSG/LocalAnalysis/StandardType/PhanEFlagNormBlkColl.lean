module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagBlkAct
public import CFSG.LocalAnalysis.StandardType.PhanEFlagPsi
public import CFSG.LocalAnalysis.StandardType.PhanENormColl

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {d : List ℕ}

private theorem q2cFNC_sgS_eq_map (hK : Nat.card K = (2 ^ f) ^ 2)
    (U : Submodule K (Fin n → K)) :
    sgS K f n U = U.map (sgv K f n) := by
  ext v
  rw [mem_sgS, Submodule.mem_map]
  constructor
  · intro hv
    exact ⟨sgv K f n v, hv, sgv_sgv hK v⟩
  · rintro ⟨u, hu, rfl⟩
    rw [sgv_sgv hK]
    exact hu

private theorem q2cFNC_coordSigma_sgv (n : ℕ) :
    CFSG.ClassicalInvolution.Phan.PhanE.Norm.coordSigma (sg K f) n = sgv K f n := by
  ext v i
  rfl

private theorem q2cFNC_sg_sq (hK : Nat.card K = (2 ^ f) ^ 2) :
    (sg K f : K ≃+* K) ^ 2 = 1 := by
  ext a
  change sg K f (sg K f a) = a
  rw [sg_sg hK]

private theorem q2cFNC_sg_ne_one (hK : Nat.card K = (2 ^ f) ^ 2) :
    (sg K f : K ≃+* K) ≠ 1 := by
  obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne (K := K) (p := 2)
    (f := f) hK
  intro h
  exact ha (by simpa using congrArg (fun φ : K ≃+* K => φ a) h)

private theorem q2cFNC_glLin_inv_apply (e : GL (Fin n) K) (v : Fin n → K) :
    glLin e⁻¹ (glLin e v) = v := by
  rw [glLin_apply, glLin_apply, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul,
    inv_mul_cancel e, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

private theorem q2cFNC_map_blkIn_map_of {b : ℕ} {e : GL (Fin n) K}
    {F : (Fin (blockSize d b) → K) →ₗ[K] (Fin (blockSize d b) → K)}
    (he : ∀ w, glLin e (blkIn n d b w) = blkIn n d b (F w))
    (U : Submodule K (Fin (blockSize d b) → K)) :
    (U.map (blkIn n d b)).map (glLin e).toLinearMap =
      (U.map F).map (blkIn n d b) := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨F w, Submodule.mem_map_of_mem hw, (he w).symm⟩
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨blkIn n d b w, Submodule.mem_map_of_mem hw, he w⟩

private theorem q2cFNC_map_symm_map {b : ℕ}
    (E : (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K))
    (U : Submodule K (Fin (blockSize d b) → K)) :
    (U.map E.symm.toLinearMap).map E.toLinearMap = U := by
  rw [← Submodule.map_comp]
  have h : E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id := by
    ext v
    simp
  rw [h, Submodule.map_id]

private theorem q2cFNC_block_invol (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d)
    (pol : List Bool) {b : ℕ} (hb : b + 1 < d.length)
    (hpol : pol.getD b false = false) {M : GL (Fin n) K} (hM : StabV n d M)
    (hinv : ∀ x ∈ refSet K n d,
      flagAct M (flagPsi hK hd pol (flagAct M (flagPsi hK hd pol x))) = x) :
    ∀ U : Submodule K (Fin (blockSize d b) → K),
      (U.map ((blkMat d b M).comp (sgv K f (blockSize d b)))).map
        ((blkMat d b M).comp (sgv K f (blockSize d b))) = U := by
  intro U
  have hb' : b < d.length := by omega
  have hlt : d.getD b 0 < d.getD (b + 1) 0 := hd.strict b hb
  have hsc : d.getD b 0 + blockSize d b = d.getD (b + 1) 0 := by
    simp only [blockSize]; omega
  let X : Submodule K (Fin n → K) := Vsub n (d.getD b 0) ⊔ U.map (blkIn n d b)
  have hX1 : Vsub n (d.getD b 0) ≤ X := le_sup_left
  have hX2 : X ≤ Vsub n (d.getD (b + 1) 0) := sup_map_blkIn_le_Vsub hd hb U
  obtain ⟨x, hx, hxE⟩ := exists_mem_refSet_E_eq hd hb hX1 hX2
  have hxn : d.getD b 0 ≤ n := q2cFPt_le_last hd hb'
  have hcn : d.getD (b + 1) 0 ≤ n := q2cFPt_le_last hd (by omega)
  have hXdim_le : finrank K X ≤ d.getD (b + 1) 0 := by
    calc finrank K X ≤ finrank K (Vsub n (d.getD (b + 1) 0)) :=
          Submodule.finrank_mono hX2
      _ = d.getD (b + 1) 0 := finrank_Vsub hcn
  have hXdim_ge : d.getD b 0 ≤ finrank K X := by
    calc d.getD b 0 = finrank K (Vsub n (d.getD b 0)) := (finrank_Vsub hxn).symm
      _ ≤ finrank K X := Submodule.finrank_mono hX1
  let s' := finrank K X - d.getD b 0
  have hs'_le : s' ≤ blockSize d b := by
    change finrank K X - d.getD b 0 ≤ blockSize d b
    simp only [blockSize]; omega
  have hj : finrank K X = d.getD b 0 + s' := by
    change finrank K X = d.getD b 0 + (finrank K X - d.getD b 0)
    omega
  have hy_mem : flagPsi hK hd pol x ∈ refSet K n d := flagPsi_mem hK hd pol hx
  have hyE : (flagPsi hK hd pol x).E (d.getD b 0 + s') = sgS K f n X := by
    rw [flagPsi_E hK hd pol hx hb hs'_le, psiSub, if_neg (by rw [hpol]; simp),
      ← hj, hxE]
  have hw_mem : flagAct M (flagPsi hK hd pol x) ∈ refSet K n d :=
    StabV.flagAct_mem_refSet hM hy_mem
  have hwE : (flagAct M (flagPsi hK hd pol x)).E (d.getD b 0 + s') =
      (sgS K f n X).map (glLin M).toLinearMap := by
    show (flagMap (glLin M) (flagPsi hK hd pol x)).E (d.getD b 0 + s') = _
    rw [flagMap_E, hyE]
  have hzE : (flagPsi hK hd pol (flagAct M (flagPsi hK hd pol x))).E
      (d.getD b 0 + s') =
      sgS K f n ((sgS K f n X).map (glLin M).toLinearMap) := by
    rw [flagPsi_E hK hd pol hw_mem hb hs'_le, psiSub, if_neg (by rw [hpol]; simp), hwE]
  have hfin : (sgS K f n ((sgS K f n X).map (glLin M).toLinearMap)).map
      (glLin M).toLinearMap = X := by
    have h : (flagAct M (flagPsi hK hd pol (flagAct M (flagPsi hK hd pol x)))).E
        (finrank K X) = x.E (finrank K X) :=
      congrArg (fun y : FlagK K n => y.E (finrank K X)) (hinv x hx)
    change (flagMap (glLin M) (flagPsi hK hd pol (flagAct M (flagPsi hK hd pol x)))).E
        (finrank K X) = x.E (finrank K X) at h
    rw [flagMap_E, hxE, hj, hzE] at h
    exact h
  let P : Submodule K (Fin (blockSize d b) → K) := sgS K f (blockSize d b) U
  let Q : Submodule K (Fin (blockSize d b) → K) :=
    sgS K f (blockSize d b) (P.map (blkMat d b M))
  have hXU : X = Vsub n (d.getD b 0) ⊔ U.map (blkIn n d b) := rfl
  have h1c : sgS K f n X = Vsub n (d.getD b 0) ⊔ P.map (blkIn n d b) := by
    rw [hXU, sgS_sup_map_blkIn (hK := hK)]
  have h2c : (sgS K f n X).map (glLin M).toLinearMap =
      Vsub n (d.getD b 0) ⊔ (P.map (blkMat d b M)).map (blkIn n d b) := by
    rw [h1c, map_sup_map_blkIn hd hb hM]
  have h3c : sgS K f n ((sgS K f n X).map (glLin M).toLinearMap) =
      Vsub n (d.getD b 0) ⊔ Q.map (blkIn n d b) := by
    rw [h2c, sgS_sup_map_blkIn (hK := hK)]
  have h4c : (sgS K f n ((sgS K f n X).map (glLin M).toLinearMap)).map
      (glLin M).toLinearMap =
      Vsub n (d.getD b 0) ⊔ (Q.map (blkMat d b M)).map (blkIn n d b) := by
    rw [h3c, map_sup_map_blkIn hd hb hM]
  have hA : X = Vsub n (d.getD b 0) ⊔ (Q.map (blkMat d b M)).map (blkIn n d b) :=
    hfin.symm.trans h4c
  have hQ : Q.map (blkMat d b M) = U := by
    have h := congrArg (fun Y : Submodule K (Fin n → K) => Y.map (blkOut n d b)) hA
    rw [hXU] at h
    rw [map_blkOut_sup_map_blkIn hd hb U,
        map_blkOut_sup_map_blkIn hd hb (Q.map (blkMat d b M))] at h
    exact h.symm
  have h1' : U.map ((blkMat d b M).comp (sgv K f (blockSize d b))) =
      (U.map (sgv K f (blockSize d b))).map (blkMat d b M) :=
    Submodule.map_comp (sgv K f (blockSize d b)) (blkMat d b M) U
  have h2' : ((U.map (sgv K f (blockSize d b))).map (blkMat d b M)).map
      ((blkMat d b M).comp (sgv K f (blockSize d b))) =
      (((U.map (sgv K f (blockSize d b))).map (blkMat d b M)).map
        (sgv K f (blockSize d b))).map (blkMat d b M) :=
    Submodule.map_comp (sgv K f (blockSize d b)) (blkMat d b M)
      ((U.map (sgv K f (blockSize d b))).map (blkMat d b M))
  rw [h1', h2']
  rw [← q2cFNC_sgS_eq_map (hK := hK) (U := U)]
  rw [← q2cFNC_sgS_eq_map (hK := hK)
      (U := (sgS K f (blockSize d b) U).map (blkMat d b M))]
  exact hQ

theorem exists_blockEquiv_coll (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d) (pol : List Bool)
    {b : ℕ} (hb : b + 1 < d.length) (hpol : pol.getD b false = false) {M : GL (Fin n) K}
    (hM : StabV n d M)
    (hinv : ∀ x ∈ refSet K n d,
      flagAct M (flagPsi hK hd pol (flagAct M (flagPsi hK hd pol x))) = x) :
    ∃ E : (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K),
      ∀ e : GL (Fin n) K, StabV n d e →
        (∀ w, glLin e (blkIn n d b w) = blkIn n d b (E w)) →
        ∀ X : Submodule K (Fin n → K), Vsub n (d.getD b 0) ≤ X →
          X ≤ Vsub n (d.getD (b + 1) 0) →
          ((sgS K f n (X.map (glLin e⁻¹).toLinearMap)).map (glLin M).toLinearMap).map
            (glLin e).toLinearMap = sgS K f n X := by
  obtain ⟨E, hE⟩ := CFSG.ClassicalInvolution.Phan.PhanE.Norm.exists_coord_equiv_map (sg K f)
    (q2cFNC_sg_sq hK) (q2cFNC_sg_ne_one hK) (by
      have h := hd.strict b hb; simp only [blockSize]; omega)
    ((blkMat d b M).comp (sgv K f (blockSize d b)))
    (q2cFNC_block_invol hK hd pol hb hpol hM hinv)
  refine ⟨E, ?_⟩
  intro e he heblock X h1 h2
  have hb' : b < d.length := by omega
  set W : Submodule K (Fin (blockSize d b) → K) := X.map (blkOut n d b) with hWdef
  have hXeq : X = Vsub n (d.getD b 0) ⊔ W.map (blkIn n d b) := by
    rw [hWdef]
    exact eq_sup_map_blkIn hd hb h1 h2
  have hb_inv : ∀ w : Fin (blockSize d b) → K,
      glLin e⁻¹ (blkIn n d b w) = blkIn n d b (E.symm w) := by
    intro w
    have h1' : glLin e (blkIn n d b (E.symm w)) = blkIn n d b w := by
      rw [heblock, E.apply_symm_apply]
    have h2' := congrArg (fun v => glLin e⁻¹ v) h1'
    rw [q2cFNC_glLin_inv_apply] at h2'
    exact h2'.symm
  have hstep1 : X.map (glLin e⁻¹).toLinearMap =
      Vsub n (d.getD b 0) ⊔ (W.map E.symm.toLinearMap).map (blkIn n d b) := by
    rw [hXeq, Submodule.map_sup, StabV.inv he b hb',
      q2cFNC_map_blkIn_map_of (F := E.symm.toLinearMap) hb_inv W]
  have hstep2 : sgS K f n (X.map (glLin e⁻¹).toLinearMap) =
      Vsub n (d.getD b 0) ⊔ (sgS K f (blockSize d b)
        (W.map E.symm.toLinearMap)).map (blkIn n d b) := by
    rw [hstep1, sgS_sup_map_blkIn (hK := hK)]
  have hstep3 : (sgS K f n (X.map (glLin e⁻¹).toLinearMap)).map
      (glLin M).toLinearMap =
      Vsub n (d.getD b 0) ⊔ ((sgS K f (blockSize d b)
        (W.map E.symm.toLinearMap)).map (blkMat d b M)).map (blkIn n d b) := by
    rw [hstep2, map_sup_map_blkIn hd hb hM]
  have hstep4 : ((sgS K f n (X.map (glLin e⁻¹).toLinearMap)).map
      (glLin M).toLinearMap).map (glLin e).toLinearMap =
      Vsub n (d.getD b 0) ⊔ (((sgS K f (blockSize d b)
        (W.map E.symm.toLinearMap)).map (blkMat d b M)).map E.toLinearMap).map
        (blkIn n d b) := by
    rw [hstep3, Submodule.map_sup, he b hb',
      q2cFNC_map_blkIn_map_of (F := E.toLinearMap) heblock
        ((sgS K f (blockSize d b) (W.map E.symm.toLinearMap)).map (blkMat d b M))]
  have hblock : ((sgS K f (blockSize d b) (W.map E.symm.toLinearMap)).map
      (blkMat d b M)).map E.toLinearMap = sgS K f (blockSize d b) W := by
    have h := hE (W.map E.symm.toLinearMap)
    rw [q2cFNC_coordSigma_sgv] at h
    rw [Submodule.map_comp (sgv K f (blockSize d b)) (blkMat d b M)
      (W.map E.symm.toLinearMap)] at h
    rw [← q2cFNC_sgS_eq_map (hK := hK) (U := W.map E.symm.toLinearMap)] at h
    rw [q2cFNC_map_symm_map E W] at h
    rw [← q2cFNC_sgS_eq_map (hK := hK) (U := W)] at h
    exact h
  have hright : sgS K f n X = Vsub n (d.getD b 0) ⊔
      (sgS K f (blockSize d b) W).map (blkIn n d b) := by
    rw [hXeq, sgS_sup_map_blkIn (hK := hK)]
  rw [hstep4, hblock, hright]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
