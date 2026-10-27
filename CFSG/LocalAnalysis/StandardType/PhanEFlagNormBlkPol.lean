module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagBlkAct
public import CFSG.LocalAnalysis.StandardType.PhanEFlagPsi
public import CFSG.LocalAnalysis.StandardType.PhanENormPolar

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {d : List ℕ}

private theorem q2cFNP_sg_pow_two (hK : Nat.card K = (2 ^ f) ^ 2) :
    (sg K f) ^ 2 = 1 := by
  ext a
  exact sg_sg hK a

private theorem q2cFNP_sg_ne_one (hK : Nat.card K = (2 ^ f) ^ 2) : sg K f ≠ 1 := by
  intro h
  classical
  haveI := Fintype.ofFinite K
  have hf : 1 ≤ f := by
    by_contra h'
    have h0 : f = 0 := by omega
    subst h0
    have h1 : Nat.card K = 1 := by simpa using hK
    have := Finite.one_lt_card (α := K)
    omega
  have hlt : 2 ^ f < Nat.card K := by
    rw [hK, pow_two]
    calc 2 ^ f = 2 ^ f * 1 := (Nat.mul_one _).symm
      _ < 2 ^ f * 2 ^ f :=
        Nat.mul_lt_mul_of_pos_left
          (one_lt_pow' (by norm_num : 1 < (2 : ℕ)) (by omega : f ≠ 0))
          (pow_pos (by norm_num) f)
  have hpos : 0 < Nat.card {a : K // sg K f a ≠ a} :=
    lt_of_lt_of_le (by omega) (card_sg_moved_ge (K := K) (f := f) hK)
  set s : Finset K := Finset.univ.filter (fun a => sg K f a ≠ a) with hs
  have hscard : s.card = Nat.card {a : K // sg K f a ≠ a} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hspos : 0 < s.card := by rw [hscard]; exact hpos
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hspos
  rw [hs, Finset.mem_filter] at ha
  exact ha.2 (by rw [h]; rfl)

private theorem q2cFNP_glLin_one {n : ℕ} :
    glLin (1 : GL (Fin n) K) = LinearEquiv.refl K (Fin n → K) := by
  ext v
  rw [glLin_apply]
  simp

private theorem q2cFNP_glLin_mul {n : ℕ} (g h : GL (Fin n) K) :
    glLin (g * h) = (glLin h).trans (glLin g) := by
  ext v
  rw [glLin_apply, LinearEquiv.trans_apply, glLin_apply, glLin_apply,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]

private theorem q2cFNP_glLin_inv {n : ℕ} (g : GL (Fin n) K) :
    glLin g⁻¹ = (glLin g).symm := by
  apply LinearEquiv.ext
  intro v
  apply (glLin g).injective
  rw [LinearEquiv.apply_symm_apply]
  have h2 : glLin g (glLin g⁻¹ v) = v := by
    have h3 : glLin (g * g⁻¹) v = glLin g (glLin g⁻¹ v) := by
      rw [q2cFNP_glLin_mul, LinearEquiv.trans_apply]
    rw [← h3, mul_inv_cancel, q2cFNP_glLin_one]
    rfl
  exact h2

private theorem q2cFNP_hermLin_eq_herm {m : ℕ} (u v : Fin m → K) :
    hermLin K f m 0 m u v = herm (sg K f) u v := by
  rw [hermLin, LinearMap.sum_apply, herm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

private theorem q2cFNP_block_invol (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d)
    (pol : List Bool) {b : ℕ} (hb : b + 1 < d.length) (hpol : pol.getD b false = true)
    {M : GL (Fin n) K} (hM : StabV n d M)
    (hinv : ∀ x ∈ refSet K n d,
      flagAct M (flagPsi hK hd pol (flagAct M (flagPsi hK hd pol x))) = x)
    (U : Submodule K (Fin (blockSize d b) → K)) :
    (perpB K f (blockSize d b) 0 (blockSize d b)
      ((perpB K f (blockSize d b) 0 (blockSize d b) U).map (blkMat d b M))).map
        (blkMat d b M) = U := by
  have ha_n : d.getD b 0 ≤ n := q2cFPt_le_last hd (by omega : b < d.length)
  have hc_n : d.getD (b + 1) 0 ≤ n := q2cFPt_le_last hd hb
  set X : Submodule K (Fin n → K) := Vsub n (d.getD b 0) ⊔ U.map (blkIn n d b) with hX
  have hX1 : Vsub n (d.getD b 0) ≤ X := by rw [hX]; exact le_sup_left
  have hX2 : X ≤ Vsub n (d.getD (b + 1) 0) := by rw [hX]; exact sup_map_blkIn_le_Vsub hd hb U
  obtain ⟨x, hxmem, hxE⟩ := exists_mem_refSet_E_eq hd hb hX1 hX2
  set l : ℕ := finrank K X with hl
  set s' : ℕ := l - d.getD b 0 with hs'
  have hs'le : s' ≤ blockSize d b := by
    have hXc : finrank K X ≤ finrank K (Vsub n (d.getD (b + 1) 0)) :=
      Submodule.finrank_mono hX2
    rw [finrank_Vsub hc_n] at hXc
    simp only [blockSize] at hXc ⊢
    omega
  have ha_l : d.getD b 0 + s' = l := by
    have haX : d.getD b 0 ≤ finrank K X := by
      have h := Submodule.finrank_mono hX1
      rwa [finrank_Vsub ha_n] at h
    omega
  set y : FlagK K n := flagPsi hK hd pol x with hy
  set z : FlagK K n := flagAct M y with hz
  have hy_ref : y ∈ refSet K n d := flagPsi_mem hK hd pol hxmem
  have hz_ref : z ∈ refSet K n d := StabV.flagAct_mem_refSet hM hy_ref
  have hkey := congrArg (fun t : FlagK K n => t.E l) (hinv x hxmem)
  rw [flagAct, flagMap_E, hxE] at hkey
  have hz_level : z.E (d.getD b 0 + (blockSize d b - s')) =
      (perpB K f n (d.getD b 0) (d.getD (b + 1) 0) X ⊓ Vsub n (d.getD (b + 1) 0)).map
        (glLin M).toLinearMap := by
    rw [hz, flagAct, flagMap_E]
    congr 1
    rw [hy, flagPsi_E hK hd pol hxmem hb (by simp only [blockSize] at hs'le ⊢; omega)]
    rw [psiSub, if_pos hpol]
    congr 1
    rw [show blockSize d b - (blockSize d b - s') = s' by omega]
    rw [ha_l, hxE]
  have hw_level : (flagPsi hK hd pol z).E l =
      perpB K f n (d.getD b 0) (d.getD (b + 1) 0)
        (z.E (d.getD b 0 + (blockSize d b - s'))) ⊓ Vsub n (d.getD (b + 1) 0) := by
    rw [show l = d.getD b 0 + s' from ha_l.symm]
    rw [flagPsi_E hK hd pol hz_ref hb hs'le, psiSub, if_pos hpol]
  rw [hw_level, hz_level] at hkey
  have hU : X.map (blkOut n d b) = U := by
    rw [hX, map_blkOut_sup_map_blkIn hd hb U]
  have hWout : ((perpB K f n (d.getD b 0) (d.getD (b + 1) 0) X ⊓
        Vsub n (d.getD (b + 1) 0)).map (glLin M).toLinearMap).map (blkOut n d b) =
      (perpB K f (blockSize d b) 0 (blockSize d b) (X.map (blkOut n d b))).map
        (blkMat d b M) := by
    rw [perpB_inf_Vsub_eq f hd hb X, map_sup_map_blkIn hd hb hM, map_blkOut_sup_map_blkIn hd hb]
  rw [perpB_inf_Vsub_eq f hd hb] at hkey
  rw [map_sup_map_blkIn hd hb hM] at hkey
  rw [hWout] at hkey
  have hblk : (perpB K f (blockSize d b) 0 (blockSize d b)
        ((perpB K f (blockSize d b) 0 (blockSize d b) (X.map (blkOut n d b))).map
          (blkMat d b M))).map (blkMat d b M) = X.map (blkOut n d b) := by
    have := congrArg (Submodule.map (blkOut n d b)) hkey
    rwa [map_blkOut_sup_map_blkIn hd hb] at this
  rw [hU] at hblk
  exact hblk

private noncomputable def q2cFNP_MbarEquiv (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (M : GL (Fin n) K) (hM : StabV n d M) :
    (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K) :=
  LinearEquiv.ofBijective (blkMat d b M) (blkMat_bijective hd hb hM)

private noncomputable def q2cFNP_MbarInv (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (M : GL (Fin n) K) (hM : StabV n d M) :
    (Fin (blockSize d b) → K) →ₗ[K] (Fin (blockSize d b) → K) :=
  (q2cFNP_MbarEquiv hd hb M hM).symm

private theorem q2cFNP_MbarInv_apply (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (M : GL (Fin n) K) (hM : StabV n d M) (v : Fin (blockSize d b) → K) :
    q2cFNP_MbarInv hd hb M hM (blkMat d b M v) = v :=
  LinearEquiv.symm_apply_apply (q2cFNP_MbarEquiv hd hb M hM) v

private theorem q2cFNP_Mbar_apply_MbarInv (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (M : GL (Fin n) K) (hM : StabV n d M) (v : Fin (blockSize d b) → K) :
    blkMat d b M (q2cFNP_MbarInv hd hb M hM v) = v :=
  LinearEquiv.apply_symm_apply (q2cFNP_MbarEquiv hd hb M hM) v

private theorem q2cFNP_mem_perpB_iff {m : ℕ} {U : Submodule K (Fin m → K)}
    {v : Fin m → K} :
    v ∈ perpB K f m 0 m U ↔ ∀ u ∈ U, hermLin K f m 0 m u v = 0 := by
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker]

private noncomputable def q2cFNP_form (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (M : GL (Fin n) K) (hM : StabV n d M) :
    (Fin (blockSize d b) → K) →ₛₗ[(sg K f).toRingHom]
      (Fin (blockSize d b) → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (sg K f).toRingHom (RingHom.id K)
    (fun u v => hermL (sg K f) u (q2cFNP_MbarInv hd hb M hM v))
    (fun u₁ u₂ v => by
      rw [hermL_apply, hermL_apply, hermL_apply, herm_add_left])
    (fun c u v => by
      rw [hermL_apply, hermL_apply, herm_smul_left, smul_eq_mul]
      rfl)
    (fun u v₁ v₂ => by
      rw [map_add, hermL_apply, hermL_apply, hermL_apply, herm_add_right])
    (fun c u v => by
      rw [map_smul, hermL_apply, hermL_apply, herm_smul_right, smul_eq_mul]
      rfl)

private theorem q2cFNP_form_apply (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (M : GL (Fin n) K) (hM : StabV n d M) (u v : Fin (blockSize d b) → K) :
    q2cFNP_form (f := f) hd hb M hM u v =
      hermLin K f (blockSize d b) 0 (blockSize d b) u (q2cFNP_MbarInv hd hb M hM v) := by
  change hermL (sg K f) u (q2cFNP_MbarInv hd hb M hM v) =
    hermLin K f (blockSize d b) 0 (blockSize d b) u (q2cFNP_MbarInv hd hb M hM v)
  rw [hermL_apply, q2cFNP_hermLin_eq_herm]

private theorem q2cFNP_form_nondegenerate (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length)
    (M : GL (Fin n) K) (hM : StabV n d M) :
    (q2cFNP_form (f := f) hd hb M hM).Nondegenerate := by
  constructor
  · intro u hu
    apply eq_zero_of_herm (sg K f)
    intro w
    have hw := hu (blkMat d b M w)
    rw [q2cFNP_form_apply, q2cFNP_MbarInv_apply, q2cFNP_hermLin_eq_herm] at hw
    exact hw
  · intro v hv
    have hzero : q2cFNP_MbarInv hd hb M hM v = 0 := by
      funext i
      have h := hv (Pi.single i (1 : K))
      rw [q2cFNP_form_apply, q2cFNP_hermLin_eq_herm, herm_single_left] at h
      simpa using h
    have := congrArg (blkMat d b M) hzero
    rwa [q2cFNP_Mbar_apply_MbarInv, map_zero] at this

private theorem q2cFNP_form_orthogonalBilin_eq (hd : IsCut n d) {b : ℕ}
    (hb : b + 1 < d.length) (M : GL (Fin n) K) (hM : StabV n d M)
    (U : Submodule K (Fin (blockSize d b) → K)) :
    U.orthogonalBilin (q2cFNP_form (f := f) hd hb M hM) =
      (perpB K f (blockSize d b) 0 (blockSize d b) U).map (blkMat d b M) := by
  ext v
  rw [Submodule.mem_orthogonalBilin, Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨q2cFNP_MbarInv hd hb M hM v, ?_, q2cFNP_Mbar_apply_MbarInv hd hb M hM v⟩
    rw [q2cFNP_mem_perpB_iff]
    intro u hu
    have h := hv u hu
    rw [q2cFNP_form_apply, q2cFNP_hermLin_eq_herm] at h
    rwa [q2cFNP_hermLin_eq_herm]
  · rintro ⟨w, hw, rfl⟩ u hu
    rw [q2cFNP_form_apply, q2cFNP_MbarInv_apply]
    exact (q2cFNP_mem_perpB_iff.mp hw) u hu

private theorem q2cFNP_form_perp_perp (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d)
    (pol : List Bool) {b : ℕ} (hb : b + 1 < d.length) (hpol : pol.getD b false = true)
    {M : GL (Fin n) K} (hM : StabV n d M)
    (hinv : ∀ x ∈ refSet K n d,
      flagAct M (flagPsi hK hd pol (flagAct M (flagPsi hK hd pol x))) = x) :
    ∀ U : Submodule K (Fin (blockSize d b) → K),
      (U.orthogonalBilin (q2cFNP_form (f := f) hd hb M hM)).orthogonalBilin
        (q2cFNP_form (f := f) hd hb M hM) = U := by
  intro U
  rw [q2cFNP_form_orthogonalBilin_eq hd hb M hM U,
    q2cFNP_form_orthogonalBilin_eq hd hb M hM
      ((perpB K f (blockSize d b) 0 (blockSize d b) U).map (blkMat d b M))]
  exact q2cFNP_block_invol hK hd pol hb hpol hM hinv U

theorem exists_blockEquiv_pol (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut n d) (pol : List Bool)
    {b : ℕ} (hb : b + 1 < d.length) (hpol : pol.getD b false = true) {M : GL (Fin n) K}
    (hM : StabV n d M)
    (hinv : ∀ x ∈ refSet K n d,
      flagAct M (flagPsi hK hd pol (flagAct M (flagPsi hK hd pol x))) = x) :
    ∃ E : (Fin (blockSize d b) → K) ≃ₗ[K] (Fin (blockSize d b) → K),
      ∀ e : GL (Fin n) K, StabV n d e →
        (∀ w, glLin e (blkIn n d b w) = blkIn n d b (E w)) →
        ∀ X : Submodule K (Fin n → K), Vsub n (d.getD b 0) ≤ X →
          X ≤ Vsub n (d.getD (b + 1) 0) →
          ((perpB K f n (d.getD b 0) (d.getD (b + 1) 0) (X.map (glLin e⁻¹).toLinearMap) ⊓
            Vsub n (d.getD (b + 1) 0)).map (glLin M).toLinearMap).map (glLin e).toLinearMap =
              perpB K f n (d.getD b 0) (d.getD (b + 1) 0) X ⊓ Vsub n (d.getD (b + 1) 0) := by
  obtain ⟨E, hE⟩ := Norm.exists_coord_perp (sg K f) (q2cFNP_sg_pow_two hK)
    (q2cFNP_sg_ne_one hK)
    (by simp only [blockSize]; exact Nat.sub_pos_of_lt (hd.strict b hb))
    (q2cFNP_form_nondegenerate (f := f) hd hb M hM)
    (q2cFNP_form_perp_perp (f := f) hK hd pol hb hpol hM hinv)
  refine ⟨E, ?_⟩
  intro e he_stab he X hX1 hX2
  have hEperp : ∀ W : Submodule K (Fin (blockSize d b) → K),
      ((perpB K f (blockSize d b) 0 (blockSize d b) W).map (blkMat d b M)).map E.toLinearMap =
        perpB K f (blockSize d b) 0 (blockSize d b) (W.map E.toLinearMap) := by
    intro W
    have hcomap : W.orthogonalBilin (q2cFNP_form (f := f) hd hb M hM) =
        (perpB K f (blockSize d b) 0 (blockSize d b) (W.map E.toLinearMap)).comap
          E.toLinearMap := by
      ext v
      rw [Submodule.mem_comap, q2cFNP_mem_perpB_iff]
      constructor
      · intro hv w hw
        obtain ⟨u, hu, rfl⟩ := hw
        have h := (hE W v).mp hv u hu
        rwa [q2cFNP_hermLin_eq_herm]
      · intro hv
        rw [hE W v]
        intro u hu
        have h := hv (E u) ⟨u, hu, rfl⟩
        rwa [q2cFNP_hermLin_eq_herm] at h
    calc ((perpB K f (blockSize d b) 0 (blockSize d b) W).map (blkMat d b M)).map
          E.toLinearMap
        = (W.orthogonalBilin (q2cFNP_form (f := f) hd hb M hM)).map E.toLinearMap := by
          rw [q2cFNP_form_orthogonalBilin_eq hd hb M hM W]
      _ = ((perpB K f (blockSize d b) 0 (blockSize d b) (W.map E.toLinearMap)).comap
            E.toLinearMap).map E.toLinearMap := by rw [hcomap]
      _ = perpB K f (blockSize d b) 0 (blockSize d b) (W.map E.toLinearMap) :=
          Submodule.map_comap_eq_of_surjective E.surjective _
  let U : Submodule K (Fin (blockSize d b) → K) := X.map (blkOut n d b)
  have hUX : X = Vsub n (d.getD b 0) ⊔ (U.map (blkIn n d b)) := by
    rw [eq_sup_map_blkIn hd hb hX1 hX2]
  have hblk_inv : (blkMat d b e⁻¹) = E.symm.toLinearMap := by
    apply LinearMap.ext
    intro w
    show blkOut n d b (glLin e⁻¹ (blkIn n d b w)) = E.symm w
    have hinv' : glLin e⁻¹ (blkIn n d b w) = blkIn n d b (E.symm w) := by
      rw [q2cFNP_glLin_inv]
      apply (glLin e).injective
      rw [LinearEquiv.apply_symm_apply, he (E.symm w), E.apply_symm_apply]
    rw [hinv', blkOut_blkIn hd hb]
  have hXe : X.map (glLin e⁻¹).toLinearMap =
      Vsub n (d.getD b 0) ⊔ (U.map E.symm.toLinearMap).map (blkIn n d b) := by
    rw [hUX, map_sup_map_blkIn hd hb (StabV.inv he_stab), hblk_inv]
  have hCe : perpB K f n (d.getD b 0) (d.getD (b + 1) 0)
        (X.map (glLin e⁻¹).toLinearMap) ⊓ Vsub n (d.getD (b + 1) 0) =
      Vsub n (d.getD b 0) ⊔ ((perpB K f (blockSize d b) 0 (blockSize d b)
        (U.map E.symm.toLinearMap)).map (blkIn n d b)) := by
    rw [hXe, perpB_inf_Vsub_eq f hd hb, map_blkOut_sup_map_blkIn hd hb]
  have hMe : (perpB K f n (d.getD b 0) (d.getD (b + 1) 0)
        (X.map (glLin e⁻¹).toLinearMap) ⊓ Vsub n (d.getD (b + 1) 0)).map
          (glLin M).toLinearMap =
      Vsub n (d.getD b 0) ⊔ ((perpB K f (blockSize d b) 0 (blockSize d b)
        (U.map E.symm.toLinearMap)).map (blkMat d b M)).map (blkIn n d b) := by
    rw [hCe, map_sup_map_blkIn hd hb hM]
  have hblk_e : (blkMat d b e) = E.toLinearMap := by
    apply LinearMap.ext
    intro w
    show blkOut n d b (glLin e (blkIn n d b w)) = E w
    rw [he w, blkOut_blkIn hd hb]
  have hMe' : ((perpB K f n (d.getD b 0) (d.getD (b + 1) 0)
        (X.map (glLin e⁻¹).toLinearMap) ⊓ Vsub n (d.getD (b + 1) 0)).map
          (glLin M).toLinearMap).map (glLin e).toLinearMap =
      Vsub n (d.getD b 0) ⊔ (((perpB K f (blockSize d b) 0 (blockSize d b)
        (U.map E.symm.toLinearMap)).map (blkMat d b M)).map (blkMat d b e)).map
          (blkIn n d b) := by
    rw [hMe, map_sup_map_blkIn hd hb he_stab]
  rw [hblk_e] at hMe'
  have hEE : (U.map E.symm.toLinearMap).map E.toLinearMap = U := by
    rw [← Submodule.map_comp]
    have hcomp : E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact E.apply_symm_apply v
    rw [hcomp, Submodule.map_id]
  rw [hEperp (U.map E.symm.toLinearMap), hEE] at hMe'
  have hPX : perpB K f n (d.getD b 0) (d.getD (b + 1) 0) X ⊓ Vsub n (d.getD (b + 1) 0) =
      Vsub n (d.getD b 0) ⊔ (perpB K f (blockSize d b) 0 (blockSize d b) U).map
        (blkIn n d b) := by
    rw [perpB_inf_Vsub_eq f hd hb]
  rw [hPX]
  exact hMe'

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
