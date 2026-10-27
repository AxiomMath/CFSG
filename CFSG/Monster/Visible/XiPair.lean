module

public import CFSG.Monster.Visible.Pair
public import CFSG.Monster.Xi.Conj
public import CFSG.Monster.Xi.Lattice
import CFSG.Monster.Visible.SignFixed

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Xi Matrix

@[expose] def gXiU : GL (Fin 24) ℚ := ⟨gXi, gXiᵀ, gXi_mul_transpose_self, gXi_transpose_mul_self⟩

theorem coe_gXiU : (gXiU : Matrix (Fin 24) (Fin 24) ℚ) = gXi := rfl

theorem gXiU_mem_latticeO : gXiU ∈ latticeO :=
  ⟨(mem_orthogonalGroup_iff _ _).2 gXi_mul_transpose_self, Xi.image_latticeQ⟩

@[expose] def xiO : latticeO := ⟨gXiU, gXiU_mem_latticeO⟩

theorem mat_xiO : mat xiO = gXi := rfl

theorem isDyadicSpinNormalizer_XiU : IsDyadicSpinNormalizer XiU :=
  ⟨(mem_orthogonalGroup_iff _ _).2 Ximat_mul_transpose_self, Ximat_mem_dyadic,
    (image_conj_eq_Q_iff XiU).2 (Subgroup.mem_normalizer_iff''.1 XiU_mem_normalizer)⟩

theorem conj_qmatR_Ximat (s : ZMod 2) (μ ν : Fin 6 → ZMod 2) {h : C}
    (hh : (h : Fin 24 → ZMod 2) ∈ H) {η : Cocode} (hη : η ∈ Hstar) :
    Ximat⁻¹ * qmatR ℚ s (greyC μ + h) (gammaD ν + η) * Ximat =
      qmatR ℚ (s + (qG ν + bG μ ν)) (greyC ν + h) (gammaD (μ + ν) + η) := by
  have e : qmatR ℚ s (greyC μ + h) (gammaD ν + η) =
      sgn s • (Tmat (greyC μ) * Tmat h * Dmat (gammaD ν) * Dmat η) := by
    rw [qmatR_eq, ← Tmat_eq, ← Dmat_eq, sgnR_rat, ← Tmat_mul_Tmat, ← Dmat_mul_Dmat,
      ← Matrix.mul_assoc]
  have e' : qmatR ℚ (s + (qG ν + bG μ ν)) (greyC ν + h) (gammaD (μ + ν) + η) =
      sgn (s + (qG ν + bG μ ν)) •
        (Tmat (greyC ν) * Tmat h * Dmat (gammaD (μ + ν)) * Dmat η) := by
    rw [qmatR_eq, ← Tmat_eq, ← Dmat_eq, sgnR_rat, ← Tmat_mul_Tmat, ← Dmat_mul_Dmat,
      ← Matrix.mul_assoc]
  rw [e, e', Matrix.mul_smul, Matrix.smul_mul, conj_Ximat μ ν hh hη, smul_smul, ← sgn_add]

theorem coe_coe_eq_qmatR (r : Q) :
    ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      qmatR ℚ (spinEquiv.symm r).s (spinEquiv.symm r).a (spinEquiv.symm r).δ :=
  calc ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)
      = ((spinEquiv (spinEquiv.symm r) : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) :=
        congrArg (fun q : Q => ((q : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ))
          (spinEquiv.apply_symm_apply r).symm
    _ = ((toGL (spinEquiv.symm r) : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) :=
        congrArg Units.val (coe_spinEquiv _)
    _ = qmatR ℚ (spinEquiv.symm r).s (spinEquiv.symm r).a (spinEquiv.symm r).δ := coe_toGL _

theorem coe_coe_conj_XiU {r r' : Q} (hr' : (r' : GL SpinIdx ℚ) = XiU⁻¹ * r * XiU) :
    ((r' : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      Ximat⁻¹ * ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) * Ximat :=
  (congrArg Units.val hr').trans ((Units.val_mul _ _).trans (congrArg (· * Ximat)
    ((Units.val_mul _ _).trans
      (congrArg (· * ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) coe_XiU_inv))))

theorem modTwoEnd_xiO_cls_of {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C)
    (hv : v ∈ codeLattice C) (h : Xi.toQ u ᵥ* gXi = Xi.toQ v) :
    modTwoEnd xiO (cls u hu) = cls v hv :=
  (modTwoEnd_mk xiO ⟨u, hu⟩).trans (congrArg Submodule.Quotient.mk (Subtype.ext
    (ratVec_injective ((latVec_spec xiO hu).2.trans h))))

private theorem cls_neg' {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hnu : -u ∈ codeLattice C) :
    cls (-u) hnu = cls u hu := by
  have h : cls (-u) hnu = -cls u hu :=
    Submodule.Quotient.mk_neg _ (x := (⟨u, hu⟩ : codeLatticeSubgroup allOnes_mem_C))
  rw [h, ZModModule.neg_eq_self]

private theorem cls_sub' {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C)
    (huv : u - v ∈ codeLattice C) : cls (u - v) huv = cls u hu + cls v hv := by
  have h : cls (u - v) huv = cls u hu - cls v hv :=
    Submodule.Quotient.mk_sub _ (x := (⟨u, hu⟩ : codeLatticeSubgroup allOnes_mem_C))
      (y := ⟨v, hv⟩)
  rw [h, ZModModule.sub_eq_add]

private theorem toQ_zsmul (c : ℤ) (u : Fin 24 → ℤ) : Xi.toQ (c • u) = (c : ℚ) • Xi.toQ u := by
  funext i
  simp [Xi.toQ]

private theorem four_smul_mem {x : Fin 24 → ℤ} (hx : (∑ i, x i) % 2 = 0) :
    (4 : ℤ) • x ∈ codeLattice C := by
  refine ⟨0, .inl rfl, 0, C.zero_mem, fun i => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, bitLift, ZMod.val_zero, Nat.cast_zero,
      mul_zero, add_zero]
    exact Int.modEq_zero_iff_dvd.2 (Dvd.intro _ rfl)
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_zero]
    unfold Int.ModEq
    omega

@[expose] def lamTL : C →ₗ[ZMod 2] L2 := AddMonoidHom.toZModLinearMap 2 lamTHom

theorem lamTL_apply (a : C) : lamTL a = lamT a := rfl

private theorem greyVec_single : ∀ j : Fin 6, greyVec (Pi.single j 1) = 0 := by decide

theorem thetaD_greyC_single (j : Fin 6) : thetaD (greyC (Pi.single j 1)) = 0 :=
  (thetaD_unique fun u => by
    rw [pair_zero_right, θ_grey (Pi.single j 1) _ u (coe_greyC _), greyVec_single,
      dotProduct_zero]).symm

private theorem P_g (j : Fin 6) : P (g j) = 0 := by
  have h := wt_B (ι6 j)
  rw [B_ι6] at h
  rw [P, h]
  rfl

theorem two_g_mem (j : Fin 6) : (2 : ℤ) • liftℤ (g j) ∈ codeLattice C := by
  have h := two_bitLift_mem weight_mod_four' (g_mem_C j)
  have e : (2 : ℤ) • liftℤ (g j) = fun i => 2 * bitLift (g j i) := by
    funext i
    rfl
  rw [e]
  exact h

theorem lamT_greyC_single (j : Fin 6) :
    lamT (greyC (Pi.single j 1)) = cls ((2 : ℤ) • liftℤ (g j)) (two_g_mem j) := by
  rw [lamT, thetaD_greyC_single, map_zero, add_zero, greyC_single, lamX, lamCodeCls]
  refine (cls_congr _ (lamCode_of_P_zero (P_g j))).trans ?_
  exact cls_congr _ (funext fun i => rfl)

theorem lamGamma_mem (j : Fin 6) : lamGamma j ∈ codeLattice C := by
  have h := lamSum_mem (Pi.single (coord 0 j) 1)
  rw [lamSum_single] at h
  exact h

theorem lamCocode_gammaD_single (j : Fin 6) :
    lamCocode (gammaD (Pi.single j 1)) = cls (lamGamma j) (lamGamma_mem j) := by
  rw [gammaD_single, lamCocode_mk, lamVec]
  exact cls_congr _ (lamSum_single (coord 0 j))

theorem xi_lamT_g (j : Fin 6) :
    modTwoEnd xiO (lamT (greyC (Pi.single j 1))) = lamCocode (gammaD (Pi.single j 1)) := by
  have hn : -lamGamma j ∈ codeLattice C := neg_mem_codeLattice allOnes_mem_C (lamGamma_mem j)
  rw [lamT_greyC_single, lamCocode_gammaD_single,
    modTwoEnd_xiO_cls_of _ hn ((two_g_vecMul_gXi j).trans (toQ_neg _).symm)]
  exact cls_neg' _ _

theorem xi_lamCocode_g (j : Fin 6) :
    modTwoEnd xiO (lamCocode (gammaD (Pi.single j 1))) =
      lamT (greyC (Pi.single j 1)) + lamCocode (gammaD (Pi.single j 1)) := by
  have h2 := two_g_mem j
  have hs : (2 : ℤ) • liftℤ (g j) - lamGamma j ∈ codeLattice C :=
    (codeLatticeSubgroup allOnes_mem_C).sub_mem h2 (lamGamma_mem j)
  rw [lamT_greyC_single, lamCocode_gammaD_single,
    modTwoEnd_xiO_cls_of _ hs ((lamGamma_vecMul_gXi j).trans (toQ_sub _ _).symm)]
  exact cls_sub' h2 _ _

theorem xi_lamT_greyC (μ : Fin 6 → ZMod 2) :
    modTwoEnd xiO (lamT (greyC μ)) = lamCocode (gammaD μ) := by
  have h : modTwoEnd xiO ∘ₗ lamTL ∘ₗ greyC = lamCocode ∘ₗ gammaD :=
    (Pi.basisFun (ZMod 2) (Fin 6)).ext fun j => by
      rw [Pi.basisFun_apply]
      exact xi_lamT_g j
  exact LinearMap.congr_fun h μ

theorem xi_lamCocode_gammaD (ν : Fin 6 → ZMod 2) :
    modTwoEnd xiO (lamCocode (gammaD ν)) = lamT (greyC ν) + lamCocode (gammaD ν) := by
  have h : modTwoEnd xiO ∘ₗ lamCocode ∘ₗ gammaD = lamTL ∘ₗ greyC + lamCocode ∘ₗ gammaD :=
    (Pi.basisFun (ZMod 2) (Fin 6)).ext fun j => by
      rw [Pi.basisFun_apply]
      exact xi_lamCocode_g j
  exact LinearMap.congr_fun h ν

theorem xi_lamCocode_lowerPair (j : Fin 6) {r s : Fin 4} (hr : r ≠ 0) (hs : s ≠ 0)
    (hrs : r ≠ s) :
    modTwoEnd xiO (lamCocode (Submodule.Quotient.mk
      (Pi.single (coord r j) 1 + Pi.single (coord s j) 1))) =
      lamCocode (Submodule.Quotient.mk (Pi.single (coord r j) 1 + Pi.single (coord s j) 1)) := by
  set a := coord r j
  set b := coord s j
  have hsum : (∑ i, (eℤ a - eℤ b) i) % 2 = 0 := by
    simp [eℤ, Finset.sum_sub_distrib]
  have h4 : (4 : ℤ) • (eℤ a - eℤ b) ∈ codeLattice C := four_smul_mem hsum
  have hla := lamSum_mem (Pi.single a 1)
  have h2a : (2 : ℤ) • lamSum (Pi.single a 1) ∈ codeLattice C :=
    (codeLatticeSubgroup allOnes_mem_C).zsmul_mem hla 2
  have key : lamCocode (Submodule.Quotient.mk (Pi.single a 1 + Pi.single b 1)) =
      cls ((4 : ℤ) • (eℤ a - eℤ b)) h4 := by
    have e : lamSum (Pi.single a 1) + lamSum (Pi.single b 1) =
        (4 : ℤ) • (eℤ a - eℤ b) + (2 : ℤ) • lamSum (Pi.single a 1) := by
      rw [lamSum_single, lamSum_single]
      funext k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eℤ]
      ring
    rw [lamCocode_mk, lamVec_add, lamVec, lamVec, cls_add, cls_congr _ e, ← cls_add h4 h2a,
      cls_two_smul hla h2a, add_zero]
  rw [key]
  refine modTwoEnd_xiO_cls_of h4 h4 ?_
  rw [toQ_zsmul, smul_vecMul, lowerDiff_vecMul_gXi j hr hs hrs]

theorem xi_lamCocode_Hstar {η : Cocode} (hη : η ∈ Hstar) :
    modTwoEnd xiO (lamCocode η) = lamCocode η := by
  have hle : Hstar ≤ LinearMap.eqLocus (modTwoEnd xiO ∘ₗ lamCocode) lamCocode := by
    rw [Hstar_eq_span, Submodule.span_le]
    rintro _ ⟨j, r, s, hr, hs, hrs, rfl⟩
    exact LinearMap.mem_eqLocus.2 (xi_lamCocode_lowerPair j hr hs hrs)
  exact LinearMap.mem_eqLocus.1 (hle hη)

@[expose] def lamHat (h : Fin 24 → ZMod 2) : Fin 24 → ℤ :=
  fun i => 2 * bitLift (h i) - 4 * bitLift (colourGamma h i)

private theorem coloured_facts : ∀ k : Fin 6,
    P (B (Fin.natAdd 6 k)) = 0 ∧ hammingNorm (colourGamma (B (Fin.natAdd 6 k))) = 4 ∧
      xiInt (lamHat (B (Fin.natAdd 6 k))) = fun i =>
        lamHat (B (Fin.natAdd 6 k)) i + 8 * bitLift (colourGamma (B (Fin.natAdd 6 k)) i) := by
  decide +kernel

private theorem B_natAdd_mem_H (k : Fin 6) : B (Fin.natAdd 6 k) ∈ H := by
  fin_cases k
  · exact ⟨v₁, v₁_mem, rfl⟩
  · exact ⟨F4.α • v₁, H₆.smul_mem F4.α v₁_mem, rfl⟩
  · exact ⟨v₂, v₂_mem, rfl⟩
  · exact ⟨F4.α • v₂, H₆.smul_mem F4.α v₂_mem, rfl⟩
  · exact ⟨v₃, v₃_mem, rfl⟩
  · exact ⟨F4.α • v₃, H₆.smul_mem F4.α v₃_mem, rfl⟩

theorem thetaD_sub_colourGamma_mem_Hstar {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) :
    thetaD h - Submodule.Quotient.mk (colourGamma h) ∈ Hstar :=
  mem_Hstar_iff.2 fun μ => by
    rw [map_sub, pair_thetaD, pair_mk, θ_colour_grey (greyC_mem_G μ) hh, sub_self]

theorem xi_lamT_coloured {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H)
    (hP : P (h : Fin 24 → ZMod 2) = 0) (hw : hammingNorm (colourGamma h) = 4)
    (hx : xiInt (lamHat h) = fun i => lamHat h i + 8 * bitLift (colourGamma h i)) :
    modTwoEnd xiO (lamT h) = lamT h := by
  obtain ⟨η, hη, hθ⟩ : ∃ η ∈ Hstar, thetaD h = Submodule.Quotient.mk (colourGamma h) + η :=
    ⟨_, thetaD_sub_colourGamma_mem_Hstar hh, by abel⟩
  have h2two : (2 : ℤ) • Visible.twoΩ ∈ codeLattice C :=
    (codeLatticeSubgroup allOnes_mem_C).zsmul_mem Visible.twoΩ_mem 2
  have hu : lamCode h + lamSum (colourGamma h) ∈ codeLattice C :=
    add_mem_codeLattice allOnes_mem_C (lamCode_mem h.2) (lamSum_mem _)
  have he : lamCode h + lamSum (colourGamma h) = lamHat h + (2 : ℤ) • Visible.twoΩ := by
    funext k
    rw [lamCode_of_P_zero hP]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lamSum, hw, lamHat, Visible.twoΩ_apply]
    push_cast
    ring
  have hL : lamHat h ∈ codeLattice C := by
    have e : lamHat h = lamCode h + lamSum (colourGamma h) - (2 : ℤ) • Visible.twoΩ := by
      rw [he, add_sub_cancel_right]
    rw [e]
    exact (codeLatticeSubgroup allOnes_mem_C).sub_mem hu h2two
  have hcls : lamX h + lamCocode (Submodule.Quotient.mk (colourGamma h)) = cls (lamHat h) hL := by
    rw [lamX, lamCodeCls, lamCocode_mk, lamVec, cls_add, cls_congr _ he, ← cls_add hL h2two,
      cls_two_smul Visible.twoΩ_mem h2two, add_zero]
  have h4 : (4 : ℤ) • liftℤ (colourGamma h) ∈ codeLattice C := four_smul_mem (by
    rw [sum_liftℤ, hw]
    rfl)
  have h8 : (2 : ℤ) • ((4 : ℤ) • liftℤ (colourGamma h)) ∈ codeLattice C :=
    (codeLatticeSubgroup allOnes_mem_C).zsmul_mem h4 2
  have hx' : xiInt (lamHat h) = lamHat h + (2 : ℤ) • ((4 : ℤ) • liftℤ (colourGamma h)) := by
    rw [hx]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, liftℤ]
    ring
  have hfix : modTwoEnd xiO (cls (lamHat h) hL) = cls (lamHat h) hL := by
    rw [modTwoEnd_xiO_cls_of hL (xiInt_mem hL) (toQ_mem_latticeQ_vecMul hL), cls_congr _ hx',
      ← cls_add hL h8, cls_two_smul h4 h8, add_zero]
  have e : lamT h = cls (lamHat h) hL + lamCocode η := by
    rw [← hcls, lamT, hθ, map_add lamCocode, add_assoc]
  rw [e, map_add, hfix, xi_lamCocode_Hstar hη]

theorem xi_lamT_H {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) :
    modTwoEnd xiO (lamT h) = lamT h := by
  set E := LinearMap.eqLocus (modTwoEnd xiO ∘ₗ lamTL) lamTL
  have hbasis : ∀ k : Fin 6, basisC (Fin.natAdd 6 k) ∈ E := fun k => by
    have hk := coloured_facts k
    have hB : (basisC (Fin.natAdd 6 k) : Fin 24 → ZMod 2) = B (Fin.natAdd 6 k) := basisC_apply _
    refine LinearMap.mem_eqLocus.2 (xi_lamT_coloured (hB ▸ B_natAdd_mem_H k) ?_ ?_ ?_)
    · rw [hB]
      exact hk.1
    · rw [hB]
      exact hk.2.1
    · rw [hB]
      exact hk.2.2
  have hzero : ∀ j : Fin 6, basisC.repr h (Fin.castAdd 6 j) = 0 := fun j => by
    obtain ⟨y, -, hy⟩ := hh
    rw [repr_apply, ← hy, ψ_l_grey]
  have hmem : h ∈ E := by
    rw [← basisC.sum_repr h]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine Fin.addCases (m := 6) (n := 6)
      (motive := fun i => basisC.repr h i • basisC i ∈ E) (fun j => ?_) (fun k => ?_) i
    · rw [hzero, zero_smul]
      exact E.zero_mem
    · exact E.smul_mem _ (hbasis k)
  exact LinearMap.mem_eqLocus.1 hmem

theorem xi_phi0 (μ ν : Fin 6 → ZMod 2) {h : C} (hh : (h : Fin 24 → ZMod 2) ∈ H) {η : Cocode}
    (hη : η ∈ Hstar) :
    modTwoEnd xiO (phi0 (greyC μ + h, gammaD ν + η)) =
      phi0 (greyC ν + h, gammaD (μ + ν) + η) := by
  rw [phi0_apply, phi0_apply, lamT_add, lamT_add]
  simp only [map_add]
  rw [xi_lamT_greyC, xi_lamT_H hh, xi_lamCocode_gammaD, xi_lamCocode_Hstar hη]
  abel

theorem xi_phi0_coords {x x' : SpinCoord}
    (hx : qmatR ℚ x'.s x'.a x'.δ = Ximat⁻¹ * qmatR ℚ x.s x.a x.δ * Ximat) :
    phi0 (x'.a, x'.δ) = modTwoEnd xiO (phi0 (x.a, x.δ)) := by
  obtain ⟨μ, h, hh, ha⟩ := exists_greyC_add x.a
  obtain ⟨ν, hν⟩ := exists_gammaD_add_mem_Hstar x.δ
  obtain ⟨η, hη, hδ⟩ : ∃ η ∈ Hstar, x.δ = gammaD ν + η := ⟨_, hν, (add_sub_cancel _ _).symm⟩
  have hm := hx.trans ((congrArg (fun M => Ximat⁻¹ * M * Ximat)
    (congrArg₂ (qmatR ℚ x.s) ha hδ)).trans (conj_qmatR_Ximat x.s μ ν hh hη))
  have hc := qmatR_injective two_ne_zero hm
  exact (congrArg phi0 (congrArg₂ Prod.mk hc.2.1 hc.2.2)).trans ((xi_phi0 μ ν hh hη).symm.trans
    (congrArg (fun p => modTwoEnd xiO (phi0 p)) (congrArg₂ Prod.mk ha hδ).symm))

theorem isCompatible_XiU : IsCompatible XiU xiO := fun r r' hr' =>
  (toAdd_phi_mk r').trans ((xi_phi0_coords (x := spinEquiv.symm r) (x' := spinEquiv.symm r')
    ((coe_coe_eq_qmatR r').symm.trans ((coe_coe_conj_XiU hr').trans
      (congrArg (fun M => Ximat⁻¹ * M * Ximat) (coe_coe_eq_qmatR r))))).trans
    (congrArg (modTwoEnd xiO) (toAdd_phi_mk r).symm))

@[expose] def xiPair : Pvis := ⟨(XiU, xiO), isDyadicSpinNormalizer_XiU, isCompatible_XiU⟩

theorem coe_xiPair :
    (xiPair : GL SpinIdx ℚ × latticeO) = (XiU, ⟨gXiU, gXiU_mem_latticeO⟩) := rfl

theorem XiU_pow_three : XiU ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, coe_XiU, Ximat_pow_three, Units.val_one])

theorem xiO_pow_three : xiO ^ 3 = 1 :=
  mat_injective (by
    show (((xiO ^ 3 : latticeO) : GL (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ) = mat 1
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, mat_one]
    exact gXi_pow_three)

theorem xiPair_pow_three : xiPair ^ 3 = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact Prod.ext XiU_pow_three xiO_pow_three)

theorem thetaEquiv_pow (p : Pvis) (n : ℕ) : thetaEquiv (p ^ n) = thetaEquiv p ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, thetaEquiv_one]
  | succ n ih => rw [pow_succ, thetaEquiv_mul, ih, pow_succ']

theorem thetaEquiv_xiPair_ne_one : thetaEquiv xiPair ≠ 1 := by
  intro h1
  have hA : vecMulVec (Pi.single 0 1 : Fin 24 → ℚ) (Pi.single 0 1) ∈ symMat := by
    rw [mem_symMat, transpose_vecMulVec]
  have h2 : theta xiPair (⟨_, hA⟩, 0, 0) = (⟨_, hA⟩, 0, 0) := by
    rw [← thetaEquiv_apply, h1]
    rfl
  rw [theta_symMat] at h2
  have h3 := congrArg (fun x : SpaceB => ((x.1 : symMat) : Matrix (Fin 24) (Fin 24) ℚ) 0 0) h2
  simp only [coe_thetaA] at h3
  rw [Matrix.mul_assoc, vecMulVec_mul, mul_vecMulVec, vecMulVec_apply, vecMulVec_apply,
    mulVec_transpose, single_one_vecMul, row_apply, Pi.single_eq_same] at h3
  change gXi 0 0 * gXi 0 0 = 1 * 1 at h3
  have hg : gXi 0 0 = -1 / 2 := by
    change gXi (coord 0 0) (coord 0 0) = -1 / 2
    rw [gXi_coord, C4_eq]
    simp
  rw [hg] at h3
  norm_num at h3

theorem orderOf_thetaEquiv_xiPair : orderOf (thetaEquiv xiPair) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ thetaEquiv_xiPair_ne_one
  rw [← thetaEquiv_pow, xiPair_pow_three, thetaEquiv_one]

theorem xi_spin_lattice_compatibility :
    ((XiU : Matrix SpinIdx SpinIdx ℚ) = Ximat ∧
      ((XiU⁻¹ : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = Ximatᵀ) ∧
    ((gXiU : Matrix (Fin 24) (Fin 24) ℚ) = gXi ∧
      ((gXiU⁻¹ : GL (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ) = gXiᵀ) ∧
    gXiU ∈ latticeO ∧
    IsDyadicSpinNormalizer XiU ∧
    IsCompatible XiU ⟨gXiU, gXiU_mem_latticeO⟩ ∧
    (∀ r r' : Q, (r' : GL SpinIdx ℚ) = XiU⁻¹ * r * XiU →
      Multiplicative.toAdd (phi (QuotientGroup.mk r')) =
        modTwoEnd ⟨gXiU, gXiU_mem_latticeO⟩ (Multiplicative.toAdd (phi (QuotientGroup.mk r)))) ∧
    ((XiU, ⟨gXiU, gXiU_mem_latticeO⟩) : GL SpinIdx ℚ × latticeO) ∈ Pvis ∧
    (xiPair : GL SpinIdx ℚ × latticeO) = (XiU, ⟨gXiU, gXiU_mem_latticeO⟩) ∧
    thetaEquiv xiPair ∈ Gvis ∧ orderOf (thetaEquiv xiPair) = 3 :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, gXiU_mem_latticeO, isDyadicSpinNormalizer_XiU, isCompatible_XiU,
    isCompatible_XiU, xiPair.2, rfl, ⟨xiPair, rfl⟩, orderOf_thetaEquiv_xiPair⟩

end CFSG.Monster.Visible
