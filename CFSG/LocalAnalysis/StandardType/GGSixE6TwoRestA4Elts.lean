module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParF2

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

private theorem e6ae_xr_mul_self
    (β : Fin Tag.E6.rank → ℤ) : xr β * xr β = 1 := by
  apply Subtype.ext
  show pinnedX .E6 F2 β 1 * pinnedX .E6 F2 β 1 = (1 : ModGL .E6 F2)
  rw [← pinnedX_add]
  rw [show (1 : F2) + 1 = 0 by rw [one_add_one_eq_two, gf2_two], pinnedX_zero]

private theorem e6ae_xr_inv
    (β : Fin Tag.E6.rank → ℤ) : (xr β)⁻¹ = xr β := by
  rw [inv_eq_iff_mul_eq_one]
  exact e6ae_xr_mul_self β

private noncomputable def e6ae_b : Module.Basis (Fin e6Data.d) (ZMod 2) (Fin e6Data.d →₀ ZMod 2) :=
  Finsupp.basisSingleOne

private theorem e6ae_digVec_apply (c : ℕ) (i : Fin e6Data.d) :
    digVec (ZMod 2) e6Data.d c i =
      if h : 2 ≤ c ∧ c / 2 - 1 < e6Data.d then
        (if i.val = c / 2 - 1 then 1 else 0) else 0 := by
  unfold digVec
  by_cases h : 2 ≤ c ∧ c / 2 - 1 < e6Data.d
  · rw [dif_pos h, dif_pos h]
    rw [CharTwo.neg_eq, one_pow, one_smul, Finsupp.single_apply]
    by_cases hi : (⟨c / 2 - 1, h.2⟩ : Fin e6Data.d) = i
    · rw [if_pos hi, if_pos (congrArg Fin.val hi).symm]
    · rw [if_neg hi, if_neg (fun hv => hi (Fin.ext hv).symm)]
  · rw [dif_neg h, dif_neg h, Finsupp.zero_apply]

private noncomputable def e6ae_matE (k : ℕ) : Matrix (Fin e6Data.d) (Fin e6Data.d) (ZMod 2) :=
  fun i j =>
    if h : 2 ≤ dig (e6Data.op k) j.val ∧ dig (e6Data.op k) j.val / 2 - 1 < e6Data.d then
      (if i.val = dig (e6Data.op k) j.val / 2 - 1 then 1 else 0)
    else 0

private theorem e6ae_toMatrix_toEnd
    (k : ℕ) :
    LinearMap.toMatrixAlgEquiv e6ae_b (toEnd (ZMod 2) e6Data.d (e6Data.op k)) = e6ae_matE k := by
  ext i j
  rw [LinearMap.toMatrixAlgEquiv_apply]
  simp only [e6ae_b, Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr,
    LinearEquiv.refl_apply, toEnd_single]
  rw [e6ae_digVec_apply]
  rfl

private noncomputable def e6ae_pOne : Array ℕ :=
  matBits e6Data.d e6Data.d (1 : Matrix (Fin e6Data.d) (Fin e6Data.d) (ZMod 2))

private noncomputable def e6ae_pE (k : ℕ) : Array ℕ := matBits e6Data.d e6Data.d (e6ae_matE k)

private noncomputable def e6ae_pW : List ℕ → Array ℕ
  | [] => e6ae_pOne
  | k :: t => bmul e6Data.d e6Data.d (bxor e6Data.d e6ae_pOne (e6ae_pE k)) (e6ae_pW t)

private noncomputable def e6ae_wM : List ℕ → Matrix (Fin e6Data.d) (Fin e6Data.d) (ZMod 2)
  | [] => 1
  | k :: t => (1 + e6ae_matE k) * e6ae_wM t

private theorem e6ae_toMat_pW (l : List ℕ) :
    toMat e6Data.d e6Data.d (e6ae_pW l) = e6ae_wM l := by
  induction l with
  | nil => simp [e6ae_pW, e6ae_wM, e6ae_pOne, toMat_matBits]
  | cons k t ih =>
    simp only [e6ae_pW, e6ae_wM, e6ae_pOne, e6ae_pE]
    rw [toMat_bmul, toMat_bxor, toMat_matBits, toMat_matBits, ih]

private def e6ae_root (k : ℕ) : Fin Tag.E6.rank → ℤ := Tag.E6.rootCertificate.root k

private noncomputable def e6ae_wGroup :
    List ℕ → e6Data_valid.minGroup (ZMod 2)
  | [] => 1
  | k :: t => e6Data_valid.xm (ZMod 2) (e6ae_root k) 1 * e6ae_wGroup t

private theorem e6ae_rootOp_root
    (k : ℕ) (hk : k < 72) :
    e6Data.rootOp (ZMod 2) (e6ae_root k) = toEnd (ZMod 2) e6Data.d (e6Data.op k) := by
  rw [show e6ae_root k = Tag.E6.rootCertificate.root k from rfl]
  exact MinData.rootOp_root (τ := .E6) (D := e6Data) (R := ZMod 2) (by
    rw [Tag.rootCertificate_length]; exact hk)

private theorem e6ae_toMatrixAlgEquiv_wGroup
    (l : List ℕ) (hl : ∀ k ∈ l, k < 72) :
    LinearMap.toMatrixAlgEquiv e6ae_b
        (e6Data_valid.endo (ZMod 2) (e6ae_wGroup l)) = e6ae_wM l := by
  induction l with
  | nil =>
    simp only [e6ae_wGroup, e6ae_wM, e6Data_valid.endo_one]
    exact map_one _
  | cons k t ih =>
    have hk : k < 72 := hl k (by simp)
    have ht : ∀ k' ∈ t, k' < 72 := fun k' hk' => hl k' (by simp [hk'])
    simp only [e6ae_wGroup, e6ae_wM]
    rw [e6Data_valid.endo_mul]
    rw [map_mul, ih ht]
    congr 1
    rw [e6Data_valid.endo_xm, one_smul, e6ae_rootOp_root k hk]
    rw [map_add, map_one, e6ae_toMatrix_toEnd]

private theorem e6ae_wGroup_eq_of_packed
    (l₁ l₂ : List ℕ)
    (hl₁ : ∀ k ∈ l₁, k < 72) (hl₂ : ∀ k ∈ l₂, k < 72)
    (h : e6ae_pW l₁ = e6ae_pW l₂) : e6ae_wGroup l₁ = e6ae_wGroup l₂ := by
  apply e6Data_valid.endo_injective (ZMod 2)
  apply (LinearMap.toMatrixAlgEquiv e6ae_b).injective
  rw [e6ae_toMatrixAlgEquiv_wGroup l₁ hl₁, e6ae_toMatrixAlgEquiv_wGroup l₂ hl₂]
  have h' := congrArg (toMat e6Data.d e6Data.d) h
  rwa [e6ae_toMat_pW l₁, e6ae_toMat_pW l₂] at h'

private noncomputable def e6ae_Xm
    (k : ℕ) : ModGL .E6 F2 := (xr (e6ae_root k) : ModGL .E6 F2)

private noncomputable def e6ae_wECm :
    List ℕ → ModGL .E6 F2
  | [] => 1
  | k :: t => e6ae_Xm k * e6ae_wECm t

private theorem e6ae_wECm_append
    (l₁ l₂ : List ℕ) : e6ae_wECm (l₁ ++ l₂) = e6ae_wECm l₁ * e6ae_wECm l₂ := by
  induction l₁ with
  | nil => simp [e6ae_wECm]
  | cons k t ih => simp only [List.cons_append, e6ae_wECm, ih, mul_assoc]

private theorem e6ae_Xm_inv (k : ℕ) :
    (e6ae_Xm k)⁻¹ = e6ae_Xm k := by
  change (((xr (e6ae_root k))⁻¹ : EC) : ModGL .E6 F2) =
    ((xr (e6ae_root k) : EC) : ModGL .E6 F2)
  rw [e6ae_xr_inv]

private theorem e6ae_wECm_singleton
    (k : ℕ) : e6ae_wECm [k] = e6ae_Xm k := by
  simp [e6ae_wECm]

private theorem e6ae_wECm_inv
    (l : List ℕ) : (e6ae_wECm l)⁻¹ = e6ae_wECm l.reverse := by
  induction l with
  | nil => simp [e6ae_wECm]
  | cons k t ih =>
    simp only [e6ae_wECm, List.reverse_cons]
    rw [mul_inv_rev, ih, e6ae_Xm_inv, ← e6ae_wECm_singleton k, ← e6ae_wECm_append]

private noncomputable def e6ae_g : F2 →+* ZMod 2 :=
  (GaloisField.equivZmodP (p := 2) : F2 →+* ZMod 2)

private noncomputable def e6ae_wP :
    List ℕ → ModGL .E6 (ZMod 2)
  | [] => 1
  | k :: t => pinnedX .E6 (ZMod 2) (e6ae_root k) 1 * e6ae_wP t

private theorem e6ae_bc_wEC
    (l : List ℕ) :
    baseChangeGL (τ := .E6) e6ae_g (e6ae_wECm l) = e6ae_wP l := by
  induction l with
  | nil => simp [e6ae_wECm, e6ae_wP, map_one]
  | cons k t ih =>
    simp only [e6ae_wECm, e6ae_wP]
    rw [map_mul (baseChangeGL (τ := .E6) e6ae_g)]
    rw [ih]
    have hX : baseChangeGL (τ := .E6) e6ae_g (e6ae_Xm k) =
        pinnedX .E6 (ZMod 2) (e6ae_root k) 1 := by
      rw [show e6ae_Xm k = pinnedX .E6 F2 (e6ae_root k) 1 from rfl]
      rw [baseChangeGL_pinnedX, map_one]
    rw [hX]

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

private theorem e6ae_wP_eq_wI
    (l : List ℕ) (hl : ∀ k ∈ l, k < 72) :
    e6ae_wP l = ((e6Isogeny (ZMod 2) (e6ae_wGroup l) : adjointGroup .E6 (ZMod 2)) :
      ModGL .E6 (ZMod 2)) := by
  induction l with
  | nil =>
    simp [e6ae_wP, e6ae_wGroup]
  | cons k t ih =>
    have hk : k < 72 := hl k (by simp)
    have ht : ∀ k' ∈ t, k' < 72 := fun k' hk' => hl k' (by simp [hk'])
    have hroot : IsRoot .E6 (e6ae_root k) := by
      rw [show e6ae_root k = Tag.E6.rootCertificate.root k from rfl]
      exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E6) k (by
        rw [Tag.rootCertificate_length]; exact hk)
    simp only [e6ae_wP, e6ae_wGroup]
    rw [map_mul, Subgroup.coe_mul, ih ht]
    have hX : pinnedX .E6 (ZMod 2) (e6ae_root k) 1 =
        ((e6Isogeny (ZMod 2) (e6Data_valid.xm (ZMod 2) (e6ae_root k) 1) :
          adjointGroup .E6 (ZMod 2)) : ModGL .E6 (ZMod 2)) :=
      (E6Pilot.coe_e6Isogeny_xm (K := ZMod 2) hroot 1).symm
    rw [hX]

private theorem e6ae_wECm_eq_of_wGroup
    (l₁ l₂ : List ℕ)
    (hl₁ : ∀ k ∈ l₁, k < 72) (hl₂ : ∀ k ∈ l₂, k < 72)
    (h : e6ae_wGroup l₁ = e6ae_wGroup l₂) : e6ae_wECm l₁ = e6ae_wECm l₂ := by
  apply baseChangeGL_injective (f := e6ae_g)
  rw [e6ae_bc_wEC l₁, e6ae_bc_wEC l₂, e6ae_wP_eq_wI l₁ hl₁, e6ae_wP_eq_wI l₂ hl₂, h]

private theorem e6ae_wECm_eq_of_packed
    (l₁ l₂ : List ℕ)
    (hl₁ : ∀ k ∈ l₁, k < 72) (hl₂ : ∀ k ∈ l₂, k < 72)
    (h : e6ae_pW l₁ = e6ae_pW l₂) : e6ae_wECm l₁ = e6ae_wECm l₂ :=
  e6ae_wECm_eq_of_wGroup l₁ l₂ hl₁ hl₂ (e6ae_wGroup_eq_of_packed l₁ l₂ hl₁ hl₂ h)

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

private theorem e6ae_root_0 : e6ae_root 0 = ![1, 0, 0, 0, 0, 0] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_3 : e6ae_root 3 = ![0, 0, 0, 1, 0, 0] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_5 : e6ae_root 5 = ![0, 0, 0, 0, 0, 1] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_6 : e6ae_root 6 = ![-1, 0, 0, 0, 0, 0] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_12 : e6ae_root 12 = ![0, 0, 0, -1, 0, 0] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_16 : e6ae_root 16 = ![0, 0, 0, 0, 0, -1] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_41 : e6ae_root 41 = ![0, -1, -1, -1, -1, 0] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_53 : e6ae_root 53 = ![-1, -1, -1, -2, -1, 0] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_54 : e6ae_root 54 = ![-1, -1, -1, -1, -1, -1] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_57 : e6ae_root 57 = ![0, -1, -1, -2, -1, -1] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_60 : e6ae_root 60 = ![-1, -1, -1, -2, -1, -1] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_70 : e6ae_root 70 = ![1, 2, 2, 3, 2, 1] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_root_71 : e6ae_root 71 = ![-1, -2, -2, -3, -2, -1] := by
  funext i; fin_cases i <;> rfl

@[expose] noncomputable def yE : EC :=
  xr ![0, -1, -1, -1, -1, 0] * xr ![0, -1, -1, -2, -1, -1] * xr ![-1, -1, -1, -1, -1, -1] *
    xr ![-1, -1, -1, -2, -1, 0] * xr ![-1, -1, -1, -2, -1, -1]

@[expose] noncomputable def cE : EC :=
  yE * zE * yE⁻¹

@[expose] noncomputable def phiE : EC :=
  xr (a5Root 0 1) * xr (a5Root 2 3) * xr (a5Root 4 5)

private theorem e6ae_highRoot_70 : highRoot .E6 = e6ae_root 70 := by
  rw [e6ae_root_70]; funext i; fin_cases i <;> rfl

private theorem e6ae_neg_root_70_71 : -e6ae_root 70 = e6ae_root 71 := by
  rw [e6ae_root_70, e6ae_root_71]; funext i; fin_cases i <;> rfl

private theorem e6ae_a5_blk00_01 : a5Root (blk 0 0) (blk 0 1) = ![1, 0, 0, 0, 0, 0] := by
  funext i; fin_cases i <;> rfl
private theorem e6ae_a5_blk01_00 : a5Root (blk 0 1) (blk 0 0) = ![-1, 0, 0, 0, 0, 0] := by
  funext i; fin_cases i <;> rfl
private theorem e6ae_a5_blk10_11 : a5Root (blk 1 0) (blk 1 1) = ![0, 0, 0, 1, 0, 0] := by
  funext i; fin_cases i <;> rfl
private theorem e6ae_a5_blk11_10 : a5Root (blk 1 1) (blk 1 0) = ![0, 0, 0, -1, 0, 0] := by
  funext i; fin_cases i <;> rfl
private theorem e6ae_a5_blk20_21 : a5Root (blk 2 0) (blk 2 1) = ![0, 0, 0, 0, 0, 1] := by
  funext i; fin_cases i <;> rfl
private theorem e6ae_a5_blk21_20 : a5Root (blk 2 1) (blk 2 0) = ![0, 0, 0, 0, 0, -1] := by
  funext i; fin_cases i <;> rfl

private theorem e6ae_a5_01 : a5Root 0 1 = ![1, 0, 0, 0, 0, 0] := by
  funext i; fin_cases i <;> rfl
private theorem e6ae_a5_23 : a5Root 2 3 = ![0, 0, 0, 1, 0, 0] := by
  funext i; fin_cases i <;> rfl
private theorem e6ae_a5_45 : a5Root 4 5 = ![0, 0, 0, 0, 0, 1] := by
  funext i; fin_cases i <;> rfl
private def e6ae_ly : List ℕ := [41, 57, 54, 53, 60]
private def e6ae_lz : List ℕ := [70, 71]
private def e6ae_lw : List ℕ := [0, 6, 3, 12, 5, 16]
private def e6ae_lphi : List ℕ := [0, 3, 5]
private def e6ae_lc : List ℕ := e6ae_ly ++ e6ae_lz ++ e6ae_ly.reverse
private def e6ae_l1 : List ℕ := e6ae_lc ++ e6ae_lz ++ e6ae_lc.reverse
private def e6ae_l2 : List ℕ := e6ae_lz ++ e6ae_lw

private theorem e6ae_yE_eq :
    (yE : ModGL .E6 F2) = e6ae_wECm e6ae_ly := by
  simp only [e6ae_ly, e6ae_wECm, e6ae_Xm, yE, xr, Subtype.coe_mk, Subgroup.coe_mul, mul_one,
    mul_assoc]
  rw [e6ae_root_41, e6ae_root_57, e6ae_root_54, e6ae_root_53, e6ae_root_60]

private theorem e6ae_zE_eq :
    (zE : ModGL .E6 F2) = e6ae_wECm e6ae_lz := by
  simp only [e6ae_lz, e6ae_wECm, e6ae_Xm, zE, xr, Subtype.coe_mk, Subgroup.coe_mul, mul_one,
    mul_assoc]
  rw [e6ae_highRoot_70, e6ae_neg_root_70_71]

private theorem e6ae_wOmegaE_eq :
    (wOmegaE : ModGL .E6 F2) = e6ae_wECm e6ae_lw := by
  simp only [e6ae_lw, e6ae_wECm, e6ae_Xm, wOmegaE, cOmegaE, xr, Subtype.coe_mk,
    Subgroup.coe_mul, mul_one, mul_assoc]
  rw [e6ae_a5_blk00_01, e6ae_a5_blk01_00, e6ae_a5_blk10_11, e6ae_a5_blk11_10,
    e6ae_a5_blk20_21, e6ae_a5_blk21_20,
    e6ae_root_0, e6ae_root_6, e6ae_root_3, e6ae_root_12, e6ae_root_5, e6ae_root_16]

private theorem e6ae_phiE_eq :
    (phiE : ModGL .E6 F2) = e6ae_wECm e6ae_lphi := by
  simp only [e6ae_lphi, e6ae_wECm, e6ae_Xm, phiE, xr, Subtype.coe_mk, Subgroup.coe_mul,
    mul_one, mul_assoc]
  rw [e6ae_a5_01, e6ae_a5_23, e6ae_a5_45, e6ae_root_0, e6ae_root_3, e6ae_root_5]

private theorem e6ae_cE_eq :
    (cE : ModGL .E6 F2) = e6ae_wECm e6ae_lc := by
  simp only [cE, e6ae_lc, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e6ae_yE_eq, e6ae_zE_eq, e6ae_wECm_inv]
  rw [← e6ae_wECm_append, ← e6ae_wECm_append]

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem cE_conj_zE :
    cE * zE * cE⁻¹ = zE * wOmegaE := by
  have hL : ((cE * zE * cE⁻¹ : EC) : ModGL .E6 F2) = e6ae_wECm e6ae_l1 := by
    rw [show ((cE * zE * cE⁻¹ : EC) : ModGL .E6 F2) =
      (cE : ModGL .E6 F2) * (zE : ModGL .E6 F2) * (cE : ModGL .E6 F2)⁻¹ from rfl]
    rw [e6ae_cE_eq, e6ae_zE_eq, e6ae_wECm_inv]
    rw [← e6ae_wECm_append, ← e6ae_wECm_append]
    rfl
  have hR : ((zE * wOmegaE : EC) : ModGL .E6 F2) = e6ae_wECm e6ae_l2 := by
    rw [show ((zE * wOmegaE : EC) : ModGL .E6 F2) =
      (zE : ModGL .E6 F2) * (wOmegaE : ModGL .E6 F2) from rfl]
    rw [e6ae_zE_eq, e6ae_wOmegaE_eq]
    rw [← e6ae_wECm_append]
    rfl
  apply Subtype.ext
  rw [hL, hR]
  exact e6ae_wECm_eq_of_packed e6ae_l1 e6ae_l2 (by decide) (by decide) (by decide +kernel)

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[simp] private theorem e6ae_a5ro_0_0_1_0 : a5Root (blk 0 0) (blk 1 0) = e6ae_root 7 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_0_1_1_1 : a5Root (blk 0 1) (blk 1 1) = e6ae_root 11 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_0_0_1_1 : a5Root (blk 0 0) (blk 1 1) = e6ae_root 18 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_0_1_1_0 : a5Root (blk 0 1) (blk 1 0) = e6ae_root 2 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_0_0_2_0 : a5Root (blk 0 0) (blk 2 0) = e6ae_root 29 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_0_1_2_1 : a5Root (blk 0 1) (blk 2 1) = e6ae_root 35 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_0_0_2_1 : a5Root (blk 0 0) (blk 2 1) = e6ae_root 40 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_0_1_2_0 : a5Root (blk 0 1) (blk 2 0) = e6ae_root 23 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_1_0_0_0 : a5Root (blk 1 0) (blk 0 0) = e6ae_root 17 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_1_1_0_1 : a5Root (blk 1 1) (blk 0 1) = e6ae_root 22 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_1_0_0_1 : a5Root (blk 1 0) (blk 0 1) = e6ae_root 10 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_1_1_0_0 : a5Root (blk 1 1) (blk 0 0) = e6ae_root 27 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_1_0_2_0 : a5Root (blk 1 0) (blk 2 0) = e6ae_root 13 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_1_1_2_1 : a5Root (blk 1 1) (blk 2 1) = e6ae_root 15 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_1_0_2_1 : a5Root (blk 1 0) (blk 2 1) = e6ae_root 25 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_1_1_2_0 : a5Root (blk 1 1) (blk 2 0) = e6ae_root 4 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_2_0_0_0 : a5Root (blk 2 0) (blk 0 0) = e6ae_root 38 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_2_1_0_1 : a5Root (blk 2 1) (blk 0 1) = e6ae_root 45 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_2_0_0_1 : a5Root (blk 2 0) (blk 0 1) = e6ae_root 34 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_2_1_0_0 : a5Root (blk 2 1) (blk 0 0) = e6ae_root 47 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_2_0_1_0 : a5Root (blk 2 0) (blk 1 0) = e6ae_root 24 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_2_1_1_1 : a5Root (blk 2 1) (blk 1 1) = e6ae_root 26 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_2_0_1_1 : a5Root (blk 2 0) (blk 1 1) = e6ae_root 14 := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem e6ae_a5ro_2_1_1_0 : a5Root (blk 2 1) (blk 1 0) = e6ae_root 36 := by
  funext i; fin_cases i <;> rfl

private def e6ae_roIdx (k l : Fin 3) : List ℕ :=
  if k = 0 ∧ l = 1 then [7, 11]
  else if k = 0 ∧ l = 2 then [29, 35]
  else if k = 1 ∧ l = 0 then [17, 22]
  else if k = 1 ∧ l = 2 then [13, 15]
  else if k = 2 ∧ l = 0 then [38, 45]
  else if k = 2 ∧ l = 1 then [24, 26]
  else []

private def e6ae_romIdx (k l : Fin 3) : List ℕ :=
  if k = 0 ∧ l = 1 then [18, 2, 11]
  else if k = 0 ∧ l = 2 then [40, 23, 35]
  else if k = 1 ∧ l = 0 then [10, 27, 22]
  else if k = 1 ∧ l = 2 then [25, 4, 15]
  else if k = 2 ∧ l = 0 then [34, 47, 45]
  else if k = 2 ∧ l = 1 then [14, 36, 26]
  else []

private theorem e6ae_rOne_eq
    (k l : Fin 3) (hkl : k ≠ l) :
    rOne k l = e6ae_wECm (e6ae_roIdx k l) := by
  fin_cases k <;> fin_cases l <;>
    simp_all [e6ae_roIdx, rOne, e6ae_wECm, e6ae_Xm, xr, Subtype.coe_mk, Subgroup.coe_mul,
      mul_one, mul_assoc]

private theorem e6ae_rOmega_eq
    (k l : Fin 3) (hkl : k ≠ l) :
    rOmega k l = e6ae_wECm (e6ae_romIdx k l) := by
  fin_cases k <;> fin_cases l <;>
    simp_all [e6ae_romIdx, rOmega, e6ae_wECm, e6ae_Xm, xr, Subtype.coe_mk, Subgroup.coe_mul,
      mul_one, mul_assoc]

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

private theorem e6ae_bound_append {l₁ l₂ : List ℕ}
    (h₁ : ∀ m ∈ l₁, m < 72) (h₂ : ∀ m ∈ l₂, m < 72) : ∀ m ∈ l₁ ++ l₂, m < 72 := by
  intro m hm
  rw [List.mem_append] at hm
  exact hm.elim (h₁ m) (h₂ m)

private theorem e6ae_lc_bound : ∀ m ∈ e6ae_lc, m < 72 := by decide

private theorem e6ae_lw_bound : ∀ m ∈ e6ae_lw, m < 72 := by decide

private theorem e6ae_lphi_bound : ∀ m ∈ e6ae_lphi, m < 72 := by decide

private theorem e6ae_lphi_rev_bound : ∀ m ∈ e6ae_lphi.reverse, m < 72 := by decide

private theorem e6ae_lw_rev_bound : ∀ m ∈ e6ae_lw.reverse, m < 72 := by decide

private theorem e6ae_roIdx_bound :
    ∀ k l : Fin 3, k ≠ l → ∀ m ∈ e6ae_roIdx k l, m < 72 := by decide +kernel

private theorem e6ae_romIdx_bound :
    ∀ k l : Fin 3, k ≠ l → ∀ m ∈ e6ae_romIdx k l, m < 72 := by decide +kernel

private theorem e6ae_comm_packed_ro :
    ∀ k l : Fin 3, k ≠ l →
      e6ae_pW (e6ae_lc ++ e6ae_roIdx k l) = e6ae_pW (e6ae_roIdx k l ++ e6ae_lc) := by
  decide +kernel

private theorem e6ae_comm_packed_rom :
    ∀ k l : Fin 3, k ≠ l →
      e6ae_pW (e6ae_lc ++ e6ae_romIdx k l) = e6ae_pW (e6ae_romIdx k l ++ e6ae_lc) := by
  decide +kernel

private theorem e6ae_comm_rOne
    (k l : Fin 3) (hkl : k ≠ l) :
    cE * rOne k l = rOne k l * cE := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [e6ae_cE_eq, e6ae_rOne_eq k l hkl]
  rw [← e6ae_wECm_append, ← e6ae_wECm_append]
  exact e6ae_wECm_eq_of_packed (e6ae_lc ++ e6ae_roIdx k l) (e6ae_roIdx k l ++ e6ae_lc)
    (e6ae_bound_append e6ae_lc_bound (e6ae_roIdx_bound k l hkl))
    (e6ae_bound_append (e6ae_roIdx_bound k l hkl) e6ae_lc_bound)
    (e6ae_comm_packed_ro k l hkl)

private theorem e6ae_comm_rOmega
    (k l : Fin 3) (hkl : k ≠ l) :
    cE * rOmega k l = rOmega k l * cE := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [e6ae_cE_eq, e6ae_rOmega_eq k l hkl]
  rw [← e6ae_wECm_append, ← e6ae_wECm_append]
  exact e6ae_wECm_eq_of_packed (e6ae_lc ++ e6ae_romIdx k l) (e6ae_romIdx k l ++ e6ae_lc)
    (e6ae_bound_append e6ae_lc_bound (e6ae_romIdx_bound k l hkl))
    (e6ae_bound_append (e6ae_romIdx_bound k l hkl) e6ae_lc_bound)
    (e6ae_comm_packed_rom k l hkl)

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem cE_mem_centralizer_jE :
    cE ∈ Subgroup.centralizer (jE : Set EC) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  rw [jE] at hj
  induction hj using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨k, l, hkl, hg | hg⟩
    · rw [hg]
      exact (e6ae_comm_rOne k l hkl).symm
    · rw [hg]
      exact (e6ae_comm_rOmega k l hkl).symm
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [mul_assoc, ihy, ← mul_assoc, ihx, mul_assoc]
  | inv x hx ih =>
    calc x⁻¹ * cE = x⁻¹ * (cE * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * cE) * x⁻¹ := by rw [ih]
      _ = cE * x⁻¹ := by group

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

private theorem e6ae_phiE_packed_self :
    e6ae_pW (e6ae_lphi ++ e6ae_lphi) = e6ae_pW [] := by decide +kernel

private theorem e6ae_phiE_packed_w :
    e6ae_pW (e6ae_lphi ++ e6ae_lw ++ e6ae_lphi.reverse) = e6ae_pW e6ae_lw.reverse := by
  decide +kernel

private theorem e6ae_phiE_packed_rOne :
    ∀ k l : Fin 3, k ≠ l →
      e6ae_pW (e6ae_lphi ++ e6ae_roIdx k l ++ e6ae_lphi.reverse) =
        e6ae_pW (e6ae_roIdx k l) := by
  decide +kernel

private theorem e6ae_phiE_packed_rOmega :
    ∀ k l : Fin 3, k ≠ l →
      e6ae_pW (e6ae_lphi ++ e6ae_romIdx k l ++ e6ae_lphi.reverse) =
        e6ae_pW (e6ae_romIdx k l ++ e6ae_roIdx k l) := by
  decide +kernel

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

private theorem e6ae_conj_mem_closure {G : Type*} [Group G] {s : Set G} {H : Subgroup G} {g : G}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ H) : ∀ x ∈ Subgroup.closure s, g * x * g⁻¹ ∈ H := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => simp
  | mul y z hy hz ihy ihz =>
    rw [show g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) by group]
    exact H.mul_mem ihy ihz
  | inv y hy ihy =>
    rw [show g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ by group]
    exact H.inv_mem ihy

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

private theorem e6ae_phiE_mul_self :
    phiE * phiE = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_one]
  rw [e6ae_phiE_eq, ← e6ae_wECm_append,
    e6ae_wECm_eq_of_packed (e6ae_lphi ++ e6ae_lphi) [] (by decide) (by decide)
      e6ae_phiE_packed_self]
  rfl

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

private theorem e6ae_phiE_mem_lE :
    phiE ∈ lE := by
  rw [lE, ← E6Pilot.range_slToAdjointE6]
  refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) 1 *
    Matrix.SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 3 by decide) 1 *
    Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) 1, ?_⟩
  rw [map_mul, map_mul, E6Pilot.slToAdjointE6_transvection, E6Pilot.slToAdjointE6_transvection,
    E6Pilot.slToAdjointE6_transvection]
  rfl

end CFSG.StandardType.GGSixE6Two

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

private theorem e6ae_mem_normalizer_of_conj {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hg : g * g = 1) : g ∈ Subgroup.normalizer H := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h x hx
  · intro hx
    have h2 := h (g * x * g⁻¹) hx
    have h3 : g * (g * x * g⁻¹) * g⁻¹ = x := by
      have hg' : g⁻¹ * g⁻¹ = 1 := by rw [← mul_inv_rev, hg, inv_one]
      calc g * (g * x * g⁻¹) * g⁻¹ = (g * g) * x * (g⁻¹ * g⁻¹) := by group
        _ = x := by rw [hg, hg']; group
    rwa [h3] at h2

private theorem e6ae_phiE_conj_rOne
    (k l : Fin 3) (hkl : k ≠ l) :
    phiE * rOne k l * phiE⁻¹ = rOne k l := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e6ae_phiE_eq, e6ae_rOne_eq k l hkl, e6ae_wECm_inv]
  rw [← e6ae_wECm_append, ← e6ae_wECm_append]
  exact e6ae_wECm_eq_of_packed (e6ae_lphi ++ e6ae_roIdx k l ++ e6ae_lphi.reverse)
    (e6ae_roIdx k l)
    (e6ae_bound_append (e6ae_bound_append e6ae_lphi_bound (e6ae_roIdx_bound k l hkl))
      e6ae_lphi_rev_bound)
    (e6ae_roIdx_bound k l hkl)
    (e6ae_phiE_packed_rOne k l hkl)

private theorem e6ae_phiE_conj_rOmega
    (k l : Fin 3) (hkl : k ≠ l) :
    phiE * rOmega k l * phiE⁻¹ = rOmega k l * rOne k l := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e6ae_phiE_eq, e6ae_rOmega_eq k l hkl, e6ae_wECm_inv, e6ae_rOne_eq k l hkl]
  rw [← e6ae_wECm_append, ← e6ae_wECm_append, ← e6ae_wECm_append]
  exact e6ae_wECm_eq_of_packed (e6ae_lphi ++ e6ae_romIdx k l ++ e6ae_lphi.reverse)
    (e6ae_romIdx k l ++ e6ae_roIdx k l)
    (e6ae_bound_append (e6ae_bound_append e6ae_lphi_bound (e6ae_romIdx_bound k l hkl))
      e6ae_lphi_rev_bound)
    (e6ae_bound_append (e6ae_romIdx_bound k l hkl) (e6ae_roIdx_bound k l hkl))
    (e6ae_phiE_packed_rOmega k l hkl)

private theorem e6ae_phiE_conj_w :
    phiE * wOmegaE * phiE⁻¹ = wOmegaE⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, e6ae_phiE_eq, e6ae_wOmegaE_eq, e6ae_wECm_inv]
  rw [← e6ae_wECm_append, ← e6ae_wECm_append]
  exact e6ae_wECm_eq_of_packed (e6ae_lphi ++ e6ae_lw ++ e6ae_lphi.reverse) e6ae_lw.reverse
    (e6ae_bound_append (e6ae_bound_append e6ae_lphi_bound e6ae_lw_bound) e6ae_lphi_rev_bound)
    e6ae_lw_rev_bound
    e6ae_phiE_packed_w

private theorem e6ae_phiE_mem_normalizer_jE :
    phiE ∈ Subgroup.normalizer (jE : Set EC) := by
  refine e6ae_mem_normalizer_of_conj ?_ e6ae_phiE_mul_self
  intro x hx
  rw [jE] at hx
  exact e6ae_conj_mem_closure (H := jE) (g := phiE)
    (s := {g | ∃ k l : Fin 3, k ≠ l ∧ (g = rOne k l ∨ g = rOmega k l)}) (fun y hy => by
    rcases hy with ⟨k, l, hkl, hy | hy⟩
    · rw [hy, e6ae_phiE_conj_rOne k l hkl]
      exact Subgroup.subset_closure ⟨k, l, hkl, Or.inl rfl⟩
    · rw [hy, e6ae_phiE_conj_rOmega k l hkl]
      exact jE.mul_mem (Subgroup.subset_closure ⟨k, l, hkl, Or.inr rfl⟩)
        (Subgroup.subset_closure ⟨k, l, hkl, Or.inl rfl⟩)) x hx

private theorem e6ae_phiE_mem_normalizer_rE :
    phiE ∈ Subgroup.normalizer (rE : Set EC) := by
  refine e6ae_mem_normalizer_of_conj ?_ e6ae_phiE_mul_self
  intro x hx
  rw [rE] at hx
  exact e6ae_conj_mem_closure (H := rE) (g := phiE)
    (s := {g | g = rOne 0 2 ∨ g = rOmega 0 2}) (fun y hy => by
    rcases hy with hy | hy
    · rw [hy, e6ae_phiE_conj_rOne 0 2 (by decide)]
      exact Subgroup.subset_closure (Or.inl rfl)
    · rw [hy, e6ae_phiE_conj_rOmega 0 2 (by decide)]
      exact rE.mul_mem (Subgroup.subset_closure (Or.inr rfl))
        (Subgroup.subset_closure (Or.inl rfl))) x hx

theorem phiE_facts :
    phiE ∈ lE ∧ phiE * wOmegaE * phiE⁻¹ = wOmegaE⁻¹ ∧
      phiE ∈ Subgroup.normalizer (jE : Set EC) ∧ phiE ∈ Subgroup.normalizer (rE : Set EC) :=
  ⟨e6ae_phiE_mem_lE, e6ae_phiE_conj_w, e6ae_phiE_mem_normalizer_jE,
    e6ae_phiE_mem_normalizer_rE⟩

end CFSG.StandardType.GGSixE6Two
