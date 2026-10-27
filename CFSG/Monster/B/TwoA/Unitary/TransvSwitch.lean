module

public import CFSG.Monster.B.TwoA.Unitary.Transv
public meta import CFSG.Monster.B.TwoA.Unitary.Planes
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Co2Inv.Rows
public meta import CFSG.Monster.B.Co2.Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.TransvSwitchInputs
public import Certificates.Certificate3127
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3175
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate16016
import CFSG.Fischer.F4

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Co2Inv Matrix Module
open CFSG.Monster.B.Classical.UnitarySix (bar bar_one)
open CFSG.Monster.B.TwoA.Amalgam (e6)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)

theorem wAct_alphaKv (i : Fin 24) :
    wAct v0 (alphaKv i) = rowsEnd (genQuotMatrix i) :=
  wAct_alpha i

theorem wAct_swG :
    wAct v0 swG = rowsEnd swGRows := by
  rw [swG, wAct_mul, wAct_mul, wAct_mul, wAct_alphaKv, wAct_alphaKv, wAct_alphaKv, wAct_alphaKv,
    rowsEnd_mul, rowsEnd_mul, rowsEnd_mul, swGRows]

theorem swGRows_tau : Native.actD 22 swGRows 60 = 6144 :=
  Certificates.certificate3127.1

theorem wAct_swG_tauW :
    wAct v0 swG tauW = sigmaW := by
  rw [wAct_swG, tauW, o14Tau, rowsEnd_decW, swGRows_tau, sigmaW_eq_decW]

theorem swG_mul_inv_rows :
    Co2Inv.rowsMul swGRows swGInvRows = Co2Inv.idRows :=
  Certificates.certificate3127.2.1

theorem wAct_swG_inv :
    wAct v0 swG⁻¹ = rowsEnd swGInvRows := by
  have h1 : rowsEnd swGInvRows * wAct v0 swG = 1 := by
    rw [wAct_swG, rowsEnd_mul, swG_mul_inv_rows, rowsEnd_idRows]
  have h2 : wAct v0 swG * wAct v0 swG⁻¹ = 1 := by
    rw [← wAct_mul, inv_mul_cancel, wAct_one]
  calc wAct v0 swG⁻¹ = (rowsEnd swGInvRows * wAct v0 swG) * wAct v0 swG⁻¹ := by
        rw [h1, one_mul]
    _ = rowsEnd swGInvRows := by rw [mul_assoc, h2, mul_one]

@[expose] def swQ :
    Kstab v0 := swG⁻¹ * rK * swG

theorem wAct_rK_alpha :
    wAct v0 rK = rowsEnd (genQuotMatrix 12) := wAct_alpha 12

theorem wAct_swQ :
    wAct v0 swQ = rowsEnd swQRows := by
  rw [swQ, wAct_mul, wAct_mul, wAct_swG, wAct_swG_inv, wAct_rK_alpha, rowsEnd_mul, rowsEnd_mul,
    swQRows]

theorem swQRows_sigma : Native.actD 22 swQRows 6144 = 6144 :=
  Certificates.certificate3127.2.2.1

theorem swQ_mem_Usig :
    swQ ∈ Usig := by
  change wAct v0 swQ sigmaW = sigmaW
  rw [wAct_swQ, sigmaW_eq_decW, rowsEnd_decW, swQRows_sigma]

@[expose] def swU :
    Usig := ⟨swQ, swQ_mem_Usig⟩

theorem swMat_det : swMat.det = 1 :=
  Certificates.certificate3127.2.2.2.1

theorem swMat_gram : swMat * hGram * (barM swMat)ᵀ = hGram :=
  Certificates.certificate3127.2.2.2.2.1

theorem barM_swMat_det : (barM swMat).det = 1 := by rw
    [det_barM, swMat_det, bar_one]

theorem barM_swMat_gram : barM swMat * hGram * (barM (barM swMat))ᵀ =
    hGram := by
  have h := congrArg barM swMat_gram
  rw [barM_mul, barM_mul, barM_hGram] at h
  exact h

@[expose] def swSU : SUh :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (barM swMat) (by rw [barM_swMat_det]; exact one_ne_zero),
    mem_SUh_iff_gram.2 ⟨barM_swMat_det, barM_swMat_gram⟩⟩

@[expose] def swElt : SigmaU6 :=
    ⟨(swSU : SUh ⧸ Zh), Multiplicative.ofAdd 1⟩

theorem sigmaAct_swElt (P : Submodule F4 V6) : sigmaAct P swElt =
    subMul (subBar P) swMat := by
  rw [swElt, sigmaAct_mk, subBarPow_one]
  change subBar (subMul P (barM swMat)) = _
  rw [subBar_subMul, barM_barM]

theorem barPowV_one (s : V6) : barPowV 1 s = barV s := ite_eq_right (by decide)

theorem sigmaAct_swElt_plane
    {p p' : Fin 891}
    (h : ∀ a : Fin 3, expand p' (barV (planeRow p a) ᵥ* swMat) = barV (planeRow p a) ᵥ* swMat) :
    sigmaAct (plane p) swElt = plane p' := by
  have hspan : sigmaAct (plane p) swElt =
      Submodule.span F4 (Set.range fun a => barV (planeRow p a) ᵥ* swMat) := by
    rw [sigmaAct_swElt, plane, subBar_span, subMul_span, ← Set.range_comp, ← Set.range_comp]
    rfl
  have hli : LinearIndependent F4 fun a => barV (planeRow p a) ᵥ* swMat := by
    have h1 := linearIndependent_vecMul (linearIndependent_barPowV (linearIndependent_planeRow p) 1)
      (A := swMat) (by rw [swMat_det]; exact one_ne_zero)
    simpa only [barPowV_one] using h1
  rw [hspan]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact (mem_plane_iff _ _).2 (h a)
  · rw [finrank_span_eq_card hli, Fintype.card_fin, finrank_plane]

theorem swIdx_ok : ∀ j : Fin 891,
    n6VecArr[(swIdx j : ℕ)]! = Native.actD 22 swQRows n6VecArr[(j : ℕ)]! ∧
    ∀ a : Fin 3, expand (b6Iso (swIdx j)) (barV (planeRow (b6Iso j) a) ᵥ* swMat) =
      barV (planeRow (b6Iso j) a) ᵥ* swMat :=
  Certificates.certificate3127.2.2.2.2.2

theorem natIdx_swU
    (j : Fin 891) : natIdx swU j =
    swIdx j := by
  apply n6vec_injective
  rw [n6vec_natIdx]
  change wAct v0 swQ (decW n6VecArr[(j : ℕ)]!) = decW n6VecArr[(swIdx j : ℕ)]!
  rw [wAct_swQ, rowsEnd_decW, (swIdx_ok j).1]

theorem phiU_swU :
    phiU swU = swElt := by
  have hall : ∀ j : Fin 891,
      sigmaAct (plane (b6Iso j)) (phiU swU) = sigmaAct (plane (b6Iso j)) swElt := by
    intro j
    rw [← plane_natIdx, natIdx_swU j, sigmaAct_swElt_plane (swIdx_ok j).2]
  have h1 : phiU swU * swElt⁻¹ = 1 := eq_one_of_sigmaAct_plane _ fun p => by
    obtain ⟨j, rfl⟩ := b6Iso_bijective.2 p
    rw [sigmaAct_mul, hall j, sigmaAct_inv_cancel]
  exact mul_inv_eq_one.1 h1

@[expose] def linU :
    Subgroup Usig :=
    (SemidirectProduct.rightHom.comp phiU.toMonoidHom).ker

theorem mem_linU
    {u : Usig} : u ∈ linU ↔
    (phiU u).right = 1 := Iff.rfl

theorem rightHom_comp_surjective :
    Function.Surjective (SemidirectProduct.rightHom.comp phiU.toMonoidHom :
      Usig →* Multiplicative (ZMod 2)) :=
  SemidirectProduct.rightHom_surjective.comp phiU.surjective

theorem index_linU :
    linU.index = 2 := by
  rw [linU, Subgroup.index_ker, MonoidHom.range_eq_top.2 rightHom_comp_surjective,
    Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem map_linU :
    linU.map phiU.toMonoidHom =
    (SemidirectProduct.inl : SUh ⧸ Zh →*
    SigmaU6).range := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, linU, ← MonoidHom.comap_ker,
    Subgroup.map_comap_eq_self_of_surjective phiU.surjective]

theorem nonempty_linU_equiv :
    Nonempty (linU ≃* unitaryPSU hF4 6) :=
  ⟨((linU.equivMapOfInjective phiU.toMonoidHom phiU.injective).trans
    (MulEquiv.subgroupCongr map_linU)).trans
    (((MonoidHom.ofInjective SemidirectProduct.inl_injective).symm).trans psiQ)⟩

theorem swU_not_mem_linU :
    swU ∉ linU := by
  rw [mem_linU, phiU_swU]
  change ¬(Multiplicative.ofAdd (1 : ZMod 2) = 1)
  decide

theorem native_unitary_transvection_switches_to_field_involution :
    (genK 6 : Kstab v0) = rK ∧ rK = alphaKv 12 ∧ phiU (genU 6) = transvSig (e6 2) ∧
    swG = alphaKv 4 * alphaKv 12 * alphaKv 23 * alphaKv 7 ∧
    wAct v0 swG tauW = sigmaW ∧
    swG⁻¹ * rK * swG ∈ Usig ∧ (swU : Kstab v0) = swG⁻¹ * rK * swG ∧
    (∀ i : Fin 6, swMat i = vec6 (#[5, 4, 29, 1092, 3393, 1024] : Array ℕ)[(i : ℕ)]!) ∧
    swMat.det = 1 ∧ swMat * hGram * (barM swMat)ᵀ = hGram ∧
    swElt = ⟨(swSU : SUh ⧸ Zh), Multiplicative.ofAdd 1⟩ ∧
    (((swSU : SUh) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = barM swMat ∧
    (∀ P : Submodule F4 V6, sigmaAct P swElt = subMul (subBar P) swMat) ∧
    phiU swU = swElt ∧
    linU.index = 2 ∧
    Nonempty (linU ≃* unitaryPSU hF4 6) ∧
    (∀ u : Usig, u ∈ linU ↔ (phiU u).right = 1) ∧
    swU ∉ linU :=
  ⟨Amalgam.genK_six, rfl, by rw [phiU_genU, transvSig_e6_two], rfl, wAct_swG_tauW, swQ_mem_Usig,
    rfl, fun _ => rfl, swMat_det, swMat_gram, rfl, rfl, sigmaAct_swElt, phiU_swU, index_linU,
    nonempty_linU_equiv, fun _ => mem_linU, swU_not_mem_linU⟩

end CFSG.Monster.B.TwoA.Unitary
