
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionImageBase

public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbit
public import CFSG.Monster.B.TwoA.Sp8.NormalizerData
public import CFSG.Monster.B.TwoA.Co2Inv.Kernel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionOrbit
public import Certificates.Certificate3077
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionConj
public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertInputs
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import CFSG.Monster.B.TwoA.Co2Inv.SixCertInputs
public import CFSG.Monster.B.Rep4371.SmallFaithful
public import CFSG.Monster.B.Gen.Max2Assembly
public import CFSG.Monster.B.Gen.PacketGeneration
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Rep4371.FaithfulImageInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8
public import CFSG.Monster.B.TwoA.Co2Inv.SixAction
public import CFSG.Monster.B.TwoA.Base.Space34A
public import CFSG.Monster.B.TwoA.Sp8.PsiInputs
public import CFSG.Monster.B.TwoA.Base.PairSpace
public import CFSG.Monster.B.TwoA.Base.Space34AInputs
public import Certificates.Certificate3055Base

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Co2Inv

theorem altCheck : ∀ v : V8, ∑ i, ∑ j, v i * gram0 i j * v j = 0 :=
  Certificates.certificate3077

theorem b0_isAlt : b0.IsAlt := fun v => by
  rw [b0, Matrix.toBilin'_apply]
  exact altCheck v

theorem natCard_Sp : Nat.card (TauCeti.BilinForm.isometryGroup b0) =
    47377612800 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup 4 b0 b0_isAlt
    b0_nondegenerate finrank_V8, Nat.card_zmod]
  decide

theorem aEquiv_e0 :
    (aEquiv (Multiplicative.ofAdd e0) : Dfull) = xhat := aEquiv_single 0

theorem closure_xGenL_le_Sp :
    Subgroup.closure (Set.range xGenL) ≤ TauCeti.BilinForm.isometryGroup b0 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact xGenL_mem_isometryGroup k

theorem orbit_Sp_e0 :
    MulAction.orbit (TauCeti.BilinForm.isometryGroup b0) e0 = {v : V8 | v ≠ 0} := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    show (g : V8 ≃ₗ[ZMod 2] V8) e0 ≠ 0
    rw [LinearEquiv.map_ne_zero_iff]
    exact Pi.single_ne_zero_iff.2 one_ne_zero
  · intro hv
    obtain ⟨f, hf, hfv⟩ := exists_conjImage_X hv
    exact ⟨⟨f, closure_xGenL_le_Sp hf⟩, hfv⟩

theorem natCard_SpX :
    Nat.card SpX = 185794560 := by
  have hi := MulAction.index_stabilizer (TauCeti.BilinForm.isometryGroup b0) e0
  have hc := (MulAction.stabilizer (TauCeti.BilinForm.isometryGroup b0) e0).card_mul_index
  have hi' : (MulAction.stabilizer (TauCeti.BilinForm.isometryGroup b0) e0).index = 255 :=
    hi.trans ((congrArg Set.ncard orbit_Sp_e0).trans ncard_nonzero)
  refine (congrArg (fun H : Subgroup (V8 ≃ₗ[ZMod 2] V8) => Nat.card H) SpX_eq_map).trans ?_
  refine (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).trans ?_
  exact card_quot hc hi' natCard_Sp

theorem H1_le_Xgrp :
    H1 ≤ Xgrp := fun _ h => Subgroup.subset_closure (Set.mem_insert_of_mem _ h)

theorem conjImage_X_le_Sp :
    (Xgrp.subgroupOf NA8).map conjHom ≤ TauCeti.BilinForm.isometryGroup b0 :=
  conjImage_X_le

theorem conjHom_e0_of_mem_Jhat
    {n : NA8} (hn : (n : Dfull) ∈ Jhat) : conjHom n e0 = e0 := by
  apply aEquiv_coe_injective
  rw [aEquiv_conjHom, aEquiv_e0, xhat_comm_of_mem_Jhat hn, mul_inv_cancel_right]

theorem conjImage_H1_le :
    (H1.subgroupOf NA8).map conjHom ≤ SpX := by
  rintro _ ⟨n, hn, rfl⟩
  have hn' : (n : Dfull) ∈ H1 := Subgroup.mem_subgroupOf.1 hn
  exact mem_SpX.2 ⟨conjImage_X_le_Sp ⟨n, Subgroup.mem_subgroupOf.2 (H1_le_Xgrp hn'), rfl⟩,
    conjHom_e0_of_mem_Jhat (H1_le_Jhat hn')⟩

@[expose] def piH1 : H1 →* Cr :=
  (jhatToKv0.comp (Subgroup.inclusion H1_le_Jhat)).codRestrict Cr fun h => by
    obtain ⟨hJ, hC⟩ := (mem_H1_iff h).1 h.2
    exact hC

theorem coe_piH1 (h : H1) :
    (piH1 h : Kstab v0) = jhatToKv0 ⟨h, H1_le_Jhat h.2⟩ := rfl

theorem piH1_surjective :
    Function.Surjective piH1 := by
  intro c
  obtain ⟨j, hj⟩ := jhatToKv0_surjective (c : Kstab v0)
  have hH : (j : Dfull) ∈ H1 := (mem_H1_iff _).2 ⟨j.2, by rw [hj]; exact c.2⟩
  exact ⟨⟨j, hH⟩, Subtype.ext hj⟩

@[expose] def sigH1 :
    H1 →* TauCeti.BilinForm.isometryGroup bZ := resZ.comp piH1

theorem sigH1_surjective :
    Function.Surjective sigH1 :=
  resZ_surjective_natCard_ker.1.comp piH1_surjective

theorem natCard_range_sigH1 :
    Nat.card sigH1.range =
    1451520 :=
  ((Subgroup.card_eq_iff_eq_top _).2 (MonoidHom.range_eq_top.2 sigH1_surjective)).trans
    natCard_isometryGroup_bZ

@[expose] def rhoH1 :
    H1 →* (V8 ≃ₗ[ZMod 2] V8) :=
  conjHom.comp (Subgroup.inclusion H1_le_normalizer)

theorem range_rhoH1 :
    rhoH1.range =
    (H1.subgroupOf NA8).map conjHom := by
  ext f
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨Subgroup.inclusion H1_le_normalizer h, h.2, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩

theorem centralizes_of_rhoH1
    {h : H1}
    (hh : rhoH1 h = 1) {x : Dfull} (hx : x ∈ A8) :
    (h : Dfull)⁻¹ * x * h = x := by
  obtain ⟨v, hv⟩ := aEquiv.surjective ⟨x, hx⟩
  have hx' : x = aEquiv v := congrArg Subtype.val hv.symm
  have e1 : (aEquiv (Multiplicative.ofAdd (rhoH1 h (Multiplicative.toAdd v))) : Dfull) =
      h * aEquiv (Multiplicative.ofAdd (Multiplicative.toAdd v)) * (h : Dfull)⁻¹ :=
    aEquiv_conjHom _ _
  have e2 : rhoH1 h (Multiplicative.toAdd v) = Multiplicative.toAdd v := by rw [hh]; rfl
  rw [e2, ofAdd_toAdd, ← hx'] at e1
  calc (h : Dfull)⁻¹ * x * h = (h : Dfull)⁻¹ * (h * x * (h : Dfull)⁻¹) * h := by rw [← e1]
    _ = x := by group

theorem wAct_fix_of_rhoH1
    {h : H1}
    (hh : rhoH1 h = 1) (v : Fin 8 → ZMod 2) :
    wAct v0 (jhatToKv0 ⟨h, H1_le_Jhat h.2⟩) (psiB v) = psiB v := by
  have hc := centralizes_of_rhoH1 hh (B7_le_A8 (PhiD_mem_B7 v))
  have e := psiW_conj (H1_le_Jhat h.2) (B7_le_Ehat (PhiD_mem_B7 v))
  refine e.symm.trans ?_
  exact congrArg psiW (Subtype.ext hc)

theorem sigH1_eq_one_of_rhoH1
    {h : H1}
    (hh : rhoH1 h = 1) : sigH1 h = 1 :=
  resZ_eq_one_of_fix (piH1 h) fun z hz => by
    obtain ⟨v, rfl⟩ := exists_psiB hz
    exact wAct_fix_of_rhoH1 hh v

theorem ker_rhoH1_le :
    rhoH1.ker ≤
    sigH1.ker := fun _ hh =>
  MonoidHom.mem_ker.2 (sigH1_eq_one_of_rhoH1 (MonoidHom.mem_ker.1 hh))

theorem Ehat_le_H1 :
    Ehat ≤ H1 := fun e he =>
  (mem_H1_iff e).2 ⟨Ehat_le_Jhat he, by
    rw [jhatToKv0_eq_one_of_mem_Ehat _ he]
    exact Cr.one_mem⟩

theorem Ehat_le_ker_sigH1
    {e : Dfull} (he : e ∈ Ehat) (hH : e ∈ H1) :
    (⟨e, hH⟩ : H1) ∈ sigH1.ker := by
  have h1 : piH1 ⟨e, hH⟩ = 1 :=
    Subtype.ext ((coe_piH1 _).trans (jhatToKv0_eq_one_of_mem_Ehat _ he))
  exact MonoidHom.mem_ker.2 ((congrArg resZ h1).trans (map_one resZ))

theorem natCard_range_rhoH1 :
    Nat.card rhoH1.range = Nat.card (rhoH1.domRestrict sigH1.ker).range * 1451520 := by
  have h1 := natCard_ker_mul_range rhoH1
  have h2 := natCard_ker_mul_range sigH1
  have h3 := natCard_ker_mul_range (rhoH1.domRestrict sigH1.ker)
  have hk : Nat.card (rhoH1.domRestrict sigH1.ker).ker = Nat.card rhoH1.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe ker_rhoH1_le).toEquiv
  have h2' : Nat.card sigH1.ker * 1451520 = Nat.card H1 :=
    (congrArg (fun t => Nat.card sigH1.ker * t) natCard_range_sigH1).symm.trans h2
  have h3' : Nat.card rhoH1.ker * Nat.card (rhoH1.domRestrict sigH1.ker).range =
      Nat.card sigH1.ker :=
    (congrArg (fun t => t * Nat.card (rhoH1.domRestrict sigH1.ker).range) hk).symm.trans h3
  exact card_split h1 h2' h3' Nat.card_pos

theorem conjImage_Ehat_le :
    (Ehat.subgroupOf NA8).map conjHom ≤ (rhoH1.domRestrict sigH1.ker).range := by
  rintro _ ⟨n, hn, rfl⟩
  have hn' : (n : Dfull) ∈ Ehat := Subgroup.mem_subgroupOf.1 hn
  exact ⟨⟨⟨n, Ehat_le_H1 hn'⟩, Ehat_le_ker_sigH1 hn' (Ehat_le_H1 hn')⟩, rfl⟩

theorem natCard_conjImage_H1_ge :
    128 * 1451520 ≤ Nat.card ((H1.subgroupOf NA8).map conjHom) := by
  have h := Subgroup.card_le_of_le conjImage_Ehat_le
  have e := (congrArg (fun H : Subgroup (V8 ≃ₗ[ZMod 2] V8) => Nat.card H) range_rhoH1).symm.trans
    natCard_range_rhoH1
  calc 128 * 1451520 = Nat.card ((Ehat.subgroupOf NA8).map conjHom) * 1451520 :=
        congrArg (· * 1451520) natCard_conjImage_Ehat.symm
    _ ≤ Nat.card (rhoH1.domRestrict sigH1.ker).range * 1451520 := Nat.mul_le_mul_right _ h
    _ = Nat.card ((H1.subgroupOf NA8).map conjHom) := e.symm

theorem conjImage_H1_eq :
    (H1.subgroupOf NA8).map conjHom = SpX :=
  Subgroup.eq_of_le_of_card_ge conjImage_H1_le (by
    rw [natCard_SpX]
    exact natCard_conjImage_H1_ge)

end CFSG.Monster.B.TwoA.Sp8
