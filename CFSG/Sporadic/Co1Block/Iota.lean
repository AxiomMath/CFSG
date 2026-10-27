
module

public import CFSG.Sporadic.Co1Block.IotaBase

public import CFSG.Sporadic.Co1Block.IotaCheck
public import CFSG.Sporadic.Schreier.Co1StabLift
public import CFSG.Sporadic.Co2Schreier.ThirdOrder
public import CFSG.Sporadic.Co2Schreier.Centralizers
public import CFSG.Sporadic.Schreier.MathieuSylowAutSpec
public import CFSG.Sporadic.Co2Schreier.Tuples
public import CFSG.Sporadic.Co2Schreier.Chains
public import CFSG.Sporadic.Co1Block.IotaCheckInputs
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Sporadic.Co2Schreier.TextCheck
public meta import CFSG.Sporadic.Co2Cert.Cert
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Schreier.Co1AutCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1AutData
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
public import CFSG.Sporadic.Schreier.Co1OrbEnum
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Sporadic.Schreier.Co1XSet
public import CFSG.Sporadic.Schreier.Co1LiftCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1LiftData
public meta import CFSG.Sporadic.Co2Cert.Data
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public import CFSG.Sporadic.Schreier.Co1StabCheckInputs
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

public noncomputable section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

theorem iota_facts :
    (CFSG.Sporadic.Co1Schreier.Native.dag [Native.hRows0, Native.hRows1]
      iotaDerivs).2.2 = true ∧ extWordsOK 2 iotaDerivs = true ∧
    allInv (extendArrs aArrs iotaDerivs) = true ∧
    eqA 2300 (extendArrs aArrs iotaDerivs)[23]! zArr = true ∧
    eqA 2300 (extendArrs aArrs iotaDerivs)[51]! uArr = true ∧
    ∀ k < 8, eqA 2300 (extendArrs aArrs iotaDerivs)[36 + k]! qArrs[k]! = true := by
  have h := iota_check
  simp only [iotaCheckOf, Bool.and_eq_true, allLt_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem repTuple_iota :
    RepTuple 2300 (extendArrs aArrs iotaDerivs) (extendTuple aSeeds iotaDerivs) :=
  repTuple_a.extend (by rw [show aSeeds.length = 2 from rfl]; exact iota_facts.2.1)
    iota_facts.2.2.1

theorem cls_iotaH
    {k : ℕ} (hk : k < 52) :
    Rep 2300 (extendArrs aArrs iotaDerivs)[k]! (clsHom (iotaH.getD k 1)) := by
  have h := repTuple_iota.2 k (by rw [← iotaH_map_cls, List.length_map, iotaH_length]; exact hk)
  rwa [← iotaH_map_cls, getD_map_one] at h

theorem stabPermEquiv_iotaA :
    stabPermEquiv iotaA = zP :=
  Subtype.ext (by
    rw [stabPermEquiv_apply]
    exact eq_of_eqA (cls_iotaH (k := 23) (by norm_num)) rep_z iota_facts.2.2.2.1)

theorem stabPermEquiv_iotaC :
    stabPermEquiv iotaC = co2U :=
  Subtype.ext (by
    rw [stabPermEquiv_apply]
    exact eq_of_eqA (cls_iotaH (k := 51) (by norm_num)) rep_u iota_facts.2.2.2.2.1)

theorem clsHom_iotaQ
    {k : ℕ} (hk : k < 8) : clsHom (iotaQ k) = qTuple.getD k 1 :=
  eq_of_eqA (cls_iotaH (k := 36 + k) (by omega)) (repTuple_q.2 k (by rw [qTuple_length']; exact hk))
    (iota_facts.2.2.2.2.2 k hk)

theorem iotaA_eq :
    iotaA = stabPermEquiv.symm zP := by
  rw [← stabPermEquiv_iotaA, MulEquiv.symm_apply_apply]

theorem iotaC_eq :
    iotaC = stabPermEquiv.symm co2U := by
  rw [← stabPermEquiv_iotaC, MulEquiv.symm_apply_apply]

theorem rep_iotaRows :

    List.Forall₂ MRep iotaRows (dagG [stabH0, stabH1] iotaDerivs) :=
  dag_rep (.cons stabH0_rep (.cons stabH1_rep .nil)) iotaDerivs iota_facts.1

theorem rep_iotaH
    (k : ℕ) :
    MRep (iotaRows.getD k CFSG.Sporadic.Co1Schreier.Native.one)
      ((iotaH.getD k 1 : stabH) : GL24) := by
  have h := getD_rep rep_iotaRows MRep.one k
  rwa [← iotaH_map_val, getD_map_one] at h

theorem rep_iotaA :
    MRep iotaARows (iotaA : GL24) := rep_iotaH 23

theorem rep_iotaC :
    MRep iotaCRows (iotaC : GL24) := rep_iotaH 51

theorem rep_iotaQ
    (k : ℕ) : MRep (iotaQRows k) (iotaQ k : GL24) := rep_iotaH (36 + k)

end CFSG.Sporadic.Co1Block
