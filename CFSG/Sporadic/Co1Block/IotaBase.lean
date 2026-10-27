
module

public import CFSG.Sporadic.Co1Block.IotaCheckBase
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
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer

@[expose] public noncomputable section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

theorem extendTuple_map {G H : Type*} [Group G] [Group H] (f : G →* H) :
    ∀ (gs : List G) (ds : List (List ℤ)), (extendTuple gs ds).map f = extendTuple (gs.map f) ds
  | _, [] => rfl
  | gs, w :: ds => by
    rw [extendTuple_cons, extendTuple_cons, extendTuple_map f _ ds, List.map_append,
      List.map_singleton, CFSG.Sporadic.Schreier.wordValue_map]

theorem getD_map_one {G H : Type*} [Group G] [Group H] (f : G →* H) (gs : List G) (k : ℕ) :
    (gs.map f).getD k 1 = f (gs.getD k 1) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases gs[k]? <;> simp

theorem letterValue_eq_letterG (gs : List GL24) (j : ℤ) : letterValue gs j = letterG gs j := by
  unfold letterValue letterG
  by_cases hj : 0 < j
  · simp only [hj, ↓reduceIte]
    congr 2
    omega
  · simp only [hj, ↓reduceIte]
    congr 3
    omega

theorem wordValue_eq_wordG (gs : List GL24) (w : List ℤ) : wordValue gs w = wordG gs w := by
  unfold wordValue wordG
  rw [List.prod_eq_foldl, List.foldl_map]
  simp only [letterValue_eq_letterG]

theorem extendTuple_eq_dagG : ∀ (gs : List GL24) (ds : List (List ℤ)),
    extendTuple gs ds = dagG gs ds
  | gs, [] => rfl
  | gs, w :: ds => by
    rw [extendTuple_cons, wordValue_eq_wordG, extendTuple_eq_dagG _ ds]
    rfl

@[expose] def iotaH : List stabH := extendTuple [stabG0, stabG1] iotaDerivs

@[expose] def iotaA : stabH := iotaH.getD 23 1

@[expose] def iotaC : stabH := iotaH.getD 51 1

@[expose] def iotaQ (k : ℕ) : stabH := iotaH.getD (36 + k) 1

theorem iotaH_map_cls :
    iotaH.map clsHom = extendTuple aSeeds iotaDerivs := by
  rw [iotaH, extendTuple_map]
  simp only [List.map_cons, List.map_nil, clsHom_stabG0, clsHom_stabG1]
  rfl

theorem iotaH_map_val : iotaH.map stabH.subtype = dagG [stabH0, stabH1] iotaDerivs := by
  rw [iotaH, extendTuple_map, ← extendTuple_eq_dagG]
  simp only [List.map_cons, List.map_nil, Subgroup.coe_subtype, coe_stabG0, coe_stabG1]

theorem iotaH_length : iotaH.length = 52 := by
  rw [iotaH, extendTuple_length]
  rfl

abbrev co2U : co2P := ⟨locU, locU_mem⟩

theorem qTuple_length' : qTuple.length = 8 := by
  rw [qTuple, List.length_map, localShape.qWords_length]

@[expose] def iotaRows : List CFSG.Sporadic.Co1Schreier.Native.Rows :=
  (CFSG.Sporadic.Co1Schreier.Native.dag [Native.hRows0, Native.hRows1] iotaDerivs).1

@[expose] def iotaARows : CFSG.Sporadic.Co1Schreier.Native.Rows :=
  iotaRows.getD 23 CFSG.Sporadic.Co1Schreier.Native.one

@[expose] def iotaCRows : CFSG.Sporadic.Co1Schreier.Native.Rows :=
  iotaRows.getD 51 CFSG.Sporadic.Co1Schreier.Native.one

@[expose] def iotaQRows (k : ℕ) : CFSG.Sporadic.Co1Schreier.Native.Rows :=
  iotaRows.getD (36 + k) CFSG.Sporadic.Co1Schreier.Native.one

theorem iotaA_mem_GA : (iotaA : GL24) ∈ GA := stabH_le_GA iotaA.2

theorem iotaC_mem_GA : (iotaC : GL24) ∈ GA := stabH_le_GA iotaC.2

theorem iotaQ_mem_GA (k : ℕ) : (iotaQ k : GL24) ∈ GA := stabH_le_GA (iotaQ k).2

end CFSG.Sporadic.Co1Block
