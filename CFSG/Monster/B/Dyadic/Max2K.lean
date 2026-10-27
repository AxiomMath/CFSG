module

public import CFSG.Monster.B.Dyadic.PinnedK
public import CFSG.Certificates.Kernel.BabyMonster.VStripSound
public import CFSG.Certificates.Kernel.BabyMonster.NativePair.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data1
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data3
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data4
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data5
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data6
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data7
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data8
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data9
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data10
public import CFSG.Certificates.Kernel.BabyMonster.Max2.Data11
public import CFSG.Certificates.Kernel.BabyMonster.Max2Br.Data2
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Data0
public import CFSG.Certificates.Kernel.BabyMonster.Max2T.Data1
public import CFSG.Monster.B.Dyadic.BridgeK
public import CFSG.Certificates.Kernel.BabyMonster.Sound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Pinned.GeneratorDeterminants
public import CFSG.Open.Defs
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile
public import Certificates.Data.Kernel.BabyMonster.Bridge24

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.KC.BM
open scoped Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] noncomputable def wordQK (w : List ℕ) : MatB := (w.map QnK).prod

@[expose] noncomputable def XK : MatB := stripMat Max2.Xb

@[expose] noncomputable def VK : MatB := stripMat Max2.V01

@[expose] noncomputable def ZK : MatB := stripMat Max2T.Z

@[expose] noncomputable def ZwK : MatB := stripMat Max2T.Zw

@[expose] noncomputable def YK : MatB := stripMat Max2T.Yz

@[expose] noncomputable def UK : MatB := stripMat Max2T.U

@[expose] noncomputable def ZqK : MatB := stripMat Max2Br.Zq

@[expose] noncomputable def UzK : MatB := stripMat Max2T.Uz

@[expose] noncomputable def CK : MatB := stripMat Max2.C

@[expose] noncomputable def CiK : MatB := stripMat Max2.Ci

@[expose] noncomputable def G1K : MatB := stripMat Max2.G1

@[expose] noncomputable def G2K : MatB := stripMat Max2.G2

@[expose] noncomputable def Gi2K : MatB := stripMat Max2.Gi2

@[expose] noncomputable def KK : MatB := stripMat Max2.K

@[expose] noncomputable def Elist : List (List Nat) :=
  [NativePair.Q0, Max2.E1, Max2.E2, Max2.E3, Max2.E4, Max2.E5, Max2.E6, Max2.E7, Max2.E8, Max2.E9,
    Max2.E10, Max2.E11, Max2.E12, Max2.E13, Max2.E14, Max2.E15, Max2.E16, Max2.E17, Max2.E18,
    Max2.E19, Max2.E20, Max2.E21]

@[expose] noncomputable def EK (i : ℕ) : MatB := stripMat (Elist.getD i [])

@[expose] noncomputable def prefixK (i : ℕ) : MatB :=
  wordQK (CFSG.Monster.B.Bin.basisWord.take (CFSG.Monster.B.Bin.basisLens.getD i 0))

@[expose] def bridgeZE : List ℕ := [4, 7, 9, 10, 11, 15, 16, 17, 20]

@[expose] def rowBitK (rows : List ℕ) (i j : ℕ) : ℕ := if (rows.getD i 0).testBit j then 1 else 0

@[expose] def actK (rows : List ℕ) (i j : ℕ) : ℕ :=
  (∑ l ∈ Finset.range 22,
    ((rowBitK rows i l * rowBitK CFSG.Monster.B.Bin.gramRows l j : ℕ) : ZMod 2)).val

@[expose] def FactMax2 : Prop :=
  ((QnK 1 * VK = QnK 0 * QnK 1 ∧ (QnK 0 * VK) ^ 2 = XK) ∧
  (XK * XK = 1 ∧ XK ≠ 1) ∧
  TK * dK ^ 24 = ZK * TK ∧
  wordQK CFSG.Monster.B.Bin.parityWord24 * ZwK = ZK * wordQK CFSG.Monster.B.Bin.parityWord24 ∧
  (ZwK * XK = YK ∧ YK ^ 5 = 1 ∧ YK ≠ 1) ∧
  (wordQK CFSG.Monster.B.Bin.parityWord24 * YK ^ 3 = UK ∧ UK * ZqK = UzK ∧
    ZK * UzK = UzK * XK ∧ ZqK = XK * (bridgeZE.map EK).prod) ∧
  (UzK * CK * wordCD CFSG.Monster.B.Bin.bridgeU = TK * wordCD CFSG.Monster.B.Bin.bridgeV ∧
    CK * CiK = 1) ∧
  (CK * cK = G1K * CK ∧ CK * dK = G2K * CK ∧ G2K * Gi2K = 1) ∧
  (∀ i < 22, prefixK i * EK i = QnK 0 * prefixK i) ∧
  e0 ᵥ* XK ≠ e0 ∧
  (∀ i j, i < 22 → j < 22 → e0 ᵥ* (EK i * EK j) =
    e0 ᵥ* (EK j * XK ^ rowBitK CFSG.Monster.B.Bin.gramRows i j * EK i)) ∧
  (∀ i j, i < 22 → j < 22 → e0 ᵥ* (G1K * EK i * G1K * EK j) =
    e0 ᵥ* (EK j * XK ^ actK CFSG.Monster.B.Bin.quotRows1 i j * (G1K * EK i * G1K))) ∧
  (∀ i j, i < 22 → j < 22 → e0 ᵥ* (Gi2K * EK i * G2K * EK j) =
    e0 ᵥ* (EK j * XK ^ actK CFSG.Monster.B.Bin.quotRows2 i j * (Gi2K * EK i * G2K))) ∧
  (KK = (G2K * G1K * G1K * G2K * G2K * G1K) ^ 14 ∧ KK * KK = 1 ∧ KK ≠ 1 ∧ KK ≠ XK) ∧
  QnK 25 * QnK 25 * XK * QnK 25 * XK = XK * (QnK 25 * QnK 25 * XK * QnK 25) ∧
  (genA₂ * genA₂ * dK ^ 24 * genA₂ * (CiK * (QnK 25 * QnK 25 * XK * QnK 25) * CK)) ^ 5 = 1) ∧
  XK = rowsK Max2.Xb.rows ∧ CK = rowsK Max2.C.rows ∧ CiK = rowsK Max2.Ci.rows ∧
  G1K = rowsK Max2.G1.rows ∧ G2K = rowsK Max2.G2.rows

end CFSG.Monster.B.Dyadic

end
