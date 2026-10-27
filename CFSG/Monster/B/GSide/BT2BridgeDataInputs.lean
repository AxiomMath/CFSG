module

public import CFSG.Monster.B.GSide.BT2MoveList
public import CFSG.Monster.B.GSide.BT2Block
public import CFSG.Monster.B.GSide.MuFourOmega
public meta import CFSG.Monster.B.GSide.BT2MoveList
public meta import CFSG.Monster.B.GSide.MuFourOmega
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public meta import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Monster.B.CTIB.Rep4371Main
public meta import CFSG.Monster.B.TwoA.Amalgam.CoFiberGraphAdj
public meta import CFSG.Monster.B.TwoA.Base.GeomNative
public meta import CFSG.Monster.B.TwoA.Par3.MainBase
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public meta import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public meta import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public meta import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public meta import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public meta import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public meta import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public meta import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase
public meta import CFSG.Monster.B.TwoA.Unitary.Twenty

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph

@[expose] def codeAdj (a b : ℕ) : Bool :=
  a != b && bWcode a b == 0 && bWcode b a == 0 && Co2.Native.vectors.contains a &&
    Co2.Native.vectors.contains b

@[expose] def codeGraph : SimpleGraph ℕ where
  Adj a b := codeAdj a b = true
  symm := ⟨fun a b h => by
    simp only [codeAdj, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h ⊢
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨⟨⟨⟨Ne.symm h1, h3⟩, h2⟩, h5⟩, h4⟩⟩
  loopless := ⟨fun a h => by simp [codeAdj] at h⟩

instance (a b : ℕ) : Decidable (codeGraph.Adj a b) :=
  decEq (codeAdj a b) true

@[expose] def CodeT (a b c : ℕ) : Prop :=
  codeAdj a b = true ∧ codeAdj b c = true ∧ codeAdj c a = true ∧
    Co2.Native.vectors.contains (a ^^^ b ^^^ c) = true

instance (a b c : ℕ) : Decidable (CodeT a b c) := by
  unfold CodeT
  infer_instance

@[expose] def bridgeSteps : List (WStep ℕ) :=
  [.ins 1 94238, .ins 1 6144, .ins 3 18432, .ins 3 129055, .ins 3 6144, .ins 5 1249714,
    .ins 5 1050624, .ins 5 1966566, .ins 5 6175, .ins 5 6144, .ins 8 6144, .ins 8 4102144,
    .ins 8 1050655, .ins 8 6175, .ins 9 6144, .ins 11 1050624, .ins 11 6144, .ins 15 6175,
    .ins 15 1789952, .ins 16 12315, .ins 16 1050624, .ins 17 6144, .ins 20 747547,
    .ins 20 1056795, .ins 20 12315, .ins 21 6144, .ins 23 6144, .ins 25 1789952, .ins 25 6144,
    .ins 28 1789952, .ins 30 1789952, .ins 31 3367537, .ins 32 6144, .ins 34 6144,
    .ins 35 1789952, .ins 36 12315, .ins 36 1050624, .ins 37 6144, .ins 40 18432, .ins 40 6144,
    .ins 40 1789952, .ins 40 12315, .ins 41 1050624, .ins 41 6144, .ins 46 3367537, .ins 46 6144,
    .ins 48 1789952, .ins 49 6144, .bdel 0, .bdel 0, .bdel 0, .bdel 1, .bdel 0, .bdel 0, .bdel 7,
    .bdel 6, .bdel 6, .bdel 6, .bdel 7, .bdel 7, .bdel 9, .bdel 13, .bdel 12, .bdel 11, .bdel 10,
    .bdel 9, .bdel 9, .bdel 8, .bdel 7, .bdel 6, .bdel 6, .bins 5 10240, .bins 5 1800537,
    .bins 5 67584, .bins 5 346532, .bins 5 1789983, .bins 3 3367537, .bins 4 1789952,
    .bins 5 6144, .bins 6 6175, .bins 6 2979840, .bins 7 1345712, .bins 6 6175, .bins 3 526336,
    .bins 4 1050624, .bins 5 564459, .bins 5 3305503, .bins 5 6144, .bins 6 2811124,
    .bins 6 2809856, .bins 7 4116046, .bins 6 2811124, .bins 5 3305503, .bins 5 564459,
    .bins 3 3367537, .bins 4 1789952, .bins 5 6144, .bins 6 6175, .bins 6 18463, .bins 6 6175,
    .bins 0 1050655, .bins 0 6175, .bins 0 2979840, .bins 1 3240441, .bins 0 6175,
    .bins 0 1050655, .bins 0 1050624, .bins 1 2979871, .bins 1 2518106, .bins 1 10240, .del 80,
    .del 78, .del 76, .del 74, .del 72, .del 71, .del 70, .del 67, .del 67, .del 65, .del 65,
    .del 65, .del 65, .del 65, .del 64, .del 61, .del 59, .del 58, .del 58, .del 54, .del 54,
    .del 52, .del 52, .del 52, .del 52, .del 52, .del 49, .del 49, .del 47, .del 47, .del 47,
    .del 47, .del 47, .del 43, .del 41, .del 40, .del 40, .del 40, .del 38, .del 36, .del 35,
    .del 35, .del 34, .del 31, .del 31, .del 29, .del 29, .del 29, .del 29, .del 27, .del 25,
    .del 24, .del 24, .del 19, .del 19, .del 17, .del 15, .del 14, .del 14, .del 14, .del 14,
    .del 11, .del 11, .del 9, .del 9, .del 7, .del 6, .del 6, .del 6, .del 6, .del 6, .del 4,
    .del 4, .del 2, .del 2, .del 2, .del 2, .del 2, .bdel 2, .bdel 1, .bdel 0]

end CFSG.Monster.B.GSide
