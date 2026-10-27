module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


structure HessData {P : Type} [Group P] [Finite P] (Yh Bh : Subgroup P) (xh bh ch : P) : Prop where
  normal : Yh.Normal
  elem : CFSG.Assembly.IsElemAbelian 3 Bh
  card : Nat.card Bh = 27
  gen : Bh = Subgroup.zpowers xh ⊔ Subgroup.zpowers bh ⊔ Subgroup.zpowers ch
  xcent : ∀ p : P, xh * p = p * xh
  cent : Bh ⊓ Subgroup.centralizer (Yh : Set P) = Subgroup.zpowers xh
  cY : ch ∈ Yh
  comp : ∃ Xh : Subgroup P, Xh ≤ Yh ∧ Xh ≤ Subgroup.centralizer ({bh} : Set P) ∧
    Group.IsPerfect Xh ∧
    (Xh.subgroupOf (Yh ⊓ Subgroup.centralizer ({bh} : Set P))).IsSubnormal ∧ ch ∈ Xh ∧
    ∃ (p n : ℕ) (_ : Fact p.Prime), 4 ≤ p ^ n ∧
      ∃ φ : Xh →* projSL 2 (GaloisField p n), Function.Surjective φ
  inner : ∀ β ∈ Bh, ¬ KFacts.InducesStdKind Yh β .field ∧ ¬ KFacts.InducesStdKind Yh β .graphField

@[expose] def HessConcl {P : Type} [Group P] (Yh Bh : Subgroup P) (bh ch : P) : Prop :=
  ∃ Fh : Subgroup P, Fh ≤ Yh ∧ CFSG.Assembly.IsElemAbelian 3 Fh ∧ Nat.card Fh = 9 ∧ ch ∈ Fh ∧
    Bh ≤ Subgroup.normalizer (Fh : Set P) ∧ Fh ⊓ Bh = Subgroup.zpowers ch ∧
    (∀ f ∈ Fh, bh * f * bh⁻¹ * f⁻¹ ∈ Subgroup.zpowers ch) ∧
    (∃ f ∈ Fh, bh * f * bh⁻¹ * f⁻¹ ≠ 1) ∧
    (∀ f ∈ Fh, f ≠ 1 → ∃ n ∈ Yh ⊓ Subgroup.normalizer (Fh : Set P), n * ch * n⁻¹ = f) ∧
    Nonempty (Sec4.autIn (Yh ⊔ Bh) Fh ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

@[expose] def Gap129HessL3 : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (Yh Bh : Subgroup P) (xh bh ch : P),
    HessData Yh Bh xh bh ch → (∃ (p e : ℕ) (_ : Fact p.Prime), Sec4.IsoLThreePi ↥Yh p e) →
    HessConcl Yh Bh bh ch

@[expose] def Gap129HessD4 : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (Yh Bh : Subgroup P) (xh bh ch : P),
    HessData Yh Bh xh bh ch →
    (∃ (r : TauCeti.PrimePower) (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid), r.p = 2 ∧
      Nonempty (↥Yh ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group)) →
    HessConcl Yh Bh bh ch

end CFSG.RankThree.PartTwo.Sec12
