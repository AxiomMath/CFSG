module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

@[expose] def IsTypeEps (X : Type) [Group X] : Prop :=
  ∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧
    ((p ^ f % 3 = 2 ∧ Nonempty (X ≃* projSL 3 (GaloisField p f))) ∨
      (p ^ f % 3 = 1 ∧ 2 < p ^ f ∧ Nonempty (X ≃* projSU 3 p f)))

structure CfgSEps (S : Type) [Group S] [Finite S] (A : Subgroup (MulAut S)) (σ : MulAut S)
    (K : Subgroup S) : Prop where
  isE27 : Late.IsE27 A
  mem : σ ∈ A
  ne_one : σ ≠ 1
  le_autFix : K ≤ autFix σ
  isSubnormal : (K.subgroupOf (autFix σ)).IsSubnormal
  isPerfect : Group.IsPerfect K
  map_mem : ∀ a ∈ A, ∀ k ∈ K, (a : MulAut S) k ∈ K
  isType : IsTypeEps (K ⧸ CFSG.pCore 2 K)
  faithful : ∀ a ∈ A, (∀ k ∈ K, (a : MulAut S) k * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) →
    a ∈ Subgroup.zpowers σ

@[expose] def NoCfgSEps (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (A : Subgroup (MulAut S)) (σ : MulAut S) (K : Subgroup S), ¬ CfgSEps S A σ K

theorem noCfgSEps_of_autNoE27 {S : Type} [Group S] [Finite S] (h : AutNoE27 S) : NoCfgSEps S :=
  fun A _ _ hc => h A hc.isE27

@[expose] def RowSEpsOf (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → NoCfgSEps S

structure KEpsRowsS : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e → RowSEpsOf (projSL 2 (GaloisField p e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowSEpsOf (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowSEpsOf (projSU 3 p e)
  three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSEpsOf (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSEpsOf (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSEpsOf (projSU 4 p 1)
  five : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowSEpsOf (alternatingGroup (Fin n))
  six : ∀ s ∈ sporadics42, RowSEpsOf (Spor s)
  seven_SL2 : ∀ n : ℕ, 1 ≤ n → RowSEpsOf (projSL 2 (GaloisField 2 n))
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowSEpsOf (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowSEpsOf (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowSEpsOf (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowSEpsOf (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowSEpsOf (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group
  eight_SL5 : RowSEpsOf (projSL 5 (GaloisField 2 1))
  eight_SU5 : RowSEpsOf (projSU 5 2 1)
  eight_SL6 : RowSEpsOf (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowSEpsOf (projSU 6 2 1)
  eight_SL7 : RowSEpsOf (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowSEpsOf (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowSEpsOf (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowSEpsOf (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowSEpsOf (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowSEpsOf (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowSEpsOf (projSp 3 (GaloisField 2 2))
  eight_SU5_4 : RowSEpsOf (projSU 5 2 2)
  eight_SU5_8 : RowSEpsOf (projSU 5 2 3)
  eight_F4 : RowSEpsOf (TauCeti.CFSGIndex.lie f4TwoIndex).Group
  nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSEpsOf (projSL 3 (GaloisField 3 e))
  nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSEpsOf (projSU 3 3 e)
  nine_G2 : RowSEpsOf (TauCeti.CFSGIndex.lie g2ThreeIndex).Group
  nine_SL4 : RowSEpsOf (projSL 4 (GaloisField 3 1))
  nine_SU4 : RowSEpsOf (projSU 4 3 1)

namespace KEpsRowsS

variable {S : Type} [Group S] [Finite S]

theorem noCfg_of_list42 (R : KEpsRowsS) (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : Census.List42 S) : NoCfgSEps S := by
  rcases h with ⟨p, e, hp, h2, he, hf⟩ | ⟨p, e, hp, h3, he, he2, hf | hf⟩ | ⟨hr, hf⟩ |
    ⟨p, hp, h3, ⟨q, hqp, hqe, hq, hf⟩ | hf | hf | hf⟩ | ⟨n, hn5, hn12, hf⟩ |
    ⟨s, hsp, hf⟩ | h7 | h8 | h9
  · exact R.one p e h2 he S hs hna hf
  · exact R.two_SL p e h3 he he2 S hs hna hf
  · exact R.two_SU p e h3 he he2 S hs hna hf
  · exact R.three hr S hs hna hf
  · exact R.four_G2 p h3 q hqp hqe hq S hs hna hf
  · exact R.four_Sp p h3 S hs hna hf
  · exact R.four_SL p h3 S hs hna hf
  · exact R.four_SU p h3 S hs hna hf
  · exact R.five n hn5 hn12 S hs hna hf
  · exact R.six s hsp S hs hna hf
  · rcases h7 with ⟨n, hn, hf | hf | hf | hf | hf⟩ | ⟨q, hq2, hq, hf⟩ |
      ⟨q, hq, hq2, hf⟩ | ⟨m, hm, hf⟩ | ⟨m, hm, hf⟩ | ⟨ht, hf⟩
    · exact R.seven_SL2 n hn S hs hna hf
    · exact R.seven_SL3 n hn S hs hna hf
    · exact R.seven_SU3 n hn S hs hna hf
    · exact R.seven_Sp4 n hn S hs hna hf
    · exact R.seven_SU4 n hn S hs hna hf
    · exact R.seven_G2 q hq2 hq S hs hna hf
    · exact R.seven_D4 q hq hq2 S hs hna hf
    · exact R.seven_Sz m hm S hs hna hf
    · exact R.seven_F4 m hm S hs hna hf
    · exact R.seven_Tits ht S hs hna hf
  · rcases h8 with hf | hf | hf | hf | hf | hf | hf | hf | ⟨b, c, hbc, hf⟩ | hf |
      hf | hf | hf | hf
    · exact R.eight_SL5 S hs hna hf
    · exact R.eight_SU5 S hs hna hf
    · exact R.eight_SL6 S hs hna hf
    · exact R.eight_SU6 S hs hna hf
    · exact R.eight_SL7 S hs hna hf
    · exact R.eight_Sp6 S hs hna hf
    · exact R.eight_Sp8 S hs hna hf
    · exact R.eight_OmegaPlus S hs hna hf
    · exact R.eight_OmegaMinus b c hbc S hs hna hf
    · exact R.eight_SL4 S hs hna hf
    · exact R.eight_Sp6_4 S hs hna hf
    · exact R.eight_SU5_4 S hs hna hf
    · exact R.eight_SU5_8 S hs hna hf
    · exact R.eight_F4 S hs hna hf
  · rcases h9 with ⟨e, he, he3, hf | hf⟩ | hf | hf | hf
    · exact R.nine_SL3 e he he3 S hs hna hf
    · exact R.nine_SU3 e he he3 S hs hna hf
    · exact R.nine_G2 S hs hna hf
    · exact R.nine_SL4 S hs hna hf
    · exact R.nine_SU4 S hs hna hf

end KEpsRowsS

end CFSG.RankThree.PartTwo.Sec4.RonanEps
