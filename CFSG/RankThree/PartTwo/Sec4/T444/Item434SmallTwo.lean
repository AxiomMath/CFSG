module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434L34Seitz
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
import CFSG.RankThree.PartTwo.Sec4.T444.Item434Alt
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.Adapters.LinearSmallCatalog
import CFSG.Adapters.LinearFieldTransport
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.LieType.SteinbergBRAutGL32
import CFSG.RankThree.Asc83Table.E27
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Extremal
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

@[expose] def IsSmallTwoOmegaMinus (X : Type) [Group X] : Prop :=
  ∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
    Nonempty (X ≃* projOmegaMinus 3 (GaloisField 2 1) b c)

@[expose] def IsSmallTwoCaseIII (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 3)) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ IsoGTwo X q) ∨
    (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
      q.exponent = 1 ∧ Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group))

@[expose] def IsSmallTwoCaseIV (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSp 4 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSU 5 2 1) ∨
    Nonempty (X ≃* projSU 6 2 1) ∨ Nonempty (X ≃* projOmegaPlus 4 (GaloisField 2 1)) ∨
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group) ∨
    Nonempty (X ≃* projSU 4 2 3) ∨ Nonempty (X ≃* projSU 5 2 3)

@[expose] def IsSmallTwoOther (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, (n = 3 ∨ n = 6) ∧ Nonempty (X ≃* projSL 2 (GaloisField 2 n))) ∨
  (∃ n : ℕ, (n = 3 ∨ n = 6) ∧ Nonempty (X ≃* projSL 3 (GaloisField 2 n))) ∨
  (∃ n : ℕ, (n = 2 ∨ n = 3 ∨ n = 6) ∧ Nonempty (X ≃* projSU 3 2 n)) ∨
  (∃ n : ℕ, (n = 1 ∨ n = 2 ∨ n = 6) ∧ Nonempty (X ≃* projSp 2 (GaloisField 2 n))) ∨
  (∃ n : ℕ, (n = 1 ∨ n = 2 ∨ n = 6) ∧ Nonempty (X ≃* projSU 4 2 n)) ∨
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent ≠ 3 ∧ (q.exponent ≤ 3 ∨ q.exponent = 6) ∧
    IsoGTwo X q) ∨
  (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    q.exponent ≠ 1 ∧ (q.exponent ≤ 3 ∨ q.exponent = 6) ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
  (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid), m ≤ 1 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group)) ∨
  (∃ ht : TauCeti.LieTypeIndex.tits.Valid,
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group)) ∨
  (Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSL 6 (GaloisField 2 1)) ∨
    Nonempty (X ≃* projSL 7 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSL 4 (GaloisField 2 2)) ∨
    Nonempty (X ≃* projSp 3 (GaloisField 2 2)) ∨ Nonempty (X ≃* projSU 5 2 2))

@[expose] def IsSmallTwoSuzuki (X : Type) [Group X] : Prop :=
  ∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid), m ≤ 1 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)

section Constructors

variable {X : Type} [Group X]

theorem IsSmallTwoCaseIII.sp62 (h : Nonempty (X ≃* projSp 3 (GaloisField 2 1))) :
    IsSmallTwoCaseIII X := Or.inl h

theorem IsSmallTwoCaseIII.sp48 (h : Nonempty (X ≃* projSp 2 (GaloisField 2 3))) :
    IsSmallTwoCaseIII X := Or.inr <| Or.inl h

theorem IsSmallTwoCaseIII.g28 {q : TauCeti.PrimePower} (h2 : q.p = 2) (h3 : q.exponent = 3)
    (h : IsoGTwo X q) : IsSmallTwoCaseIII X := Or.inr <| Or.inr <| Or.inl ⟨q, h2, h3, h⟩

theorem IsSmallTwoCaseIII.d42 {q : TauCeti.PrimePower}
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (h2 : q.p = 2) (h1 : q.exponent = 1)
    (h : Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) :
    IsSmallTwoCaseIII X := Or.inr <| Or.inr <| Or.inr ⟨q, hq, h2, h1, h⟩

theorem IsSmallTwoCaseIV.sp82 (h : Nonempty (X ≃* projSp 4 (GaloisField 2 1))) :
    IsSmallTwoCaseIV X := Or.inl h

theorem IsSmallTwoCaseIV.u52 (h : Nonempty (X ≃* projSU 5 2 1)) : IsSmallTwoCaseIV X :=
  Or.inr <| Or.inl h

theorem IsSmallTwoCaseIV.u62 (h : Nonempty (X ≃* projSU 6 2 1)) : IsSmallTwoCaseIV X :=
  Or.inr <| Or.inr <| Or.inl h

theorem IsSmallTwoCaseIV.o8p (h : Nonempty (X ≃* projOmegaPlus 4 (GaloisField 2 1))) :
    IsSmallTwoCaseIV X := Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem IsSmallTwoCaseIV.f42 (h : Nonempty (X ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group)) :
    IsSmallTwoCaseIV X := Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem IsSmallTwoCaseIV.u48 (h : Nonempty (X ≃* projSU 4 2 3)) : IsSmallTwoCaseIV X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem IsSmallTwoCaseIV.u58 (h : Nonempty (X ≃* projSU 5 2 3)) : IsSmallTwoCaseIV X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h

theorem IsSmallTwoOther.l2 {n : ℕ} (hn : n = 3 ∨ n = 6)
    (h : Nonempty (X ≃* projSL 2 (GaloisField 2 n))) : IsSmallTwoOther X :=
  Or.inl ⟨n, hn, h⟩

theorem IsSmallTwoOther.l3 {n : ℕ} (hn : n = 3 ∨ n = 6)
    (h : Nonempty (X ≃* projSL 3 (GaloisField 2 n))) : IsSmallTwoOther X :=
  Or.inr <| Or.inl ⟨n, hn, h⟩

theorem IsSmallTwoOther.u3 {n : ℕ} (hn : n = 2 ∨ n = 3 ∨ n = 6)
    (h : Nonempty (X ≃* projSU 3 2 n)) : IsSmallTwoOther X :=
  Or.inr <| Or.inr <| Or.inl ⟨n, hn, h⟩

theorem IsSmallTwoOther.sp4 {n : ℕ} (hn : n = 1 ∨ n = 2 ∨ n = 6)
    (h : Nonempty (X ≃* projSp 2 (GaloisField 2 n))) : IsSmallTwoOther X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, hn, h⟩

theorem IsSmallTwoOther.u4 {n : ℕ} (hn : n = 1 ∨ n = 2 ∨ n = 6)
    (h : Nonempty (X ≃* projSU 4 2 n)) : IsSmallTwoOther X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨n, hn, h⟩

theorem IsSmallTwoOther.g2 {q : TauCeti.PrimePower} (h2 : q.p = 2) (h3 : q.exponent ≠ 3)
    (hq : q.exponent ≤ 3 ∨ q.exponent = 6) (h : IsoGTwo X q) : IsSmallTwoOther X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨q, h2, h3, hq, h⟩

theorem IsSmallTwoOther.d4 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (h2 : q.p = 2) (h1 : q.exponent ≠ 1)
    (hq : q.exponent ≤ 3 ∨ q.exponent = 6)
    (h : Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group)) :
    IsSmallTwoOther X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨q, hv, h2, h1, hq, h⟩

theorem IsSmallTwoOther.f4 {m : ℕ} (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid) (hm1 : m ≤ 1)
    (h : Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group)) : IsSmallTwoOther X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨m, hm, hm1, h⟩

theorem IsSmallTwoOther.tits (ht : TauCeti.LieTypeIndex.tits.Valid)
    (h : Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group)) : IsSmallTwoOther X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨ht, h⟩

theorem IsSmallTwoOther.eight
    (h : Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSL 6 (GaloisField 2 1)) ∨
      Nonempty (X ≃* projSL 7 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSL 4 (GaloisField 2 2)) ∨
      Nonempty (X ≃* projSp 3 (GaloisField 2 2)) ∨ Nonempty (X ≃* projSU 5 2 2)) :
    IsSmallTwoOther X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h

end Constructors

theorem isLie42SmallTwo_cases {X : Type} [Group X] (h : IsLie42SmallTwo X) :
    IsL34 X ∨ IsSmallTwoOmegaMinus X ∨ IsSmallTwoCaseIII X ∨ IsSmallTwoCaseIV X ∨
      IsSmallTwoOther X ∨ IsSmallTwoSuzuki X ∨ Nonempty (X ≃* projSL 2 (GaloisField 2 1)) ∨
      Nonempty (X ≃* projSU 3 2 1) ∨ Nonempty (X ≃* projSL 2 (GaloisField 2 2)) ∨
      Nonempty (X ≃* projSL 3 (GaloisField 2 1)) := by
  rcases h with
    (⟨n, hn1, hn, hL2 | hL3 | hU3 | hSp4 | hU4⟩ | ⟨q, hq2, hq, hG2⟩ | ⟨q, hv, hq2, hq, hD4⟩ |
      ⟨m, hm, hm1, hSz⟩ | ⟨m, hm, hm1, hF4⟩ | ⟨ht, hT⟩) |
    (h52 | h52u | h62 | h62u | h72 | h62s | h82 | h8p | h8m | h44 | h64 | h54 | h58 | hF42)
  ·
    rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 by omega) with rfl | rfl | hn' | hn'
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hL2
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inl hL2
    all_goals exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      IsSmallTwoOther.l2 (by omega) hL2
  ·
    rcases (show n = 2 ∨ n = 1 ∨ n = 3 ∨ n = 6 by omega) with rfl | rfl | hn' | hn'
    · exact Or.inl hL3
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr hL3
    all_goals exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      IsSmallTwoOther.l3 (by omega) hL3
  ·
    rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 by omega) with rfl | hn' | hn' | hn'
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hU3
    all_goals exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      IsSmallTwoOther.u3 (by omega) hU3
  ·
    rcases (show n = 3 ∨ n = 1 ∨ n = 2 ∨ n = 6 by omega) with rfl | hn' | hn' | hn'
    · exact Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIII.sp48 hSp4
    all_goals exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      IsSmallTwoOther.sp4 (by omega) hSp4
  ·
    rcases (show n = 3 ∨ n = 1 ∨ n = 2 ∨ n = 6 by omega) with rfl | hn' | hn' | hn'
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIV.u48 hU4
    all_goals exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      IsSmallTwoOther.u4 (by omega) hU4
  ·
    by_cases h3 : q.exponent = 3
    · exact Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIII.g28 hq2 h3 hG2
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoOther.g2 hq2 h3 hq hG2
  ·
    by_cases h1 : q.exponent = 1
    · exact Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIII.d42 hv hq2 h1 hD4
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoOther.d4 hv hq2 h1 hq hD4
  ·
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨m, hm, hm1, hSz⟩
  ·
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoOther.f4 hm hm1 hF4
  ·
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoOther.tits ht hT
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoOther.eight (Or.inl h52)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIV.u52 h52u
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoOther.eight <|
      Or.inr <| Or.inl h62
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIV.u62 h62u
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoOther.eight <|
      Or.inr <| Or.inr <| Or.inl h72
  · exact Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIII.sp62 h62s
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIV.sp82 h82
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIV.o8p h8p
  · exact Or.inr <| Or.inl h8m
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoOther.eight <|
      Or.inr <| Or.inr <| Or.inr <| Or.inl h44
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoOther.eight <|
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h64
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoOther.eight <|
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h54
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIV.u58 h58
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| IsSmallTwoCaseIV.f42 hF42

theorem false_of_isQuasisimple_of_isSolvable_quotient {X : Type} [Group X] (hq : IsQuasisimple X)
    (hs : Group.IsSolvable (X ⧸ Subgroup.center X)) : False := by
  have : Group.IsPerfect X := hq.1
  have : Group.IsPerfect (X ⧸ Subgroup.center X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  have : Nontrivial (X ⧸ Subgroup.center X) := IsSimpleGroup.toNontrivial
  exact Group.IsPerfect.not_isSolvable (X ⧸ Subgroup.center X) hs

theorem false_of_isQuasisimple_of_projSL_two_two {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (e : X ⧸ Subgroup.center X ≃* projSL 2 (GaloisField 2 1)) : False := by
  have hcard : Nat.card (X ⧸ Subgroup.center X) = 6 := by
    rw [Nat.card_congr e.toEquiv, Sec19.Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  exact false_of_isQuasisimple_of_isSolvable_quotient hq
    (CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcard]; norm_num))

theorem false_of_isQuasisimple_of_projSU_three_two {X : Type} [Group X] (hq : IsQuasisimple X)
    (e : X ⧸ Subgroup.center X ≃* projSU 3 2 1) : False := by
  have := Sec13.isSolvable_projSU_two
  exact false_of_isQuasisimple_of_isSolvable_quotient hq
    (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

theorem pRank_three_mulAut_projSL_two_four_le_one :
    CFSG.pRank 3 (MulAut (projSL 2 (GaloisField 2 2))) ≤ 1 := by
  obtain ⟨e⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl KFacts.L34.card_galoisField_two_two)
  let ψ : projSL 2 (GaloisField 2 2) ≃* alternatingGroup (Fin 5) :=
    (KFacts.L34.projSLEquivProjectiveSL 2 _).trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        2 _).symm.trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _).trans e))
  rw [CFSG.RankThree.Asc83Table.pRank_congr (MulAut.congr ψ)]
  exact pRank_three_mulAut_alternatingGroup_five_le_one

theorem pRank_three_mulAut_projSL_three_two_le_one :
    CFSG.pRank 3 (MulAut (projSL 3 (GaloisField 2 1))) ≤ 1 := by
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod 2) = Fintype.card (GaloisField 2 1) := by
    rw [ZMod.card, Fintype.card_eq_nat_card, GaloisField.card 2 1 one_ne_zero, pow_one]
  let φ : ZMod 2 ≃+* GaloisField 2 1 := FiniteField.ringEquivOfCardEq hcard
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  let ψ : projSL 3 (GaloisField 2 1) ≃* GL (Fin 3) (ZMod 2) :=
    (KFacts.L34.projSLEquivProjectiveSL 3 _).trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 _).symm.trans
      ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 3)).symm.trans
        (e₂.trans e₃)))
  rw [CFSG.RankThree.Asc83Table.pRank_congr (MulAut.congr ψ)]
  refine csSup_le' ?_
  rintro r ⟨B, -, hB⟩
  have hdvd : 3 ^ r ∣ 336 := by
    rw [← hB, ← CFSG.LieType.SteinbergBR.AutGL32.card_mulAut_GL32]
    exact Subgroup.card_subgroup_dvd_card B
  by_contra hr
  have h9 : 3 ^ 2 ∣ 3 ^ r := Nat.pow_dvd_pow 3 (by omega)
  have := h9.trans hdvd
  norm_num at this

section Families


@[expose] def Item434OmegaMinusEight : Prop :=
  Item434SecFor IsSmallTwoOmegaMinus

@[expose] def Item434SmallTwoIII : Prop :=
  Item434SecFor IsSmallTwoCaseIII

@[expose] def Item434SmallTwoIV : Prop :=
  Item434SecFor IsSmallTwoCaseIV

@[expose] def Item434SmallTwoOther : Prop :=
  Item434SecFor IsSmallTwoOther

theorem item434SmallTwo_of (hII : Item434OmegaMinusEight) (hIII : Item434SmallTwoIII)
    (hIV : Item434SmallTwoIV) (hO : Item434SmallTwoOther) : Item434SmallTwo := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  rcases isLie42SmallTwo_cases hL with h | h | h | h | h | h | h | h | h | h
  · exact item434SecFor_isL34' G₀ hG₀ H G f hf hker A M Q hc h
  · exact hII G₀ hG₀ H G f hf hker A M Q hc h
  · exact hIII G₀ hG₀ H G f hf hker A M Q hc h
  · exact hIV G₀ hG₀ H G f hf hker A M Q hc h
  · exact hO G₀ hG₀ H G f hf hker A M Q hc h
  · obtain ⟨m, hm, -, ⟨e⟩⟩ := h
    exact (hc.false_of_pRank_mulAut_le_one e (KFacts.KP7.pRank_three_mulAut_le_one
      (Census.suzukiModel_of_index m hm))).elim
  · obtain ⟨e⟩ := h
    exact (false_of_isQuasisimple_of_projSL_two_two hc.isQuasisimple e).elim
  · obtain ⟨e⟩ := h
    exact (false_of_isQuasisimple_of_projSU_three_two hc.isQuasisimple e).elim
  · obtain ⟨e⟩ := h
    exact (hc.false_of_pRank_mulAut_le_one e pRank_three_mulAut_projSL_two_four_le_one).elim
  · obtain ⟨e⟩ := h
    exact (hc.false_of_pRank_mulAut_le_one e pRank_three_mulAut_projSL_three_two_le_one).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
