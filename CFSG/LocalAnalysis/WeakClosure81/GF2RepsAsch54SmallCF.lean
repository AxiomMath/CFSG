module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.GH74.Defs

import CFSG.GH74.SectionalRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Alm
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Sect
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.Form2
import CFSG.CGT.Timmesfeld75.Main
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.GroupTheory.SubgroupCardMul
import CFSG.Holt.General.Basic
import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.Sol78Family
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
import CFSG.LocalAnalysis.WeakClosure81.EightNine
import CFSG.LocalAnalysis.WeakClosure81.SevenNine
import CFSG.LocalAnalysis.WeakClosure81.ThirteenFour
import CFSG.LocalAnalysis.WeakClosure81.W18PackFix
import CFSG.LocalAnalysis.WeakClosure81.W18PackRank
import CFSG.LocalAnalysis.WeakClosure81.W19Conf
import CFSG.LocalAnalysis.WeakClosure81.W19Hyp197
import CFSG.LocalAnalysis.WeakClosure81.W19Min
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.B3Facts
import CFSG.Quasithin.Background.B3FourConj
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.C4Statement
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E2TwoLieQuotLift
import CFSG.Quasithin.Background.E2TwoProofDefs
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.E4Solv
import CFSG.Quasithin.Background.F9Sixteen
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.H16TwoM22
import CFSG.Quasithin.Background.HMathieuO2Data
import CFSG.Quasithin.Background.HSecQuot
import CFSG.Quasithin.Background.HTriSolv
import CFSG.Quasithin.Background.HTriU3
import CFSG.Quasithin.Background.SmithB42L2L32
import CFSG.Quasithin.Background.SmithB42L2Nat
import CFSG.Quasithin.Background.SmithB42SL3Key
import CFSG.Quasithin.Background.SmithB45SL3Label
import CFSG.Quasithin.Background.SmithB45SL3Outer
import CFSG.Quasithin.Background.SmithB51LnRealB
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S14117
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.EmptyFaithful.T1515Der
import CFSG.Quasithin.Vol2.Ch10SecA1011B
import CFSG.Quasithin.Vol2.Ch10SecANat3
import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
import CFSG.Quasithin.Vol2.Ch11SecBTCIso
import CFSG.Quasithin.Vol2.Ch11StatementsE
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4
import CFSG.Quasithin.Vol2.Ch12Sec2Statements
import CFSG.Quasithin.Vol2.Ch7NotFFS7
import CFSG.Quasithin.Vol2.Ch8Sec2L825O
import CFSG.Quasithin.Vol2.Ch8Sec2L829LM1
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.Schreier.J4SCommGenBase1
import CFSG.Timmesfeld.Bridge.RootSetsSolv
import Certificates.Kernel.J4Count.Cent11Base
import Certificates.Kernel.J4Count.Fix5
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {P : ∀ (X : Type) [Group X], Prop}

theorem not_isCompositionFactor_of_normal {X : Type} [Group X] (A : Subgroup X) [A.Normal]
    (hA : ∀ (L : Type) [Group L], E1.IsCompositionFactor ↥A L → ¬ P L)
    (hQ : ∀ (L : Type) [Group L], E1.IsCompositionFactor (X ⧸ A) L → ¬ P L)
    (L : Type) [Group L] (h : E1.IsCompositionFactor X L) : ¬ P L :=
  (isCompositionFactor_of_normal A h).elim (hA L) (hQ L)

theorem not_isCompositionFactor_of_isSolvable
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    {X : Type} [Group X] [Finite X] (hX : Group.IsSolvable X)
    (L : Type) [Group L] (h : E1.IsCompositionFactor X L) : ¬ P L := fun hL => by
  have : Finite L := isCompositionFactor_finite h
  obtain ⟨a, b, hab⟩ := hP L hL
  exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor hX h a b)

theorem not_isCompositionFactor_of_sectionalTwoRankLE
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    {X : Type} [Group X] [Finite X] (hX : CFSG.GH74.SectionalTwoRankLE X 2)
    (L : Type) [Group L] (h : E1.IsCompositionFactor X L) : ¬ P L := fun hL => by
  have : Finite L := isCompositionFactor_finite h
  obtain ⟨N, M, hNM, -, -, -, -, ⟨e⟩⟩ := h
  have := hNM
  exact hP L hL
    (CFSG.GH74.SectionalTwoRankLE.of_mulEquiv e (sectionalTwoRankLE_section hX M (N.subgroupOf M)))

theorem not_isCompositionFactor_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : ∀ (L : Type) [Group L], E1.IsCompositionFactor X L → ¬ P L)
    (L : Type) [Group L] (hc : E1.IsCompositionFactor X' L) : ¬ P L :=
  h L ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).2 hc)

theorem sectionalTwoRankLE_of_odd {X : Type} [Group X] [Finite X] (h : Odd (Nat.card X))
    (r : ℕ) : CFSG.GH74.SectionalTwoRankLE X r := by
  intro S hS
  refine ⟨∅, by simp, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hdvd : 2 ^ n ∣ Nat.card X := hn ▸ Subgroup.card_subgroup_dvd_card S
  have hn0 : n = 0 := by
    by_contra hn0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact (Nat.not_even_iff_odd.2 h) (even_iff_two_dvd.2 ((dvd_pow_self 2 (by omega)).trans hdvd))
  rw [hn0, pow_zero] at hn
  rw [Finset.coe_empty, Subgroup.closure_empty, eq_comm]
  exact Subgroup.eq_bot_of_card_eq S hn

theorem not_isCompositionFactor_of_isPGroup_normal
    (hP : ∀ (L : Type) [Group L] [Finite L], P L →
      (∃ a b : L, a * b ≠ b * a) ∧ ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    {X : Type} [Group X] [Finite X] (S : Subgroup X) [S.Normal] (hS : IsPGroup 2 S)
    (hi : ¬ 2 ∣ S.index) (L : Type) [Group L] (h : E1.IsCompositionFactor X L) : ¬ P L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine not_isCompositionFactor_of_normal S ?_ ?_ L h
  · have := hS.isNilpotent
    exact not_isCompositionFactor_of_isSolvable (fun L _ _ hL => (hP L hL).1) inferInstance
  · refine not_isCompositionFactor_of_sectionalTwoRankLE (fun L _ _ hL => (hP L hL).2)
      (sectionalTwoRankLE_of_odd ?_ 2)
    rw [← Subgroup.index_eq_card, Nat.odd_iff]
    omega

theorem not_hasCompFactor_of_subgroupOf
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q} [E.Normal] (hq : Group.IsSolvable (Q ⧸ E))
    (X : Subgroup Q)
    (h : ∀ (L : Type) [Group L], E1.IsCompositionFactor ↥(E.subgroupOf X) L → ¬ P L) :
    ¬ HasCompFactor X P := by
  rintro ⟨L, _, hc, hL⟩
  have : Finite L := isCompositionFactor_finite hc
  exact h L (isCompositionFactor_subgroupOf_of_isSolvable_quot hq hc (hP L hL)) hL

theorem not_hasCompFactor_of_isSolvable
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    {Q : Type} [Group Q] [Finite Q] {X : Subgroup Q} (hX : Group.IsSolvable ↥X) :
    ¬ HasCompFactor X P := by
  rintro ⟨L, _, hc, hL⟩
  exact not_isCompositionFactor_of_isSolvable hP hX L hc hL

theorem not_hasCompFactor_normalizer_inf
    (hP : ∀ (L : Type) [Group L] [Finite L], P L →
      (∃ a b : L, a * b ≠ b * a) ∧ ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    {Q : Type} [Group Q] [Finite Q] {E T : Subgroup Q} [E.Normal] (hq : Group.IsSolvable (Q ⧸ E))
    (hT : IsSylowIn 2 (T ⊓ E) E) :
    ¬ HasCompFactor (Subgroup.normalizer ((T ⊓ E : Subgroup Q) : Set Q)) P := by
  set N := Subgroup.normalizer ((T ⊓ E : Subgroup Q) : Set Q)
  refine not_hasCompFactor_of_subgroupOf (fun L _ _ hL => (hP L hL).1) hq N ?_
  have hle : T ⊓ E ≤ E ⊓ N := le_inf inf_le_right Subgroup.le_normalizer
  have : ((T ⊓ E).subgroupOf (E ⊓ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 inf_le_right
  refine not_isCompositionFactor_of_mulEquiv
    ((MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right E N).symm).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_right)).symm
    (not_isCompositionFactor_of_isPGroup_normal hP ((T ⊓ E).subgroupOf (E ⊓ N))
      (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm) fun h2 => hT.2.2 ?_)
  rw [← Subgroup.relIndex_mul_relIndex (T ⊓ E) (E ⊓ N) E hle inf_le_left]
  exact dvd_mul_of_dvd_left h2 _

end CFSG.LocalAnalysis.WeakClosure81

end
