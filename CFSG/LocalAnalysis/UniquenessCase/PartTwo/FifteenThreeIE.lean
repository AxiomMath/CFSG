module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Core

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

@[expose] def S15ThreeSigSubPiGap (D : Data G) : Prop :=
  DataExt D → UC6.R6_14 D → F07.R76Sig D → F08.R82 D →
    ∀ (V₀ V L K₀ : Subgroup G) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
      (hshape : s15Shape D V₀ V hV L K₀)
      (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
        (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
      (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
      (hrs : s15Rs D V₀ V hV L K₀ = 2) (hsig : D.sig ⊆ D.sig1)
      (hSg : UC6S846.SigmaStd D) (h3 : 3 ∉ D.sig)
      (hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
      (q : ℕ) (hq : q ∈ D.sig) (hqK : ¬ q ∣ Nat.card ↥(barSub V₀ V hV K₀)),
      ∃ R E : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R D.M ∧
        E ≤ R ⊓ centralizer (R : Set G) ∧ CFSG.Open.IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 ∧ 2 ≤ CFSG.Open.pRank q (D.M ⊓ centralizer (E : Set G))

theorem s15_Three_sig_sub_pi_core {D : Data G} {V₀ V L K₀ : Subgroup G}
    (hgap : S15ThreeSigSubPiGap D) (hx : DataExt D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h82 : F08.R82 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : s15Rs D V₀ V hV L K₀ = 2) (hsig : D.sig ⊆ D.sig1)
    (hSg : UC6S846.SigmaStd D) (h3 : 3 ∉ D.sig)
    (hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {q : ℕ} (hq : q ∈ D.sig) (hqK : ¬ q ∣ Nat.card ↥(barSub V₀ V hV K₀)) :
    ∃ R E : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R D.M ∧
      E ≤ R ⊓ centralizer (R : Set G) ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2 ∧ 2 ≤ CFSG.Open.pRank q (D.M ⊓ centralizer (E : Set G)) :=
  hgap hx h614 h76 h82 V₀ V L K₀ h hV hshape hperf hL2 hrs hsig hSg h3 hns q hq hqK

@[expose] def S15ThreeRankLeThreeGap (D : Data G) : Prop :=
  DataExt D → UC6.R6_14 D → F07.R76Sig D → F08.R82 D →
    ∀ (V₀ V L K₀ : Subgroup G) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
      (hshape : s15Shape D V₀ V hV L K₀)
      (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
        (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
      (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
      (hrs : s15Rs D V₀ V hV L K₀ = 2) (hsig : D.sig ⊆ D.sig1)
      (hSg : UC6S846.SigmaStd D) (h3 : 3 ∉ D.sig)
      (hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
      (q : ℕ) (hq : q ∈ D.sig) (h4 : 4 ≤ CFSG.Open.pRank q D.M),
      ∃ R E : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R D.M ∧
        E ≤ R ⊓ centralizer (R : Set G) ∧ CFSG.Open.IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 ∧ 2 < CFSG.Open.pRank q (D.M ⊓ normalizer (E : Set G))

theorem s15_Three_rank_le_three_core {D : Data G} {V₀ V L K₀ : Subgroup G}
    (hgap : S15ThreeRankLeThreeGap D) (hx : DataExt D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h82 : F08.R82 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hshape : s15Shape D V₀ V hV L K₀)
    (hperf : s15KNatPerf ↥(barSub V₀ V hV K₀) (barSub (v1Sub D.M V₀ V hV L) V hV K₀)
      (commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)))
    (hL2 : IsL3 ↥(barSub V₀ V hV K₀) 1 ∨ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5)
    (hrs : s15Rs D V₀ V hV L K₀ = 2) (hsig : D.sig ⊆ D.sig1)
    (hSg : UC6S846.SigmaStd D) (h3 : 3 ∉ D.sig)
    (hns : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {q : ℕ} (hq : q ∈ D.sig) (h4 : 4 ≤ CFSG.Open.pRank q D.M) (h77 : F07.R77E2 D) :
    ∃ R E : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R D.M ∧
      E ≤ R ⊓ centralizer (R : Set G) ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2 ∧ rankThreeGamma 1 3 E ≤ D.M := by
  obtain ⟨R, E, hRsyl, hEZ, hEel, hEcard, h2rank⟩ :=
    hgap hx h614 h76 h82 V₀ V L K₀ h hV hshape hperf hL2 hrs hsig hSg h3 hns q hq h4
  obtain ⟨-, hq2⟩ := D.sig_prime q hq
  have hRM : R ≤ D.M := by
    obtain ⟨Q, hQ⟩ := hRsyl
    rw [← hQ]
    exact Subgroup.map_subtype_le (H := D.M) Q
  have hEM : E ≤ D.M := (hEZ.trans inf_le_left).trans hRM
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M := hSg.sig1_sp q (hsig hq)
  exact ⟨R, E, hRsyl, hEZ, hEel, hEcard,
    h77 hsig q hq hq2 hsp 3 Nat.prime_three (by norm_num) h3 E hEM hEel hEcard h2rank⟩

end Core

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
