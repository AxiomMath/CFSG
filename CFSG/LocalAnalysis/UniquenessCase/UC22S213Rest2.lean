module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Alt
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Spor
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3Closed (L : Subgroup G) : Prop :=
  ¬ 3 ∣ Nat.card (center (Bar2 L)) ∧
    ((∃ m, 6 ≤ m ∧ IsAlt (BarInf L) m) ∨ IsSpor (BarInf L) .M11 ∨ IsSpor (BarInf L) .M22 ∨
      IsSpor (BarInf L) .M23 ∨ IsSpor (BarInf L) .HS)

@[expose] def S21_3Rest2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ F08.Thin8 L →
    CFSG.Open.pRank 3 L ≤ 2 → (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem s21_3Rest_of_rest2 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
      s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    (hord : ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName),
      (s = .M11 ∨ s = .M22 ∨ s = .M23 ∨ s = .HS) → IsSpor X s → ¬ 27 ∣ Nat.card X)
    (Ch : Choice2011 G) (h : S21_3Rest2 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_3Rest (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL hthin h3 hk1 a ha hpr hN
  by_cases hC : S21_3Closed L
  · have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha
    have hNp := hN S.p S.hp
    obtain ⟨hZ, ⟨m, hm, hA⟩ | hX | hX | hX | hX⟩ := hC
    · exact uc22s213_not_centralizesBar_of_isAlt hS hU S hσ hPart hSE hOut hL hZ hm hA h3 hk1
        hodd hpr hNp
    all_goals
      first
      | exact uc22s213_not_centralizesBar_of_isSpor hS hU S hσ hPart hSE hOut hrank hout hord hL
          hZ (by decide) hX hk1 hodd hpr hNp
  · exact h hH c L hL hC hthin h3 hk1 a ha hpr hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
