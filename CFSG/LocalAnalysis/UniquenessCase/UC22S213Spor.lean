module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22S216Spor
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_not_centralizesBar_of_isSpor (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
      s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    (hord : ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName),
      (s = .M11 ∨ s = .M22 ∨ s = .M23 ∨ s = .HS) → IsSpor X s → ¬ 27 ∣ Nat.card X)
    {L : Subgroup G} (hL : L ∈ calC S.M) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)))
    {s : TauCeti.SporadicName} (hs : s = .M11 ∨ s = .M22 ∨ s = .M23 ∨ s = .HS)
    (hX : IsSpor (BarInf L) s) (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1)
    {a : G} (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (hN : CFSG.Open.pRank S.p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  haveI := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have hsJ : s ≠ .J1 := by rcases hs with rfl | rfl | rfl | rfl <;> decide
  exact uc22s213_not_centralizesBar_of_inner hS hU S hσ hPart hSE hOut hL hZ
    (fun σ hσ' => uc22s216_mem_range_conj_of_isSpor hout hL hX hσ') (hord (BarInf L) s hs hX)
    (hrank (BarInf L) s hsJ hX) hk1 hodd hpr hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
