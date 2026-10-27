module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Card
import CFSG.LocalAnalysis.UniquenessCase.UC22SigmaThreeStrong
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS3
import CFSG.LocalAnalysis.UniquenessCase.UC7P3NoBad
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Setup4Core
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_not_centralizesBar_of_strong (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hSS : StronglyEmbeddedSolvable) (hB : BadNoStrongThree) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hspr : IsStronglyPEmbedded r S.M) (hrL : 2 ≤ CFSG.Open.pRank r L)
    (hrB : r ∣ Nat.card (BarInf L)) (h3600 : 3600 < Nat.card (BarInf L))
    {a : G} (ha : a ∈ c.B) (hpr : (orderOf a).Prime) : ¬ CentralizesBar a L := by
  intro haL
  have hr2 : r ≠ 2 := by omega
  have : Fact r.Prime := ⟨hr⟩
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha
  have hLM : L ≤ S.M := CFSG.Quasithin.A3.subnormal_le hL.1
  let k := PartOne.Section7.R72.setup4Core hS hU S hPart r hr hr2 hspr
  have h5k : 5 ≤ k.p := hr5
  have hra : orderOf a ≠ 2 := fun h => Nat.not_even_iff_odd.mpr hodd (h ▸ even_two)
  have hY := uc22p21d_sup_pCore_eq hpr hra (Nat.card_zpowers a) fun g hg =>
    uc22p21d_centralizesBar_of_mem_zpowers haL hg
  have hle : normalizer ((zpowers a : Subgroup G) : Set G) ≤ S.M := by
    refine uc22s213_normalizer_le_of_card_barInf hS.simple hr hr2 hLM hL.2.1 hL.2.2 hrL hrB h3600
      hpr (zpowers_le.mpr (c.hBM (c.hle ha))) (Nat.card_zpowers a) hY
      fun H htop hHM hrank Y hYN hYp => ?_
    have hH : k.Config H := ⟨htop, hHM, hrank⟩
    rcases (em (3 ∈ uniqueFourBeta G)).elim
        (fun h3 => k.solvable_or_of_stronglyEmbeddedSolvable_of_kIDExcluded h5k
          (k.kIDExcluded_of_strongThree h5k
            (isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hσ h3) hB)
          hH (k.step75 h5k hSE) hSS)
        (fun h3 => k.solvable_or_of_stronglyEmbeddedSolvable h5k h3 hH (k.step75 h5k hSE) hSS)
      with hsol | ⟨-, -, h3600'⟩
    ·
      have : Group.IsSolvable ↥(((H ⊓ S.M).subgroupOf H).map
          (QuotientGroup.mk' (CFSG.pPrimeCore r ↥H))) := hsol
      have hsY : Group.IsSolvable ↥Y :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYN)
      rw [CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect hYp] at hsY
      rw [hsY, Subgroup.card_bot]
      norm_num
    · exact h3600' Y hYN hYp
  exact s21_2 _ Ch hH c (zpowers a) (zpowers_le.mpr ha) hle

end CFSG.LocalAnalysis.UniquenessCase.UC22
