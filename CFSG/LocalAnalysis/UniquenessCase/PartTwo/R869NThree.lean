module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS3
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Good
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R869NRest3 (D : Data G) : Prop :=
  ∀ L : Subgroup G, L ≤ D.M → D.M ≤ normalizer (L : Set G) → IsProdOfCalC D.M L → ¬ Thin8 L →
    (∀ q : ℕ, q.Prime → q ≠ 2 → 2 ≤ CFSG.Open.pRank q L → IsStronglyPEmbedded q D.M →
      q = 5 ∧ ¬ 2 ^ 12 ∣ Nat.card (Bar2 L)) →
    ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ A : Subgroup G, A ≤ D.M → Nat.card A = r →
      (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L → normalizer (A : Set G) ≤ D.M

theorem R869NRest3_of_R869N (D : Data G) (h : R869N D) : R869NRest3 D :=
  fun L hLM hML hprod hthin _ => h L hLM hML hprod hthin

end CFSG.LocalAnalysis.UniquenessCase.UC22.F08

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Sec7Core4 StronglyEmbeddedFive StronglyEmbeddedThree StronglyEmbeddedSolvable)

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_r870 (hSS : StronglyEmbeddedSolvable) (hSE : StronglyEmbeddedFive)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hsp : IsStronglyPEmbedded q S.M)
    (huniq : ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank q (normalizer (D : Set G) ⊓ S.M) → normalizer (D : Set G) ≤ S.M)
    {L A : Subgroup G} (hLM : L ≤ S.M) (hLperf : ⁅L, L⁆ = L) (h2 : 2 ≤ CFSG.Open.pRank q L)
    (h5 : q = 5 → 2 ^ 12 ∣ Nat.card (Bar2 L)) {r : ℕ} (hr : r.Prime) (hAM : A ≤ S.M)
    (hAr : Nat.card A = r) (hY : (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L) :
    normalizer (A : Set G) ≤ S.M := by
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal q hq hq2 hsp huniq
  refine UC6.R869S.normalizer_le_of_solvable_or hS.simple hq hq2 hLM hLperf h2 h5 hr hAM hAr hY
    fun H htop hHM hrank => ?_
  have hH : k.Config H := ⟨htop, hHM, hrank⟩
  by_cases hq3 : q = 3
  · exact Or.inl (k.kInputThree hq3 hK3 hH).2.2.2
  · have h5k : 5 ≤ k.p := hq.five_le_of_ne_two_of_ne_three hq2 hq3
    rcases k.solvable_or_of_stronglyEmbeddedSolvable_of_kIDExcluded h5k
        (k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank)) hH (k.step75 h5k hSE) hSS with
      hsol | ⟨hq5, -, hle⟩
    · exact Or.inl hsol
    · exact Or.inr ⟨hq5, k.odd_card_pPrimeCore_of_not_le hHM hrank, hle⟩

theorem r869NS5_dataOfSetup (hSS : StronglyEmbeddedSolvable) (hSE : StronglyEmbeddedFive)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G) :
    F08.R869NS5 (dataOfSetup hS S) := by
  rintro L hLM hML hprod ⟨p, hp, h2, h5⟩ r hr hr2 A hAM hAr hY
  have hσ := (dataOfSetup hS S).sig_prime p hp
  have hLperf := UC6.R869S.perfect_of_isProdOfCalC hprod
  have hns : ¬ Group.IsSolvable ↥(dataOfSetup hS S).M := by
    intro hs
    have hsL : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLM)
    rw [CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hLperf] at hsL
    subst hsL
    obtain ⟨E, hE, -, hcard⟩ := CFSG.SectionRank.exists_pRank hσ.1.one_lt (⊥ : Subgroup G)
    rw [le_bot_iff.1 hE, Subgroup.card_bot] at hcard
    have := Nat.one_lt_pow (by omega : CFSG.Open.pRank p (⊥ : Subgroup G) ≠ 0) hσ.1.one_lt
    omega
  exact normalizer_le_of_r870 hSS hSE hK3 hS S hσ.1 hσ.2
    (UC6S846.sp_of_mem_sig (UC6S846.sigmaStd_dataOfSetup hS S) hns hp)
    (normalizer_le_of_mem_sigmaOf S hp) hLM hLperf h2 h5 hr hAM hAr hY

theorem r869N_dataOfSetup_of_rest3 (hSS : StronglyEmbeddedSolvable) (hSE : StronglyEmbeddedFive)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (hUC : rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (h : F08.R869NRest3 (dataOfSetup hS S)) :
    F08.R869N (dataOfSetup hS S) := by
  intro L hLM hML hprod hthin r hr hr2 A hAM hAr hY
  by_cases hq : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q L ∧
      IsStronglyPEmbedded q S.M ∧ (q = 5 → 2 ^ 12 ∣ Nat.card (Bar2 L))
  · obtain ⟨q, hq, hq2, h2, hsp, h5⟩ := hq
    exact normalizer_le_of_r870 hSS hSE hK3 hS S hq hq2 hsp
      (normalizer_le_of_agl81TheoremC hUC hC S hq hq2 hsp) hLM
      (UC6.R869S.perfect_of_isProdOfCalC hprod) h2 h5 hr hAM hAr hY
  · refine h L hLM hML hprod hthin (fun q hq' hq2 h2 hsp => ?_) r hr hr2 A hAM hAr hY
    by_contra hne
    exact hq ⟨q, hq', hq2, h2, hsp, fun h5 => Classical.byContradiction fun h12 => hne ⟨h5, h12⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
