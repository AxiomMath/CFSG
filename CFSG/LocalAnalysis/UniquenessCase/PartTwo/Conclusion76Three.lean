module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Core
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Theorem76
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem pRank_pPrimeCore_le_three_of_evenRank_le_three (he : CFSG.Open.evenRank G ≤ 3)
    {M : Subgroup G} (hM : IsTwoLocal M) {p : ℕ} (hp : p.Prime) (hsp : IsStronglyPEmbedded p M)
    (huniq : ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (D : Set G) ⊓ M) →
      Subgroup.normalizer (D : Set G) ≤ M)
    {H : Subgroup G} (hHM : ¬ H ≤ M) (hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) {q : ℕ}
    (hq : q.Prime) :
    CFSG.Open.pRank q ((CFSG.pPrimeCore p ↥H).map H.subtype) ≤ 3 := by
  have hKM := pPrimeCore_le hsp hp hrank
  rcases eq_or_ne q 2 with rfl | hq2
  ·
    have hodd : Odd (Nat.card (CFSG.pPrimeCore p ↥H)) := odd_card_pPrimeCore hsp hp huniq hHM hrank
    obtain ⟨E, hEK, -, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) ((CFSG.pPrimeCore p ↥H).map H.subtype)
    have hdvd : Nat.card E ∣ Nat.card (CFSG.pPrimeCore p ↥H) := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective]
      exact Subgroup.card_dvd_of_le hEK
    by_contra hlt
    have h2 : 2 ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self 2 (by omega)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
  · calc CFSG.Open.pRank q ((CFSG.pPrimeCore p ↥H).map H.subtype) ≤ CFSG.Open.pRank q M :=
          CFSG.SectionRank.pRank_mono hq.one_lt hKM
      _ ≤ CFSG.Open.evenRank G :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank q hq hq2 M hM
      _ ≤ 3 := he

namespace Sec7Core4

@[expose] def ofThree (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G) (M : Subgroup G)
    (maxLocal : rankThreeIsMaxTwoLocal M) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (strong : IsStronglyPEmbedded p M)
    (huniq : ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (D : Set G) ⊓ M) →
      Subgroup.normalizer (D : Set G) ≤ M) :
    Sec7Core4 G where
  standing := ⟨hS.simple, hS.nonab, hS.kProper, hS.charTwo, le_of_eq hS.rank.symm⟩
  M := M
  maxLocal := maxLocal
  p := p
  prime := hp
  odd := hp2
  strong := strong
  huniq := huniq
  rankK := fun _ hHM hrank _ hq =>
    pRank_pPrimeCore_le_three_of_evenRank_le_three (le_of_eq hS.rank) maxLocal.1 hp strong huniq
      hHM hrank hq

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 Sec7Core4 StronglyEmbeddedFive StronglyEmbeddedThree rankThreeGamma_self_le)

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_mem_sigmaOf (S : Setup G) {p : ℕ} (hp : p ∈ sigmaOf S.M) :
    ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank p (normalizer (D : Set G) ⊓ S.M) → normalizer (D : Set G) ≤ S.M :=
  fun D hD hD2 h2 => hp.2.choose_spec.u2 _ ⟨D, hD, hD2, rfl⟩ h2

theorem normalizer_le_of_agl81TheoremC (hUC : rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hsp : IsStronglyPEmbedded p S.M) :
    ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank p (normalizer (D : Set G) ⊓ S.M) → normalizer (D : Set G) ≤ S.M := by
  intro D hD hD2 h2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (normalizer (D : Set G) ⊓ S.M)
  have hEM : E ≤ S.M := hE.trans inf_le_right
  have hEp : IsPGroup p E := hEel.isPGroup
  have h2E : 2 ≤ CFSG.Open.pRank p E :=
    h2.trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEel hEcard)
  exact hC hUC S.p S.hp S.P S.M S.witness p hp hp2 E hEM hEp h2E
    (rankThreeGamma_self_le hsp hEM hEp) (normalizer (D : Set G)) ⟨D, hD, hD2, rfl⟩
    (hE.trans inf_le_left)

theorem conclusion76_three_dataOfSetup (hSE3 : StronglyEmbeddedThree) (hS : Standing G)
    (hUC : rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    (hk1 : IsStronglyPEmbedded 3 (dataOfSetup hS S).M) :
    Conclusion76 (dataOfSetup hS S).M 3 :=
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal 3 Nat.prime_three
    (by norm_num) hk1 (normalizer_le_of_agl81TheoremC hUC hC S Nat.prime_three (by norm_num) hk1)
  k.conclusion76_of_stronglyEmbeddedThree rfl hSE3

theorem conclusion76_dataOfSetup_of_five_le (hSE : StronglyEmbeddedFive) (hS : Standing G)
    (hUC : rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hsp : IsStronglyPEmbedded p (dataOfSetup hS S).M) :
    Conclusion76 (dataOfSetup hS S).M p :=
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal p hp (by omega) hsp
    (normalizer_le_of_agl81TheoremC hUC hC S hp (by omega) hsp)
  k.conclusion76_of_kIDExcluded h5 (k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank)) hSE

theorem r76_dataOfSetup (hSE : StronglyEmbeddedFive) (hSE3 : StronglyEmbeddedThree)
    (hS : Standing G) (hUC : rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G) :
    UC22.F07.R76 (dataOfSetup hS S) := by
  intro p hp hp2 hsp
  rcases eq_or_ne p 3 with rfl | hp3
  · exact conclusion76_three_dataOfSetup hSE3 hS hUC hC S hsp
  · exact conclusion76_dataOfSetup_of_five_le hSE hS hUC hC S hp
      (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hsp

theorem r76Sig_dataOfSetup (hSE : StronglyEmbeddedFive) (hSE3 : StronglyEmbeddedThree)
    (hS : Standing G) (S : Setup G) : UC22.F07.R76Sig (dataOfSetup hS S) := by
  intro p hp hp2 hsp
  have hpp : p.Prime := ((dataOfSetup hS S).sig_prime p hp).1
  rcases eq_or_ne p 3 with rfl | hp3
  · exact (Sec7Core4.ofThree hS S.M S.witness.maxLocal 3 hpp hp2 hsp
      (normalizer_le_of_mem_sigmaOf S hp)).conclusion76_of_stronglyEmbeddedThree rfl hSE3
  · let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal p hpp hp2 hsp
      (normalizer_le_of_mem_sigmaOf S hp)
    exact k.conclusion76_of_kIDExcluded (hpp.five_le_of_ne_two_of_ne_three hp2 hp3)
      (k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank)) hSE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
