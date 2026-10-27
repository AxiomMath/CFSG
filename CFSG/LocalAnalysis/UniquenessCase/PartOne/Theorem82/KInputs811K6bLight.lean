module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811

import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeLinFour
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeLinSix
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSeven
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeSpMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

theorem three_le_pRank_centralizer_of_lieModel_psp6 {X : Type} [Group X] [Finite X] {r f : ℕ}
    (hq : ¬ 3 ∣ r ^ f) (hm : LieModel X .PSp 3 r f) :
    ∀ y : X, orderOf y = 3 → 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {y}) := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (t := .PSp) (by decide)
  letI := hK
  letI := hfin
  haveI : Finite (StatedProj (StatedSp 3 K)) := Finite.of_equiv _ e.toEquiv
  exact CFSG.GroupTheory.CoprimeTransport.le_pRank_centralizer_of_mulEquiv e
    (fun y hy => i294CrossModelPSp6_holds K (hcard ▸ hq) y hy)

theorem three_le_pRank_centralizer_of_lieModel_omega7 {X : Type} [Group X] [Finite X]
    {r f : ℕ} (hq : ¬ 3 ∣ r ^ f) (hodd : Odd (r ^ f)) (hm : LieModel X .POmegaOdd 3 r f) :
    ∀ y : X, orderOf y = 3 → 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {y}) := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (t := .POmegaOdd) (by decide)
  letI := hK
  letI := hfin
  haveI : Finite (StatedProj (StatedOmega (StatedQuadOdd 3 K))) := Finite.of_equiv _ e.toEquiv
  exact CFSG.GroupTheory.CoprimeTransport.le_pRank_centralizer_of_mulEquiv e
    (fun y hy => i294CrossModelPOmega7_holds K (hcard ▸ hq) (hcard ▸ hodd) y hy)

theorem three_le_pRank_centralizer_of_lieModel_psl4 {X : Type} [Group X] [Finite X] {r f : ℕ}
    (h3 : 3 ∣ r ^ f - 1) (hm : LieModel X .PSL 4 r f) :
    ∀ y : X, orderOf y = 3 → 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {y}) := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (t := .PSL) (by decide)
  letI := hK
  letI := hfin
  haveI : Finite (StatedProj (StatedSL 4 K)) := Finite.of_equiv _ e.toEquiv
  exact CFSG.GroupTheory.CoprimeTransport.le_pRank_centralizer_of_mulEquiv e
    (fun y hy => i294CrossModelPSL4_holds K (hcard ▸ h3) y hy)

theorem three_le_pRank_centralizer_of_lieModel_psl67 {X : Type} [Group X] [Finite X]
    {n r f : ℕ} (hn : n = 6 ∨ n = 7) (h3 : ¬ 3 ∣ r ^ f) (h3' : ¬ 3 ∣ r ^ f - 1)
    (hm : LieModel X .PSL n r f) :
    ∀ y : X, orderOf y = 3 → 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {y}) := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (t := .PSL) (by decide)
  letI := hK
  letI := hfin
  haveI : Finite (StatedProj (StatedSL n K)) := Finite.of_equiv _ e.toEquiv
  exact CFSG.GroupTheory.CoprimeTransport.le_pRank_centralizer_of_mulEquiv e
    (fun y hy => i294CrossModelPSL67_holds K (hcard ▸ h3) (hcard ▸ h3') n hn y hy)

theorem three_le_pRank_centralizer_of_isLie811_light {Y : Type} [Group Y] [Finite Y]
    {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center Y))
    (hb : fam = .psp6 ∨ fam = .omega7 ∨ (fam = .l4 ∧ r ^ f % 3 = 1) ∨
      ((fam = .l6 ∨ fam = .l7) ∧ r ^ f % 3 = 2))
    {x : Y} (hx : orderOf x = 3) : 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {x}) := by
  obtain ⟨-, -, hfam⟩ := h
  refine CFSG.GroupTheory.CoprimeTransport.le_pRank_centralizer_of_quotient hZ ?_ x hx
  rcases hb with rfl | rfl | ⟨rfl, h1⟩ | ⟨hfam67, h2⟩
  · obtain ⟨hr, hr3, hm⟩ := hfam
    exact three_le_pRank_centralizer_of_lieModel_psp6
      (fun hd => hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
        (Nat.prime_three.dvd_of_dvd_pow hd)).symm) hm
  · obtain ⟨hr, hr2, hr3, hm⟩ := hfam
    exact three_le_pRank_centralizer_of_lieModel_omega7
      (fun hd => hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
        (Nat.prime_three.dvd_of_dvd_pow hd)).symm) ((hr.odd_of_ne_two hr2).pow) hm
  · obtain ⟨-, -, ⟨-, hm⟩ | ⟨h2, -⟩⟩ := hfam
    · exact three_le_pRank_centralizer_of_lieModel_psl4 (by omega) hm
    · omega
  · rcases hfam67 with rfl | rfl
    · obtain ⟨-, ⟨-, hm⟩ | ⟨h1, -⟩⟩ := hfam
      · exact three_le_pRank_centralizer_of_lieModel_psl67 (Or.inl rfl) (by omega) (by omega) hm
      · omega
    · obtain ⟨-, ⟨-, hm⟩ | ⟨h1, -⟩⟩ := hfam
      · exact three_le_pRank_centralizer_of_lieModel_psl67 (Or.inr rfl) (by omega) (by omega) hm
      · omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
