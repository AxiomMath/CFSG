module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811

import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmMinusMain
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniPSU67

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

theorem three_le_pRank_centralizer_of_lieModel_psu4 {X : Type} [Group X] [Finite X] {r f : ℕ}
    (h3 : 3 ∣ r ^ f + 1) (hm : LieModel X .PSU 4 r f) :
    ∀ y : X, orderOf y = 3 → 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {y}) := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (t := .PSU) (by decide)
  letI := hK
  letI := hfin
  haveI : Finite (StatedProj (StatedSU 4 (r ^ f) K)) := Finite.of_equiv _ e.toEquiv
  exact CFSG.GroupTheory.CoprimeTransport.le_pRank_centralizer_of_mulEquiv e
    (fun y hy => i294CrossModelPSU4_holds (r ^ f) K hcard h3 y hy)

theorem three_le_pRank_centralizer_of_lieModel_psu67 {X : Type} [Group X] [Finite X]
    {n r f : ℕ} (hn : n = 6 ∨ n = 7) (h3 : ¬ 3 ∣ r ^ f) (h3' : ¬ 3 ∣ r ^ f + 1)
    (hm : LieModel X .PSU n r f) :
    ∀ y : X, orderOf y = 3 → 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {y}) := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (t := .PSU) (by decide)
  letI := hK
  letI := hfin
  haveI : Finite (StatedProj (StatedSU n (r ^ f) K)) := Finite.of_equiv _ e.toEquiv
  exact CFSG.GroupTheory.CoprimeTransport.le_pRank_centralizer_of_mulEquiv e
    (fun y hy => i294CrossModelPSU67_holds (r ^ f) K hcard h3 h3' n hn y hy)

theorem three_le_pRank_centralizer_of_lieModel_pomega8m {X : Type} [Group X] [Finite X]
    {r f : ℕ} (hq : ¬ 3 ∣ r ^ f) (hm : LieModel X .POmegaMinus 4 r f) :
    ∀ y : X, orderOf y = 3 → 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {y}) := by
  obtain ⟨-, K, hK, hfin, hcard, b, c, hbc, ⟨e⟩⟩ :=
    hm.statedClassicalModel (t := .POmegaMinus) (by decide)
  letI := hK
  letI := hfin
  haveI : Finite (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) :=
    Finite.of_equiv _ e.toEquiv
  exact CFSG.GroupTheory.CoprimeTransport.le_pRank_centralizer_of_mulEquiv e
    (fun y hy => i294CrossModelPOmegaMinus4_holds K (hcard ▸ hq) b c hbc y hy)

theorem three_le_pRank_centralizer_of_isLie811_heavy {Y : Type} [Group Y] [Finite Y]
    {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center Y))
    (hb : (fam = .l4 ∧ r ^ f % 3 = 2) ∨ ((fam = .l6 ∨ fam = .l7) ∧ r ^ f % 3 = 1) ∨
      fam = .pomega8m)
    {x : Y} (hx : orderOf x = 3) : 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {x}) := by
  obtain ⟨-, -, hfam⟩ := h
  refine CFSG.GroupTheory.CoprimeTransport.le_pRank_centralizer_of_quotient hZ ?_ x hx
  rcases hb with ⟨rfl, h2⟩ | ⟨hfam67, h1⟩ | rfl
  · obtain ⟨-, -, ⟨h1, -⟩ | ⟨-, hm⟩⟩ := hfam
    · omega
    · exact three_le_pRank_centralizer_of_lieModel_psu4 (by omega) hm
  · rcases hfam67 with rfl | rfl
    · obtain ⟨-, ⟨h2, -⟩ | ⟨-, hm⟩⟩ := hfam
      · omega
      · exact three_le_pRank_centralizer_of_lieModel_psu67 (Or.inl rfl) (by omega) (by omega) hm
    · obtain ⟨-, ⟨h2, -⟩ | ⟨-, hm⟩⟩ := hfam
      · omega
      · exact three_le_pRank_centralizer_of_lieModel_psu67 (Or.inr rfl) (by omega) (by omega) hm
  · obtain ⟨hr, hr3, hm⟩ := hfam
    exact three_le_pRank_centralizer_of_lieModel_pomega8m
      (fun hd => hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
        (Nat.prime_three.dvd_of_dvd_pow hd)).symm) hm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
