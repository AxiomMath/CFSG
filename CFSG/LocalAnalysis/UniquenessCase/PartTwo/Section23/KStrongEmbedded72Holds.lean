module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72U3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Spor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Local
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72AltTenRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72AutSz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72ReeMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def KF7ReeTypeOne : Prop :=
  ∀ {X : Type} [Group X] [Finite X], CFSG.pPrimeCore 3 X = ⊥ →
    ∀ {L N : Subgroup X},
      L.Normal → genFittingFStar X ≤ L → F07.IsReeType ↥L 1 →
        IsStronglyPEmbedded 3 N → Group.IsSolvable ↥N

theorem kf7ReeTypeOne_of_recognition (hRec : KF7ReeTypeOneRecognition) : KF7ReeTypeOne := by
  intro X _ _ hO L N hLN hKL hshape hN
  exact kf7_reeType_one_of_recognition hRec hO hLN hKL hshape hN

theorem kf7_reeType_one_case (hRee : KF7ReeTypeOne) {p : ℕ} (hp3 : p = 3)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal)
    (hKL : genFittingFStar X ≤ L) (hshape : F07.IsReeType ↥L 1)
    (hN : IsStronglyPEmbedded p N) : Group.IsSolvable ↥N := by
  subst hp3
  exact hRee hO hLN hKL hshape hN

theorem kf7ReeTypeOne_holds :
    KF7ReeTypeOne :=
  kf7ReeTypeOne_of_recognition kf7_reeType_one_recognition

theorem kStrongEmbedded72_holds :
    KStrongEmbedded72 := by
  intro p hp hp2 X hG hFin hO
  intro L hLN hKL hshape
  intro N hN
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hshape with ⟨n, hPSL⟩ | ⟨n, hPSU⟩ | ⟨hp3, hRee' | hM11 | hL3⟩ |
    ⟨hp5, hAutSz | hTits | hMcL | hAlt⟩ | ⟨hp11, hJ4⟩
  ·
    left
    have hn : 1 ≤ n := by
      have hadm := hPSL.admissible
      rw [CFSG.Open.StatedLieAdmissible] at hadm
      exact hadm.2.1
    exact kf7_l2_case hp hp2 hn hO hLN hKL hPSL hN
  ·
    left
    exact kf7_u3_case hp hp2 hO hLN hKL hPSU hN
  ·
    left
    exact kf7_reeType_one_case kf7ReeTypeOne_holds hp3 hO hLN hKL hRee' hN
  ·
    left
    exact kf7_m11_case hp hp3 hO hLN hKL hM11 hN
  ·
    left
    exact kf7_l34_case hp hp3 hO hLN hKL hL3 hN
  ·
    left
    exact kf7_autSz_case hp hp5 hO hLN hKL hAutSz hN
  ·
    left
    exact kf7_tits_case hp hp5 hO hLN hKL hTits hN
  ·
    left
    exact kf7_mcl_case hp hp5 hO hLN hKL hMcL hN
  ·
    exact Or.inr (kf7_altTen_case hp hp5 hO hLN hKL hAlt hN)
  ·
    left
    exact kf7_j4_case hp hp11 hO hLN hKL hJ4 hN

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
