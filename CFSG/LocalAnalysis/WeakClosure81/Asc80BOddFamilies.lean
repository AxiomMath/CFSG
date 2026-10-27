module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddInner
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmega
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddL2
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddG2D4Outer
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcF4E8
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcE6
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcE7
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcTwE6Seitz
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddRee
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSLNonlinear
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUAniso
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSp4Q8One
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSp4QuatGen
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaAniso
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaOuter
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaRes
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterResidual

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem seitzFour_oddLieType_of_families :
    SeitzFour fun X _ => CFSG.Models.OddLieType X ∧
      ¬ CFSG.Models.LieModel X .PSL 2 5 1 ∧ ¬ CFSG.Models.LieModel X .PSL 2 3 2 := by
  have hO : SeitzFourOuter fun X _ => IsOddOrthogonal X :=
    POmegaOuter.seitzFourOuter_orthogonal_of_aniso POmegaOuter.seitzFourOOuterAniso_holds
  intro G _ _ L E hLn hLs hnab ⟨⟨t, n, p, f, hp, hm⟩, h5, h9⟩ hC hE h4 hx
  obtain ⟨-, -, hadm⟩ := hm.1
  cases t with
  | PSL =>
    rcases (show 2 = n ∨ 3 ≤ n by have := hadm.1; omega) with rfl | hn
    · exact seitzFour_psl2 L E hLn hLs hnab ⟨⟨p, f, hp, hm⟩, h5, h9⟩ hC hE h4 hx
    · exact PSLOuter.seitzFour_psl L E hLn hLs hnab ⟨n, p, f, hn, hp, hm⟩ hC hE h4 hx
  | PSU =>
    exact seitzFour_of_inner_outer
      (P := fun X _ => ∃ n p f : ℕ, 3 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSU n p f)
      seitzFourInner_psu seitzFourOuter_psu L E hLn hLs hnab ⟨n, p, f, hadm.1, hp, hm⟩ hC hE h4 hx
  | PSp =>
    exact seitzFour_of_inner_outer
      (P := fun X _ => ∃ n p f : ℕ, 2 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSp n p f)
      seitzFourInner_psp
        (PSpOuter.seitzFourOuter_psp_of_sp4DiagAniso
          (PSpOuter.seitzFourSp4DiagAniso_of_quat PSpOuter.seitzFourSp4DiagQuat_holds))
        L E hLn hLs hnab ⟨n, p, f, hadm.1, hp, hm⟩ hC hE h4 hx
  | POmegaOdd =>
    exact seitzFour_of_inner_outer OSeitz.seitzFourInner_orthogonal hO L E hLn hLs hnab
      ⟨n, p, f, hp, Or.inl hm⟩ hC hE h4 hx
  | POmegaPlus =>
    exact seitzFour_of_inner_outer OSeitz.seitzFourInner_orthogonal hO L E hLn hLs hnab
      ⟨n, p, f, hp, Or.inr (Or.inl hm)⟩ hC hE h4 hx
  | POmegaMinus =>
    exact seitzFour_of_inner_outer OSeitz.seitzFourInner_orthogonal hO L E hLn hLs hnab
      ⟨n, p, f, hp, Or.inr (Or.inr hm)⟩ hC hE h4 hx
  | G2 =>
    obtain rfl := hadm.1
    exact seitzFour_g2_td4 L E hLn hLs hnab ⟨p, f, hp, Or.inr hm⟩ hC hE h4 hx
  | trialityD4 =>
    obtain rfl : n = 0 := hadm
    exact seitzFour_g2_td4 L E hLn hLs hnab ⟨p, f, hp, Or.inl hm⟩ hC hE h4 hx
  | F4 =>
    obtain rfl : n = 0 := hadm
    exact seitzFour_f4_e8 L E hLn hLs hnab ⟨p, f, hp, Or.inl hm⟩ hC hE h4 hx
  | E8 =>
    obtain rfl : n = 0 := hadm
    exact seitzFour_f4_e8 L E hLn hLs hnab ⟨p, f, hp, Or.inr hm⟩ hC hE h4 hx
  | E6 =>
    obtain rfl : n = 0 := hadm
    exact seitzFour_e6 L E hLn hLs hnab ⟨p, f, hp, hm⟩ hC hE h4 hx
  | twistedE6 =>
    obtain rfl : n = 0 := hadm
    exact seitzFour_twistedE6 L E hLn hLs hnab ⟨p, f, hp, hm⟩ hC hE h4 hx
  | twistedG2 =>
    obtain ⟨rfl, rfl, -⟩ := hadm
    exact seitzFour_ree L E hLn hLs hnab ⟨f, hm⟩ hC hE h4 hx
  | E7 =>
    obtain rfl : n = 0 := hadm
    exact seitzFour_e7 L E hLn hLs hnab ⟨p, f, hp, hm⟩ hC hE h4 hx
  | twistedB2 => exact absurd hadm.2.1 hp
  | twistedF4 => exact absurd hadm.2.1 hp
  | Tits => exact absurd hadm.2.1 hp

end CFSG.LocalAnalysis.WeakClosure81
