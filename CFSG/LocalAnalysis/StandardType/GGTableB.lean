module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem LargeEvenLabelAll.mono {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (hPP' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → P' R I F)
    (h : LargeEvenLabelAll lab P) : LargeEvenLabelAll lab P' := fun Q hQ =>
  largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.1, hPP' R I F hq.2⟩) (h Q hQ)

theorem ggTableBInputs_of_labels
    (h₀ : ∀ lab, LargeEvenInLambda2 lab → ¬ GGOutdiagPilotLabel lab →
      LargeEvenLabelAll lab fun R _ I _ => GGOutdiagCyclic R I)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I) :
    GGLNoncyclicInput ∧ GGBstarInput ∧ GGStdSubPreInput := by
  have ha₀ := ggLNoncyclicInput_of_remaining h₀
  refine ⟨ha₀, ggBstarInput_of_labels ha₀ fun p lab hp hlab hs => ?_,
    ggStdSubPreInput_of_labels fun p lab hp hlab hs => ?_⟩
  · exact (h p lab hp hlab hs).mono fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩
  · exact (h p lab hp hlab hs).mono fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, h3⟩

end CFSG.StandardType
