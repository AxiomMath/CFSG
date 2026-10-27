module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Native
public import CFSG.Quasithin.Background.F7TwoInvD4Aut
public import CFSG.Quasithin.Background.F7TwoInvSQTKFam
public import CFSG.Quasithin.Background.F7TwoDefs

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.TrialityD4


theorem invAutGenFam3D4Even : InvAutGenFam3D4Even := by
  intro f S _ _ hf hmod φ hφ2 hφ1
  have hLie : LieModel S .trialityD4 0 2 f := Or.inr (Or.inl ⟨rfl, by decide, hmod⟩)
  obtain ⟨d⟩ := nonempty_trialityD4Data_of_lieModel hf hLie
  exact invAutGen_of_trialityD4Data d hf hmod.2 hφ2 hφ1

end CFSG.Quasithin.F7Two
