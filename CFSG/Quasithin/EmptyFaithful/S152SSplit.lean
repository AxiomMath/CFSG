module

public import CFSG.Quasithin.EmptyFaithful.S152SFam

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def BCTFamL2 : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSL 2 2 f →
    BorelCentralizerTrivial X

@[expose] def BCTFamL3 : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSL 3 2 f →
    BorelCentralizerTrivial X

@[expose] def BCTFamU3 : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSU 3 2 f →
    BorelCentralizerTrivial X

@[expose] def BCTFamSp4 : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSp 2 2 f →
    BorelCentralizerTrivial X

@[expose] def BCTFamG2 : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .G2 2 f →
    BorelCentralizerTrivial X

@[expose] def BCTFam3D4 : Prop :=
  ∀ (f : ℕ), 2 ≤ f → ∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .trialityD4 2 f →
    BorelCentralizerTrivial X

@[expose] def BCTFam2F4 : Prop :=
  ∀ (f : ℕ), Odd f → 3 ≤ f → ∀ (X : Type) [Group X] [Finite X], ReeTitsModel X .twistedF4 2 f →
    BorelCentralizerTrivial X

@[expose] def BCTFamSz : Prop :=
  ∀ (f : ℕ), Odd f → 3 ≤ f → ∀ (X : Type) [Group X] [Finite X], SuzukiModel X 2 f →
    BorelCentralizerTrivial X

theorem BigQBorelCentralizerTrivial.of_families (h1 : BCTFamL2) (h2 : BCTFamL3) (h3 : BCTFamU3)
    (h4 : BCTFamSp4) (h5 : BCTFamG2) (h6 : BCTFam3D4) (h7 : BCTFam2F4) (h8 : BCTFamSz) :
    BigQBorelCentralizerTrivial := by
  intro X _ _ ⟨f, hf, h⟩
  rcases h with h | h | h | h | h | h | h | h
  · exact h1 f hf X h
  · exact h2 f hf X h
  · exact h3 f hf X h
  · exact h4 f hf X h
  · exact h5 f hf X h
  · exact h6 f hf X h
  · exact h7 f h.1 h.2.1 X h.2.2
  · exact h8 f h.1 h.2.1 X h.2.2

end CFSG.Quasithin
