module

public import CFSG.Quasithin.Background.Harris.Routing.Adapters

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Open CFSG.Blueprint

theorem oneCompFor_fam3D4_of_false
    (h : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (f : ℕ), 1 ≤ f →
      ∀ (Γ A L : Subgroup (GLV V)) (m : ℕ), G93Hyp Γ A L L m →
      ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f → False) :
    OneCompFor Fam3D4 :=
  oneCompFor_of_simple_quot
    (P := fun X _ => ∃ f, 1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f)
    (fun _ _ _ _ e ⟨f, hf, hm⟩ =>
      ⟨f, hf, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hm⟩)
    (fun _ _ ⟨hs, h⟩ => ⟨hs, h⟩)
    (fun V _ _ _ Γ A L m hG ⟨f, hf, hP⟩ => (h V f hf Γ A L m hG hP).elim)

theorem oneCompFor_fam2F4_of_false
    (h : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (f : ℕ), Odd f → 3 ≤ f →
      ∀ (Γ A L : Subgroup (GLV V)) (m : ℕ), G93Hyp Γ A L L m →
      ReeTitsModel (↥L ⧸ Subgroup.center ↥L) .twistedF4 2 f → False) :
    OneCompFor Fam2F4 :=
  oneCompFor_of_simple_quot
    (P := fun X _ => ∃ f, Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f)
    (fun _ _ _ _ e ⟨f, hf, hf3, hm⟩ =>
      ⟨f, hf, hf3, CFSG.SectionRank.reeTitsModel_of_mulEquiv e hm⟩)
    (fun _ _ ⟨hs, h⟩ => ⟨hs, h⟩)
    (fun V _ _ _ Γ A L m hG ⟨f, hf, hf3, hP⟩ => (h V f hf hf3 Γ A L m hG hP).elim)

theorem oneCompFor_famTits_of_false
    (h : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (Γ A L : Subgroup (GLV V)) (m : ℕ), G93Hyp Γ A L L m →
      ReeTitsModel (↥L ⧸ Subgroup.center ↥L) .Tits 2 1 → False) :
    OneCompFor FamTits :=
  oneCompFor_of_simple_quot (P := fun X _ => ReeTitsModel X .Tits 2 1)
    (fun _ _ _ _ e hm => CFSG.SectionRank.reeTitsModel_of_mulEquiv e hm)
    (fun _ _ h => h)
    (fun V _ _ _ Γ A L m hG hP => (h V Γ A L m hG hP).elim)

end CFSG.Quasithin.G11.Harris
