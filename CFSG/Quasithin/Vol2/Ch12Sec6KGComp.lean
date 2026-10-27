module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGFacts26

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def Comp12626Lie2Big : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v → ∀ f : ℕ, 3 ≤ f →
      ¬ (StatedClassicalModel ↥K .PSL 2 2 f ∨ StatedClassicalModel ↥K .PSL 3 2 f ∨
        StatedClassicalModel ↥K .PSU 3 2 f ∨ StatedClassicalModel ↥K .PSp 2 2 f ∨
        ChevalleyExceptionalModel ↥K .G2 2 f ∨ ChevalleyExceptionalModel ↥K .trialityD4 2 f ∨
        (Odd f ∧ ReeTitsModel ↥K .twistedF4 2 f) ∨ (Odd f ∧ SuzukiModel ↥K 2 f) ∨
        ∃ s : Bool, IsSLEps3 s (2 ^ f) ↥K)

@[expose] def Comp12626Lie2Four : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v →
      ¬ (StatedClassicalModel ↥K .PSL 3 2 2 ∨ StatedClassicalModel ↥K .PSU 3 2 2 ∨
        StatedClassicalModel ↥K .PSp 2 2 2 ∨ ChevalleyExceptionalModel ↥K .G2 2 2 ∨
        ChevalleyExceptionalModel ↥K .trialityD4 2 2 ∨ ∃ s : Bool, IsSLEps3 s 4 ↥K)

@[expose] def Comp12626Lie2Two : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v →
      ¬ (StatedClassicalModel ↥K .PSL 3 2 1 ∨ StatedClassicalModel ↥K .PSL 4 2 1 ∨
        StatedClassicalModel ↥K .PSL 5 2 1 ∨ ChevalleyExceptionalModel ↥K .trialityD4 2 1 ∨
        ReeTitsModel ↥K .Tits 2 1)

@[expose] def Comp12626Sporadic : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v → ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
        s = .HS ∨ s = .He ∨ s = .Ru) → ¬ Nonempty (↥K ≃* NativeSporadic.Carrier s)

end CFSG.Quasithin.H13.S126C
