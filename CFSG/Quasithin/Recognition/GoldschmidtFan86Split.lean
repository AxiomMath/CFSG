module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Open CFSG.QuasithinUnique

@[expose] def FanNoD10 : Prop :=
  ∀ (A C B : Type) [Group A] [Group C] [Group B] (X : GoldAmalgam A C B), Hyp53 X →
    ¬ Nonempty (oTwoQuot A ≃* DihedralGroup 5)

@[expose] def FanOrder : Prop :=
  ∀ (A C B : Type) [Group A] [Group C] [Group B] (X : GoldAmalgam A C B), Hyp53 X →
    Nat.card C = 2 ^ 11 ∨ Nat.card C = 2 ^ 12

@[expose] def FanUnique : Prop :=
  ∀ (A C B A' C' B' : Type) [Group A] [Group C] [Group B] [Group A'] [Group C'] [Group B']
    (X : GoldAmalgam A C B) (X' : GoldAmalgam A' C' B'), Hyp53 X → Hyp53 X' →
      Nat.card C = Nat.card C' → X.IsIso X'

theorem fanMain_iff : FanMain ↔ FanNoD10 ∧ FanOrder ∧ FanUnique := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun A C B _ _ _ X hX => (h1 A C B X hX).1, fun A C B _ _ _ X hX => (h1 A C B X hX).2,
      h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun A C B _ _ _ X hX => ⟨h1 A C B X hX, h2 A C B X hX⟩, h3⟩

end CFSG.Quasithin.Fan86
