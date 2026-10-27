module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIb5
public import CFSG.Quasithin.Recognition.Kleidman.F204.AssemblyTop
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIb3

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

@[expose] def CaseIIT1Ge7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S D X : Subgroup G), Frame L1 L2 S D X →
    ConfigT1 L1 L2 S → ∀ α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S), IsCritData α β α' →
      Zv α' ≤ Qv α → 7 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S) → False

theorem caseII_T1_false_of_lt (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
    {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
    (hb : bMin (P1 L1 L2 S) (P2 L1 L2 S) < 7) : False := by
  obtain ⟨-, -, -, ⟨k, hk⟩, hb3⟩ := t1II_setup F hT1 hc hII
  have h3 : bMin (P1 L1 L2 S) (P2 L1 L2 S) = 3 ∨ bMin (P1 L1 L2 S) (P2 L1 L2 S) = 5 := by omega
  rcases h3 with h | h
  · exact caseII_T1_b3_false F hT1 hc hII h
  · exact caseII_T1_b5_false F hT1 hc hII h

theorem caseIIT1_of_ge7 (h : CaseIIT1Ge7) : CaseIIT1 := by
  intro G _ _ L1 L2 S D X F hT1 α β α' hc hII
  by_cases hb : bMin (P1 L1 L2 S) (P2 L1 L2 S) < 7
  · exact caseII_T1_false_of_lt F hT1 hc hII hb
  · exact h G L1 L2 S D X F hT1 α β α' hc hII (by omega)

end CFSG.Quasithin.Kleidman.F204
