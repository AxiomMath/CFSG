module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SigCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabElem

public section

namespace CFSG.KC.EvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.EvenSporadicStandard.M22Std.E32Check

@[expose] def insK (a : Tab) : List Tab → List Tab
  | [] => [a]
  | b :: l => if tabLE a b = true then a :: b :: l else b :: insK a l

@[expose] def isortK : List Tab → List Tab
  | [] => []
  | b :: l => insK b (isortK l)

@[expose] def elemStepK (I : List Tab) (lv : List (List Tab)) : List (List Tab) :=
  (lv.flatMap fun L => (extCands I L).map fun x => isortK (ext L x)).dedup

@[expose] def elemLevelK (T : List Tab) : Nat → List (List Tab)
  | 0 => [[idTab]]
  | k + 1 => elemStepK (invTabs T) (elemLevelK T k)

@[expose] def jTabsK : List Tab := (elemLevelK s0Tabs 5).headD []

@[expose] def CheckPropK : Prop :=
  (elemLevelK s0Tabs 5).length = 1 ∧ elemLevelK s0Tabs 6 = [] ∧
  jTabsK.length = 32 ∧ jTabsK.Nodup ∧ idTab ∈ jTabsK ∧
  (∀ a ∈ jTabsK, a ∈ s0Tabs ∧ tmul a a = idTab ∧
    ∀ b ∈ jTabsK, tmul a b ∈ jTabsK ∧ comm a b = true) ∧
  (∃ l ∈ s0Inner, l ∈ jTabsK ∧ l ∉ f1Tabs) ∧
  ∀ L ∈ elemLevelK s0Tabs 4, L.Nodup ∧
    (normB L = true → 4 < (L.filter fun l => decide (l ∈ jTabsK)).length ∨ ∀ l ∈ L, l ∈ f1Tabs)

instance : Decidable CheckPropK := by
  unfold CheckPropK
  infer_instance

@[expose] def xPropK : Prop :=
  ∃ l ∈ jTabsK, l ∈ s0Outer ∧ tmul l l = idTab ∧ fixF l = 4

instance : Decidable xPropK := by
  unfold xPropK
  infer_instance

end CFSG.KC.EvenSporM22
