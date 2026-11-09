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

@[expose] def StepOKK (T : List Tab) (k : Nat) : Prop :=
  (∀ L ∈ elemLevel T k, ∀ x ∈ extCands (invTabs T) L, isortK (ext L x) ∈ elemLevel T (k + 1)) ∧
    ∀ L ∈ elemLevel T (k + 1), L.length = 2 ^ (k + 2)

instance (T : List Tab) (k : Nat) : Decidable (StepOKK T k) := by
  unfold StepOKK
  infer_instance

@[expose] def stepB (k i : Nat) : Bool :=
  (extCands (invTabs s0Tabs) ((elemLevel s0Tabs k).getD i [])).all fun x =>
    decide (isortK (ext ((elemLevel s0Tabs k).getD i []) x) ∈ elemLevel s0Tabs (k + 1))

theorem stepOKK_of (k n : Nat) (hn : (elemLevel s0Tabs k).length = n)
    (h : ∀ i < n, stepB k i = true)
    (hl : ∀ L ∈ elemLevel s0Tabs (k + 1), L.length = 2 ^ (k + 2)) : StepOKK s0Tabs k := by
  refine ⟨fun L hL x hx => ?_, hl⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have hb := h i (by omega)
  unfold stepB at hb
  rw [List.getD_eq_getElem _ _ hi] at hb
  exact of_decide_eq_true (List.all_eq_true.1 hb x hx)

@[expose] def jTabsK : List Tab := (elemLevel s0Tabs 4).headD []

@[expose] def CheckRestK : Prop :=
  (elemLevel s0Tabs 4).length = 1 ∧
  jTabsK.length = 32 ∧ jTabsK.Nodup ∧ jTabsK.Pairwise (fun a b => tabLE a b = true) ∧
  idTab ∈ jTabsK ∧ tTab ∈ jTabsK ∧
  (∀ a ∈ jTabsK, a ∈ s0Tabs ∧ tmul a a = idTab ∧
    ∀ b ∈ jTabsK, tmul a b ∈ jTabsK ∧ comm a b = true) ∧
  (∃ l ∈ s0Inner, l ∈ jTabsK ∧ l ∉ f1Tabs) ∧
  ∀ L ∈ elemLevel s0Tabs 3, L.Nodup ∧
    (normB L = true → 4 < (L.filter fun l => decide (l ∈ jTabsK)).length ∨ ∀ l ∈ L, l ∈ f1Tabs)

instance : Decidable CheckRestK := by
  unfold CheckRestK
  infer_instance

@[expose] def CheckPropK : Prop := (∀ k < 5, StepOKK s0Tabs k) ∧ CheckRestK

@[expose] def xPropK : Prop :=
  ∃ l ∈ jTabsK, l ∈ s0Outer ∧ tmul l l = idTab ∧ fixF l = 4

instance : Decidable xPropK := by
  unfold xPropK
  infer_instance

end CFSG.KC.EvenSporM22
