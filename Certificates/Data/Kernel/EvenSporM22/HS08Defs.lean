module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HCheck
public import Certificates.Data.Kernel.EvenSporM22.E32Defs

public section

namespace CFSG.KC.EvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.HS08Check

@[expose] def jGensW : List (List Nat) :=
  [[0], [2, 6, 7], [0, 1, 2, 3, 5, 7], [0, 3, 6, 7], [0, 4, 7]]

@[expose] def jLit : List Tab := isortK (span (jGensW.map (wordTab s0Gens)))

@[expose] def JOK (L : List Tab) : Prop :=
  L.length = 32 ∧ L.Nodup ∧ idTab ∈ L ∧
    ∀ a ∈ L, a ∈ s0Tabs ∧ tmul a a = idTab ∧ ∀ b ∈ L, tmul a b ∈ L ∧ comm a b = true

instance (L : List Tab) : Decidable (JOK L) := by
  unfold JOK
  infer_instance

@[expose] def OutInvPropJ (J : List Tab) : Prop :=
  ∀ v ∈ s0Outer, tmul v v = idTab → ∃ w ∈ owWords, ∃ j ∈ J,
    tmul (wordTab letterTabs4 w) v = tmul j (wordTab letterTabs4 w)

instance (J : List Tab) : Decidable (OutInvPropJ J) := by
  unfold OutInvPropJ
  infer_instance

@[expose] def ConjPropJ (J : List Tab) : Prop :=
  cPairs.length = 231 ∧ (∀ p ∈ cPairs, tmul p.1 p.2 = idTab) ∧
  cPairs.Pairwise fun p q => ∃ x ∈ J, tmul (tmul (tmul p.2 q.1) x) (tmul q.2 p.1) ∉ J

instance (J : List Tab) : Decidable (ConjPropJ J) := by
  unfold ConjPropJ
  infer_instance

end CFSG.KC.EvenSporM22
