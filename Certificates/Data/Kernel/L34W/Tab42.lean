module

public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverCertInputs
public import Certificates.Data.GrSLitL34FactsRealReps
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Open.Defs

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] noncomputable def pword (G : Nat → Nat) (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun j _ ih p => strictN (pcomp (nat_lit 42) (nat_lit 6) (mask 6) p (G j)) ih) w p

@[expose] noncomputable def gS (G : Nat → Nat) (j : Nat) : Nat :=
  G (nIf(Nat.beq j (nat_lit 0), nat_lit 0, nIf(Nat.beq j (nat_lit 1), nat_lit 1, nat_lit 2)))

@[expose] noncomputable def tgK (G : Nat → Nat) (t : Nat) : Nat :=
  pword (gS G) (tg t) (pidn (nat_lit 42) (nat_lit 6))

@[expose] noncomputable def repK (G : Nat → Nat) (i : Nat) : Nat :=
  pword G (realRepWords.getD i []) (pidn (nat_lit 42) (nat_lit 6))

@[expose] noncomputable def yK (G : Nat → Nat) (t i : Nat) : Nat :=
  pcomp (nat_lit 42) (nat_lit 6) (mask 6) (tgK G t) (repK G i)

end CFSG.KC.L34W

end
