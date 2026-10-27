module

public import CFSG.ClassicalInvolution.Q3.Q3ZWords
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.PresLetters.F17352
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.Q3Z

namespace Certificates

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.Q3Z in
theorem certificate17352 : Finite (PG 6 a2Words) ∧ Nat.card (PG 6 a2Words) ≤ 5616 :=
  CFSG.KC.MiscCoset.TableFact.card a2Words (by norm_num) CFSG.KBFact.F17352

end Certificates
