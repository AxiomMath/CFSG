module

public import CFSG.Monster.Schur.TripleM12Words
import Certificates.Kernel.CosetCC.C9700A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.CosetTablePresented
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.Monster.Schur CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

private theorem certificate9700_rels_eq : m12Rels.map encW = CFSG.KBRoute.F9700.rels := by
  decide +kernel

open CFSG.Monster.Schur CFSG.CosetTable in
theorem certificate9700 : Finite (PG 3 m12Rels) ∧ Nat.card (PG 3 m12Rels) ≤ 95040 := by
  have h := CFSG.KBFact.F9700
  rw [← certificate9700_rels_eq] at h
  exact TableFact.card m12Rels (by norm_num) h

end Certificates
