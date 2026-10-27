module

public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.G24IdentPc
import Certificates.Kernel.PresLetters.F733004
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.Quasithin.St84 CFSG.KC.MiscCoset

namespace Certificates

theorem certificate733004 : (Finite (CFSG.CosetTable.PG 3 CFSG.Quasithin.St84.G24Pc.relsA) ∧
      Nat.card (CFSG.CosetTable.PG 3 CFSG.Quasithin.St84.G24Pc.relsA) ≤ 180) ∧
    (Finite (CFSG.CosetTable.PG 10 CFSG.Quasithin.St84.G24Pc.relsQ1) ∧
      Nat.card (CFSG.CosetTable.PG 10 CFSG.Quasithin.St84.G24Pc.relsQ1) ≤ 1024) ∧
    (Finite (CFSG.CosetTable.PG 10 CFSG.Quasithin.St84.G24Pc.relsQ2) ∧
      Nat.card (CFSG.CosetTable.PG 10 CFSG.Quasithin.St84.G24Pc.relsQ2) ≤ 1024) :=
  ⟨TableFact.card G24Pc.relsA (by norm_num) CFSG.KBFact.F733004a,
    TableFact.card G24Pc.relsQ1 (by norm_num) CFSG.KBFact.F733004b,
    TableFact.card G24Pc.relsQ2 (by norm_num) CFSG.KBFact.F733004c⟩

end Certificates
