module

public import Certificates.Data.GrSLitL34FactsFourCubeData
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.PresLetters.F22217
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import Mathlib.Algebra.Order.Ring.Star

public section

open CFSG.ComponentClassification.GrSLit.L34Facts.FourCube CFSG.CosetTable

namespace Certificates

open CFSG.ComponentClassification.GrSLit.L34Facts.FourCube CFSG.CosetTable in
theorem certificate22217 : (Finite (PG 5 (qRels 0)) ∧ Nat.card (PG 5 (qRels 0)) ≤ 512) ∧
    (Finite (PG 5 (qRels d1)) ∧ Nat.card (PG 5 (qRels d1)) ≤ 512) :=
  ⟨CFSG.KC.MiscCoset.TableFact.card (qRels 0) (by norm_num) CFSG.KBFact.F22217a,
    CFSG.KC.MiscCoset.TableFact.card (qRels d1) (by norm_num) CFSG.KBFact.F22217b⟩

end Certificates
