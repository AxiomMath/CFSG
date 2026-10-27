module

public import Certificates.Data.G23RecogGluePresentationInputs
import Certificates.Kernel.PresLetters.F320008
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

open CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

namespace Certificates

open CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable in
theorem certificate320008 : Finite (PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5) ∧
    Nat.card (PG (subsetOf 6 [0, 1, 2, 3, 4]).length g23H5) ≤ 576 :=
  CFSG.KC.MiscCoset.TableFact.card g23H5 (by decide) CFSG.KBFact.F320008

end Certificates
