
module

public import Certificates.Certificate2172Base

public import CFSG.Sporadic.Schreier.J4SInvData
import Certificates.Kernel.SporSch.J4S.InvP

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native in
theorem certificate2172 : (∀ i < 4, comp11 generatorColumns[i]! genInvColumns[i]! = idRows 11)
    ∧ (∀ i < 4, ∀ e < 1024, (conjTab[i]!)[e]! < 1024 ∧
      elementColumns[(conjTab[i]!)[e]!]! =
        comp11 (comp11 generatorColumns[i]! elementColumns[e]!) genInvColumns[i]!
    )
    ∧ (∀ j < 19967, (fN j < 2048 ∧ fE j < 1024 ∧ squares[fE j]! = 0 ∧
      app11 elementColumns[fE j]! (fN j) = fN j ∧ ¬ (fN j = 0 ∧ fE j = 0)) ∧
      ((fP j = j ∧ (fE j = 0 ∨ ambIdx (fN j) (fE j) < 77)) ∨
        (fP j < j ∧ fG j < 5 ∧ genMapN (fG j) (fN (fP j)) (fE (fP j)) = fN j ∧
          genMapE (fG j) (fE (fP j)) = fE j))
    )
    ∧ (∀ e < 1024, ∀ n < 2048,
      (squares[e]! = 0 ∧ app11 elementColumns[e]! n = n ∧ ¬ (n = 0 ∧ e = 0)) →
        (forestIdx[n + 2048 * e]! - 1 < 19967 ∧ fN (forestIdx[n + 2048 * e]! - 1) = n ∧
          fE (forestIdx[n + 2048 * e]! - 1) = e)
    )
    ∧ (∀ i < 77, (ambHead[i]!)[0]! < 2048 ∧ (ambHead[i]!)[1]! < 1024)
    ∧ (ambAllOK KPairs = true) := KernelSporSch.J4InvP.facts

end Certificates
