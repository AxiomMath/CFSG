module

public import CFSG.Certificates.Kernel.B45NorSound
public import Certificates.Kernel.C260431.Chk
import Certificates.Kernel.C260431.Tr
import Certificates.Kernel.C260431.N1
import Certificates.Kernel.C260431.N2
import Certificates.Kernel.C260431.N3
import Certificates.Kernel.C260431.N4
import Certificates.Kernel.C260431.N5

public section

open CFSG.Quasithin.B45Mat.Ind CFSG.KC.B45Nor CFSG.KD.C260431

namespace CertificateChecks.Batch260431

open CFSG.Quasithin.B45Mat.Ind CFSG.KC.B45Nor CFSG.KD.C260431

theorem std_eq (t : ℕ) :
    (fun z : Bool => if z then m23Std t true else m23Std t false) = m23Std t := by
  funext z
  cases z <;> rfl

theorem nor_of (t : ℕ) (h : nor23K t = true)
    (hT : ∀ b, trChk (m23Std t b) (ht23 t b) 0 = true) : m23NorOK t = true := by
  have e := nortonFastOK_of_norKP h hT
  rw [← std_eq] at e
  exact e

theorem tr3 (b : Bool) : trChk (m23Std 3 b) (ht23 3 b) 0 = true := by
  cases b
  exacts [tr44aA, tr44aB]

theorem tr4 (b : Bool) : trChk (m23Std 4 b) (ht23 4 b) 0 = true := by
  cases b
  exacts [tr44bA, tr44bB]

theorem tr5 (b : Bool) : trChk (m23Std 5 b) (ht23 5 b) 0 = true := by
  cases b
  exacts [tr120A, tr120B]

end CertificateChecks.Batch260431

namespace Certificates

open CertificateChecks.Batch260431 in
open CFSG.Quasithin.B45Mat.Ind in
theorem certificate260431 :
    m23NorOK 1 = true ∧ m23NorOK 2 = true ∧ m23NorOK 3 = true ∧ m23NorOK 4 = true ∧
      m23NorOK 5 = true :=
  ⟨nor_of 1 nor23N1 nor23Tr1, nor_of 2 nor23N2 nor23Tr2, nor_of 3 nor23N3 tr3,
    nor_of 4 nor23N4 tr4, nor_of 5 nor23N5 tr5⟩

end Certificates
