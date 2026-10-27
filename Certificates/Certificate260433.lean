module

public import CFSG.Certificates.Kernel.B45NorSound
public import Certificates.Kernel.C260433.Chk
import Certificates.Kernel.C260433.Tr
import Certificates.Kernel.C260433.N1
import Certificates.Kernel.C260433.N2
import Certificates.Kernel.C260433.N3
import Certificates.Kernel.C260433.N4
import Certificates.Kernel.C260433.N5

public section

open CFSG.Quasithin.B45Mat.Ind CFSG.KC.B45Nor CFSG.KD.C260433

namespace CertificateChecks.Batch260433

open CFSG.Quasithin.B45Mat.Ind CFSG.KC.B45Nor CFSG.KD.C260433

theorem std_eq (t : ℕ) :
    (fun z : Bool => if z then m24Std t true else m24Std t false) = m24Std t := by
  funext z
  cases z <;> rfl

theorem nor_of (t : ℕ) (h : nor24K t = true)
    (hT : ∀ b, trChk (m24Std t b) (ht24 t b) 0 = true) : m24NorOK t = true := by
  have e := nortonFastOK_of_norKP h hT
  rw [← std_eq] at e
  exact e

theorem tr3 (b : Bool) : trChk (m24Std 3 b) (ht24 3 b) 0 = true := by
  cases b
  exacts [tr44aA, tr44aB]

theorem tr4 (b : Bool) : trChk (m24Std 4 b) (ht24 4 b) 0 = true := by
  cases b
  exacts [tr44bA, tr44bB]

theorem tr5 (b : Bool) : trChk (m24Std 5 b) (ht24 5 b) 0 = true := by
  cases b
  exacts [tr120A, tr120B]

end CertificateChecks.Batch260433

namespace Certificates

open CertificateChecks.Batch260433 in
open CFSG.Quasithin.B45Mat.Ind in
theorem certificate260433 :
    m24NorOK 1 = true ∧ m24NorOK 2 = true ∧ m24NorOK 3 = true ∧ m24NorOK 4 = true ∧
      m24NorOK 5 = true :=
  ⟨nor_of 1 nor24N1 nor24Tr1, nor_of 2 nor24N2 nor24Tr2, nor_of 3 nor24N3 tr3,
    nor_of 4 nor24N4 tr4, nor_of 5 nor24N5 tr5⟩

end Certificates
