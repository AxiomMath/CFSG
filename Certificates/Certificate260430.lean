module

public import CFSG.Certificates.Kernel.B45IndSound
public import Certificates.Data.Kernel.B45Ind.M23
import Certificates.Kernel.C260430.F0
import Certificates.Kernel.C260430.F1
import Certificates.Kernel.C260430.F2

public section

open CFSG.Quasithin.B45Mat.Ind CFSG.KC.B45Ind

namespace CertificateChecks.Batch260430

open CFSG.Quasithin.B45Mat.Ind CFSG.KC.B45Ind

theorem ts23L_eq : LA m23Ts = ts23L :=
  LA_cosArr _ _ _

theorem coset_eq : m23CosetOK = coset23L := by
  simp only [m23CosetOK, coset23L, cosetOK_eq, ts23L_eq]

theorem flag_eq (i : ℕ) : m23FlagOK i = flag23L i := by
  simp only [m23FlagOK, flagOK, flag23L, invCols_eq]
  congr 1
  funext z
  simp only [m23K, k23L, indCols_eq, ts23L_eq]
  cases z <;> rfl

end CertificateChecks.Batch260430

namespace Certificates

open CertificateChecks.Batch260430 in
open CFSG.Quasithin.B45Mat.Ind in
theorem certificate260430 :
    m23CosetOK = true ∧ m23FlagOK 0 = true ∧ m23FlagOK 1 = true ∧ m23FlagOK 2 = true :=
  ⟨coset_eq.trans CFSG.KD.C260430.coset, (flag_eq 0).trans CFSG.KD.C260430.flag0,
    (flag_eq 1).trans CFSG.KD.C260430.flag1, (flag_eq 2).trans CFSG.KD.C260430.flag2⟩

end Certificates
