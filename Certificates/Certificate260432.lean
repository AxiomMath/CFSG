module

public import CFSG.Certificates.Kernel.B45IndSound
public import Certificates.Data.Kernel.B45Ind.M24
import Certificates.Kernel.C260432.F0
import Certificates.Kernel.C260432.F1
import Certificates.Kernel.C260432.F2

public section

open CFSG.Quasithin.B45Mat.Ind CFSG.KC.B45Ind

namespace CertificateChecks.Batch260432

open CFSG.Quasithin.B45Mat.Ind CFSG.KC.B45Ind

theorem ts24L_eq : LA m24Ts = ts24L :=
  LA_cosArr _ _ _

theorem coset_eq : m24CosetOK = coset24L := by
  simp only [m24CosetOK, coset24L, cosetOK_eq, ts24L_eq, List.toList_toArray]

theorem flag_eq (i : ℕ) : m24FlagOK i = flag24L i := by
  simp only [m24FlagOK, flagOK, flag24L, invCols_eq]
  congr 1
  funext z
  simp only [m24K, k24L, indCols_eq, ts24L_eq]
  cases z <;> rfl

end CertificateChecks.Batch260432

namespace Certificates

open CertificateChecks.Batch260432 in
open CFSG.Quasithin.B45Mat.Ind in
theorem certificate260432 :
    m24CosetOK = true ∧ m24FlagOK 0 = true ∧ m24FlagOK 1 = true ∧ m24FlagOK 2 = true :=
  ⟨coset_eq.trans CFSG.KD.C260432.coset, (flag_eq 0).trans CFSG.KD.C260432.flag0,
    (flag_eq 1).trans CFSG.KD.C260432.flag1, (flag_eq 2).trans CFSG.KD.C260432.flag2⟩

end Certificates
