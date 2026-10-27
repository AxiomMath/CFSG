module

public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data0
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data1
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data2
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data3
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data4
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data5
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data6
public import CFSG.Certificates.Kernel.BabyMonster.FixedLine.Data7

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM.FixedLine

@[expose] noncomputable def Ck : List (List (List Nat)) :=
  [C0.rows, C1.rows, C2.rows, C3.rows, C4.rows, C5.rows, C6.rows, C7.rows, C8.rows, C9.rows,
    C10.rows, C11.rows, C12.rows, C13.rows, C14.rows, C15.rows, C16.rows, C17.rows, C18.rows,
    C19.rows, C20.rows, C21.rows, C22.rows, C23.rows, C24.rows, C25.rows]

end CertificateChecks.KernelBM.Dy

end
