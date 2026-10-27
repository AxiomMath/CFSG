module

public import CFSG.CGT.Timmesfeld75.ListWCMathieuData
import CFSG.Certificates.Kernel.WCK2Sound
import Certificates.Kernel.WCK2.Checks

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.WCK CFSG.KC.S97RYK CFSG.CGT.Timmesfeld75.WCCheck

private theorem m22_mem (l : Int) :
    m22gens l ∈ [m22tA, m22tAi, m22tB, m22tBi, CFSG.Sporadic.Th.Native.idT 22] := by
  unfold m22gens
  split_ifs <;> simp

private theorem m23_mem (l : Int) :
    m23gens l ∈ [m23tA, m23tAi, m23tB, m23tBi, CFSG.Sporadic.Th.Native.idT 23] := by
  unfold m23gens
  split_ifs <;> simp

private theorem m24_mem (l : Int) :
    m24gens l ∈ [m24tA, m24tAi, m24tB, m24tBi, CFSG.Sporadic.Th.Native.idT 24] := by
  unfold m24gens
  split_ifs <;> simp

open CFSG.CGT.Timmesfeld75.WCCheck in
theorem certificate21102 :
    wcCheck m22Data = true ∧ wcCheck m23Data = true ∧ wcCheck m24Data = true :=
  ⟨wcCheck_of_K2 (gens_valid (D := m22Data) m22_mem KernelWCK2.m22_gens) KernelWCK2.m22_ok,
    wcCheck_of_K2 (gens_valid (D := m23Data) m23_mem KernelWCK2.m23_gens) KernelWCK2.m23_ok,
    wcCheck_of_K2 (gens_valid (D := m24Data) m24_mem KernelWCK2.m24_gens) KernelWCK2.m24_ok⟩

end Certificates
