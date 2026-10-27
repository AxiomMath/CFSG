module

public import CFSG.LargeExtraspecial.S97RYData
import CFSG.Certificates.Kernel.S97RYKSound
import Certificates.Kernel.S97RYK.Checks

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.S97RYK CFSG.LargeExtraspecial.S11.PairCheck CFSG.CGT.Timmesfeld75.WCCheck

private theorem a9_mem (l : Int) : a9gens l ∈ [a9tA, a9tAi, a9tB, a9tBi, CFSG.Sporadic.Th.Native.idT 9] := by
  unfold a9gens
  split_ifs <;> simp

private theorem m22_mem (l : Int) :
    m22gens l ∈ [m22tA, m22tAi, m22tB, m22tBi, CFSG.Sporadic.Th.Native.idT 22] := by
  unfold m22gens
  split_ifs <;> simp

open CFSG.LargeExtraspecial.S11.PairCheck in
theorem certificate21103 :
    pairCheck a9PData = true ∧ pairCheck m22PData = true :=
  ⟨pairCheck_of_K (gens_valid (D := a9PData.D) a9_mem KernelS97RY.a9_gens) KernelS97RY.a9_ok,
    pairCheck_of_K (gens_valid (D := m22PData.D) m22_mem KernelS97RY.m22_gens) KernelS97RY.m22_ok⟩

end Certificates
