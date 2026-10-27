module

public import Certificates.Data.Kernel.D43.Tree
public import Certificates.Kernel.D43.TreeData
public import Certificates.Kernel.D43.HexG
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43 CFSG.KC.Enum

abbrev D43BX : Nat := 121695702607180549954634604969984

abbrev D43BB : Nat := 3458816788738179078

theorem fixX : (fixAll GX.F TW D43BX 0 0 131071 && fixAll GX.F TW D43BX 1 0 131069 &&
    fixAll GX.F TW D43BX 2 0 253 && fixAll GX.F TW D43BX 3 0 252 &&
    fixAll GX.F TW D43BX 4 0 252 && fixAll GX.F TW D43BX 5 0 28 &&
    fixAll GX.F TW D43BX 6 0 28 && fixAll GX.F TW D43BX 7 0 24) = true := by
  decide +kernel

theorem fixB : (fixAll GX.F TW D43BB 0 2 131068 && fixAll GX.F TW D43BB 1 2 130812 &&
    fixAll GX.F TW D43BB 2 2 252 && fixAll GX.F TW D43BB 3 2 28 &&
    fixAll GX.F TW D43BB 4 2 24) = true := by
  decide +kernel

theorem treeX2 : treeChunk GX.F TW TR TQ 2 46255 28 6 253 0 = true := by decide +kernel
theorem treeX3 : treeChunk GX.F TW TR TQ 3 46283 1 479 252 0 = true := by decide +kernel
theorem treeX4 : treeChunk GX.F TW TR TQ 4 46284 27 15916 252 0 = true := by decide +kernel
theorem treeX5 : treeChunk GX.F TW TR TQ 5 46311 1 186 28 0 = true := by decide +kernel
theorem treeX6 : treeChunk GX.F TW TR TQ 6 46312 2 1 28 0 = true := by decide +kernel
theorem treeX7 : treeChunk GX.F TW TR TQ 7 46314 26 3 24 0 = true := by decide +kernel
theorem treeB0 : treeChunk GX.F TW TR TQ 8 46340 3 6 131068 0 = true := by decide +kernel
theorem treeB2 : treeChunk GX.F TW TR TQ 10 52904 27 15916 252 0 = true := by decide +kernel
theorem treeB3 : treeChunk GX.F TW TR TQ 11 52931 2 1 28 0 = true := by decide +kernel
theorem treeB4 : treeChunk GX.F TW TR TQ 12 52933 26 3 24 0 = true := by decide +kernel

@[expose] noncomputable def treeD43b1 (c : Nat) : Bool :=
  treeChunk GX.F TW TR TQ (nat_lit 9) (nat_lit 46343) (nat_lit 6561) (nat_lit 26571)
    (nat_lit 130812) c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.treeD43b1 0 26 1 as CertificateChecks.KernelD43.d43treeb1_

namespace CertificateChecks.KernelD43

open CFSG.KC.D43 CFSG.KC.Enum

#kc_forall_chunks treeB1 (fun c => treeD43b1 c = true) 26 CertificateChecks.KernelD43.d43treeb1_ 1

theorem negTreeR : (!treeChunk GX.F TW (patchT TR 0 (TR 1)) TQ 0 0 26572 0 131071 0) = true := by
  decide +kernel

theorem negTreeQ : (!treeChunk GX.F TW TR (patchT TQ 0 (TQ 1)) 0 0 26572 0 131071 0) = true := by
  decide +kernel

theorem negTreeM : (!fixAll GX.F TW D43BX 0 0 130815 &&
    !treeChunk GX.F TW TR TQ 0 0 26572 0 130815 0) = true := by
  decide +kernel

end CertificateChecks.KernelD43

end
