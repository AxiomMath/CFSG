module

public import Certificates.Kernel.SmithD6Tr7.Facts
public import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod in
theorem certificate38793 : (∀ k ∈ tr7Gens 4, k < 365211 ∧ tr7RepImg 4 k = k) ∧ wtIdx (tr7Target 4) < 75735 ∧
    (∀ v ∈ tr7Cols32 4, tr7Red (tr7Ech (tr7Cols32 4)) v = 0) ∧
    ∀ m < 2 ^ (tr7Bs32 4).length, tr7XorSel (tr7Bs32 4) m = 0 ∨
      ∀ U : Submodule (ZMod 2) V, (∀ k ∈ tr7Gens 4, ∀ c, decode32 c ∈ U →
        decode32 (applyCols (tvCols k) c) ∈ U) →
        decode32 (tr7XorSel (tr7Bs32 4) m) ∈ U → decode32 (tr7Target 4) ∈ U :=
  SmithD6Tr7.tr7M1_of_pinned (PinnedModel.lineIdx_of_memB pinnedModel)
    (PinnedModel.wtArr_toList pinnedModel) (j := 4) (by simp)

end Certificates
