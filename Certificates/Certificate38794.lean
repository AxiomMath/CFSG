module

public import Certificates.Kernel.SmithD6Tr7.Facts
public import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod in
theorem certificate38794 : (∀ k ∈ tr7Gens 5, k < 365211 ∧ tr7RepImg 5 k = k) ∧ wtIdx (tr7Target 5) < 75735 ∧
    (∀ v ∈ tr7Cols32 5, tr7Red (tr7Ech (tr7Cols32 5)) v = 0) ∧
    ∀ m < 2 ^ (tr7Bs32 5).length, tr7XorSel (tr7Bs32 5) m = 0 ∨
      ∀ U : Submodule (ZMod 2) V, (∀ k ∈ tr7Gens 5, ∀ c, decode32 c ∈ U →
        decode32 (applyCols (tvCols k) c) ∈ U) →
        decode32 (tr7XorSel (tr7Bs32 5) m) ∈ U → decode32 (tr7Target 5) ∈ U :=
  SmithD6Tr7.tr7M1_of_pinned (PinnedModel.lineIdx_of_memB pinnedModel)
    (PinnedModel.wtArr_toList pinnedModel) (j := 5) (by simp)

end Certificates
