module

public import Certificates.Kernel.SmithD6Tr7.Facts
public import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod in
theorem certificate38792 : ∀ j, j = 0 ∨ j = 1 ∨ j = 3 →
    (∀ k ∈ tr7Gens j, k < 365211 ∧ tr7RepImg j k = k) ∧ wtIdx (tr7Target j) < 75735 ∧
    (∀ v ∈ tr7Cols32 j, tr7Red (tr7Ech (tr7Cols32 j)) v = 0) ∧
    ∀ m < 2 ^ (tr7Bs32 j).length, tr7XorSel (tr7Bs32 j) m = 0 ∨
      ∀ U : Submodule (ZMod 2) V, (∀ k ∈ tr7Gens j, ∀ c, decode32 c ∈ U →
        decode32 (applyCols (tvCols k) c) ∈ U) →
        decode32 (tr7XorSel (tr7Bs32 j) m) ∈ U → decode32 (tr7Target j) ∈ U :=
  fun _ hj => SmithD6Tr7.tr7M1_of_pinned (PinnedModel.lineIdx_of_memB pinnedModel)
    (PinnedModel.wtArr_toList pinnedModel) (by rcases hj with h | h | h <;> simp [h])

end Certificates
