module

public import Certificates.Data.GHarrisA5Data
import Certificates.Kernel.GHarrisA5.Words
import Certificates.Kernel.GHarrisA5.IsoGlue
import Certificates.Kernel.GHarrisA5.Norm

public section

namespace Certificates

open CertificateChecks.KernelGHarrisA5

open CFSG.ComponentClassification.GHarris in
theorem certificate22613 :
    (∀ k ∈ List.range 70, (GL42.witAt k).isOrbit = true → k ∈ GL42.orbitKs) ∧
    (∀ k ∈ GL42.orbitKs, GL42.a5Idx k < 4 ∧
      (∀ e ∈ GL42.e0c, e ∈ GL42.a5At (GL42.a5Idx k)) ∧
      (∀ c ∈ GL42.conjAt k, c ∈ GL42.a5At (GL42.a5Idx k)) ∧
      (GL42.a5At (GL42.a5Idx k)).length = 60 ∧
      ∀ i ∈ List.range 60, GL42.wordProd (GL42.e0c ++ GL42.conjAt k) ((GL42.wordsAt k).getD i []) =
        (GL42.a5At (GL42.a5Idx k)).getD i GL42.M4c.one) ∧
    (∀ j ∈ List.range 4,
      (∀ p q : alternatingGroup (Fin 5),
        GL42.phiA5 j (p * q) = (GL42.phiA5 j p).mul (GL42.phiA5 j q)) ∧
      (∀ p : alternatingGroup (Fin 5), GL42.phiA5 j p = GL42.M4c.one → p = 1) ∧
      (∀ p : alternatingGroup (Fin 5), GL42.phiA5 j p ∈ GL42.a5At j) ∧
      ∀ c ∈ GL42.a5At j, ∃ p : alternatingGroup (Fin 5), GL42.phiA5 j p = c) ∧
    (∀ k ∈ GL42.orbitKs, ∀ k' ∈ GL42.orbitKs, GL42.a5Idx k ≠ GL42.a5Idx k' →
      GL42.IsOrder4 (GL42.wordProd (GL42.e0c ++ GL42.conjAt k ++ GL42.conjAt k')
        (GL42.pairWord k k'))) ∧
    (∀ a ∈ GL42.rowsW, ∀ b ∈ GL42.rowsW, ∀ c ∈ GL42.V4c.all, ∀ d ∈ GL42.V4c.all,
      GL42.NoFiveSeven ⟨a, b, c, d⟩) :=
  ⟨orbit_ok, words_ok, iso_ok, pairs_ok, norm_ok⟩

end Certificates
