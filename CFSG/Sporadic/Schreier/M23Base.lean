
module

public import CFSG.Sporadic.Schreier.M23Pinned
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Schreier.M23Data
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Th.GroupTheory
public import Certificates.Data.CFSGNative.SporadicSchreier.Count

@[expose] public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem fam_m23_order :
    ∃ r : GroupRecord, MathieuCertificateK "M23" = some r ∧ r.chain.degree = 23 ∧
      r.chain.generators = [imageList m23PermA, imageList m23PermB] ∧
      ∃ Q : RawSchreierDatum 23, r.chain.Records Q ∧ ValidSchreier Q ∧
        Q.orderCertificate = 10200960 ∧ Q.originalSubgroup = NativeSporadic.M23 ∧
        Nat.card NativeSporadic.M23 = 10200960 := by
  obtain ⟨Q, hrec, hQ, hcert, hsub, hcard⟩ := exists_root_chain (N := 10200960)
    m23_chain_check (by rw [m23_orbitSizes]; rfl) m23_generators
  refine ⟨m23Record, mathieuCertificate_M23, hrec.1, m23_generators, Q, hrec, hQ, hcert, ?_, ?_⟩
  · rw [hsub, m23_eq_closure]
  · rw [m23_eq_closure, hcard]

theorem m23_card : Nat.card NativeSporadic.M23 = 10200960 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := fam_m23_order
  exact h

theorem m23Certificate_originalSubgroup :
    m23Certificate.originalSubgroup = NativeSporadic.M23 := by
  rw [m23Certificate, certificate_originalSubgroup, m23_eq_closure]
  congr 1
  ext g
  simp

end CFSG.Sporadic.Schreier
