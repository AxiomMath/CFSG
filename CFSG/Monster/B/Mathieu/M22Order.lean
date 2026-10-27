module

public import CFSG.Monster.B.Mathieu.M22Check

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Certificates CFSG.Sporadic.Mathieu

theorem fam_M22_order :
    ∃ r : GroupRecord, MathieuCertificateK "M22" = some r ∧ r.chain.degree = 22 ∧
      r.chain.generators = [imageList m22gA, imageList m22gB] ∧
      ∃ Q : RawSchreierDatum 22, r.chain.Records Q ∧ ValidSchreier Q ∧
        Q.orderCertificate = 443520 ∧ Q.originalSubgroup = CFSG.Blueprint.NativeSporadic.M22 ∧
        Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := by
  obtain ⟨Q, hrec, hQ, hcert, hsub, hcard⟩ :=
    exists_root_chain (N := 443520) m22_chain_check (by rw [m22_orbitSizes]; rfl) m22_generators
  refine ⟨m22Record, mathieuCertificate_M22, hrec.1, m22_generators, Q, hrec, hQ, hcert, ?_, ?_⟩
  · rw [hsub, m22_eq]
  · rw [m22_eq, hcard]

end CFSG.Monster.B.Mathieu
