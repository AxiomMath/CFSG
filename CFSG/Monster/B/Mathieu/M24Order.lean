module

public import CFSG.Monster.B.Mathieu.M24Check

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Certificates CFSG.Sporadic.Mathieu

theorem fam_M24_order :
    ∃ r : GroupRecord, MathieuCertificateK "M24" = some r ∧ r.chain.degree = 24 ∧
      r.chain.generators = [imageList m24gA, imageList m24gB] ∧
      ∃ Q : RawSchreierDatum 24, r.chain.Records Q ∧ ValidSchreier Q ∧
        Q.orderCertificate = 244823040 ∧ Q.originalSubgroup = CFSG.Blueprint.NativeSporadic.M24 ∧
        Nat.card CFSG.Blueprint.NativeSporadic.M24 = 244823040 := by
  obtain ⟨Q, hrec, hQ, hcert, hsub, hcard⟩ :=
    exists_root_chain (N := 244823040) m24_chain_check (by rw [m24_orbitSizes]; rfl) m24_generators
  refine ⟨m24Record, mathieuCertificate_M24, hrec.1, m24_generators, Q, hrec, hQ, hcert, ?_, ?_⟩
  · rw [hsub, m24_eq]
  · rw [m24_eq, hcard]

end CFSG.Monster.B.Mathieu
