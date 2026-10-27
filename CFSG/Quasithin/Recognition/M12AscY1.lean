module

public import CFSG.Quasithin.Recognition.M12AscWin
public import Certificates.Certificate8950
public import CFSG.Quasithin.Recognition.M12AscCoxData

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

namespace AscCox

variable {m : AscModel z}

theorem u_facts (c : AscCox m) : c.u' * c.u' = 1 ∧ m.ψ mA * c.u' = c.u' * m.ψ mA ∧
    z * c.u' = c.u' * z := by
  obtain ⟨uM, huM, hu'eq⟩ : ∃ uM : ↥ascHModel, (uM = mU ∨ uM = mU * mZ) ∧ c.u' = m.ψ uM := by
    rcases c.hu' with h | h
    · exact ⟨mU, Or.inl rfl, h⟩
    · exact ⟨mU * mZ, Or.inr rfl, h⟩
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := cox_local uM huM
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg m.ψ c1
    simpa only [map_mul, map_one, ← hu'eq] using this
  · have := congrArg m.ψ c4
    simpa only [map_mul, ← hu'eq] using this
  · have := congrArg m.ψ c5
    simpa only [map_mul, m.ψ_hz, ← hu'eq] using this

theorem mem_H (c : AscCox m) : c.u' ∈ ascH z := by
  rcases c.hu' with e | e
  · rw [e]; exact m.ψ_mem mU
  · rw [e]; exact m.ψ_mem _

theorem ρ_pa (c : AscCox m) : c.ρ pa = m.ψ mA := by
  unfold pa
  rw [map_mul, c.ρ_au, c.ρ_u, mul_assoc, c.u_facts.1, mul_one]

theorem ρ_pb (c : AscCox m) : c.ρ pb = c.u' * z := by
  unfold pb
  rw [map_mul, c.ρ_u, c.ρ_z]

theorem ρ_ps (c : AscCox m) : c.ρ ps = z * m.ψ mA := by
  have : ps = swap 0 1 * pa := by unfold ps pa; rfl
  rw [this, map_mul, c.ρ_z, c.ρ_pa]

theorem ρ_pcp (c : AscCox m) :
    c.ρ pcp = (c.u' * m.ψ mX) * m.ψ mA * (c.u' * m.ψ mX) := by
  have h : pcp = swap 3 4 * pa * swap 3 4 := Certificates.certificate8950.1
  rw [h, map_mul, map_mul, c.ρ_ux, c.ρ_pa]

theorem u_notin_Qz [Finite G] (hyp : Asc03Hyp G z) (c : AscCox m) : c.u' ∉ ascQ z := by
  intro h
  have h2 := ((m.mem_ascQ_iff_tb hyp).1 h).2
  rcases c.hu' with e | e
  · rw [e, m.tb_ψ_mU] at h2
    exact uTab_not_q h2
  · rw [e, map_mul, m.ψ_hz, m.tb_mul (m.ψ_mem mU) (z_mem_ascH z), m.tb_ψ_mU, m.tb_z] at h2
    exact uzTab_not_q h2

end AscCox

namespace AscModel

variable {m : AscModel z}

theorem a_mem_F [Finite G] : m.ψ mA ∈ m.fSub := by
  refine m.mem_fSub_iff.2 ⟨m.ψ_mem mA, ?_⟩
  rw [m.tb_ψ mA]
  show tabOf aFPerm ∈ FTabs
  rw [tabOf_aFPerm]
  exact aFTab_mem

theorem a_ne_one : m.ψ mA ≠ 1 := fun h => mA_ne (m.ψ_injective (by rw [h, map_one]))

theorem a_sq : m.ψ mA * m.ψ mA = 1 := by rw [← map_mul, mA_sq, map_one]

theorem exists_conj_a [Finite G] (hyp : Asc03Hyp G z) :
    ∃ c0 : G, c0 * z * c0⁻¹ = m.ψ mA := by
  have haF : m.ψ mA ∈ m.fSub := m.a_mem_F
  exact (m.conj_mem_Q_iff hyp (m.fSub_le_ascQ hyp haF) m.a_ne_one).2 haF

theorem z_ne_a (c : AscCox m) : z ≠ m.ψ mA := by
  intro h
  have : c.ρ (swap 0 1) = c.ρ pa := c.ρ_z.trans (h.trans c.ρ_pa.symm)
  exact absurd (c.ρ_inj this) Certificates.certificate8950.2.1

theorem u_notin_Qa [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (c : AscCox m) :
    c.u' ∉ ascQ (m.ψ mA) := by
  intro hu
  have haQ : m.ψ mA ∈ ascQ z := m.fSub_le_ascQ hyp m.a_mem_F
  obtain ⟨c0, hc0⟩ := exists_conj_a (m := m) hyp
  have hca : IsConj z (m.ψ mA) := isConj_iff.2 ⟨c0, hc0⟩
  have hzQ : z ∈ ascQ z := z_mem_ascQ hyp
  have hcu : IsConj z c.u' := m.outInv_isConj hyp c.mem_H (c.u_notin_Qz hyp) c.u_facts.1
  have hs : IsConj z (z * m.ψ mA) := isConj_iff.2 ⟨c.g, c.g_conj⟩
  have hsQ : z * m.ψ mA ∈ ascQ z := mul_mem hzQ haQ
  have hua : c.u' ≠ m.ψ mA := fun e => c.u_notin_Qz hyp (e ▸ haQ)
  have hsu : z * m.ψ mA ≠ c.u' := fun e => c.u_notin_Qz hyp (e ▸ hsQ)
  have hzu : z ≠ c.u' := fun e => c.u_notin_Qz hyp (e ▸ hzQ)
  have h1 : m.ψ mA ∈ ascQ c.u' := mem_ascQ_symm hyp hca hcu hua.symm hu
  have h2 : z * m.ψ mA ∈ ascQ c.u' := mem_ascQ_symm hyp hs hcu hsu c.u'_Qs
  have h3 : z ∈ ascQ c.u' := by
    have := mul_mem h1 h2
    have e : m.ψ mA * (z * m.ψ mA) = z := by
      calc m.ψ mA * (z * m.ψ mA) = (m.ψ mA * z) * m.ψ mA := by rw [mul_assoc]
        _ = (z * m.ψ mA) * m.ψ mA := by rw [m.ψ_comm_z mA]
        _ = z * (m.ψ mA * m.ψ mA) := by rw [mul_assoc]
        _ = z := by rw [a_sq, mul_one]
    rwa [e] at this
  exact c.u_notin_Qz hyp (mem_ascQ_symm hyp hcu (IsConj.refl z) hzu.symm h3)

theorem exists_y0 [Finite G] [IsSimpleGroup G]
    (hyp : Asc03Hyp G z) (c : AscCox m) :
    ∃ y : G, y * y = m.ψ mA ∧ y * z = (z * m.ψ mA) * y ∧
      y * c.ρ pcp = (m.ψ mA * (c.u' * z)) * y ∧ y * c.u' = (z * c.ρ pcp) * y := by
  obtain ⟨c0, hc0⟩ := exists_conj_a (m := m) hyp
  obtain ⟨ma⟩ : Nonempty (AscModel (m.ψ mA)) := ⟨hc0 ▸ m.conj c0⟩
  have hyp_a : Asc03Hyp G (m.ψ mA) := hc0 ▸ asc03Hyp_conj hyp c0
  have haQ : m.ψ mA ∈ ascQ z := m.fSub_le_ascQ hyp m.a_mem_F
  have hca : IsConj z (m.ψ mA) := isConj_iff.2 ⟨c0, hc0⟩
  have hzQa : z ∈ ascQ (m.ψ mA) := mem_ascQ_symm hyp (IsConj.refl z) hca (z_ne_a c) haQ
  have hzF : z ∈ ma.fSub := ma.zconj_mem_fSub hyp_a hzQa hca.symm
  have hcom_az : z * m.ψ mA = m.ψ mA * z := (m.ψ_comm_z mA).symm
  have h1 : z ∈ ascH (m.ψ mA) := Subgroup.mem_centralizer_singleton_iff.2 hcom_az
  have h3 : c.u' ∈ ascH (m.ψ mA) :=
    Subgroup.mem_centralizer_singleton_iff.2 c.u_facts.2.1.symm
  have h4 : c.ρ pcp ∈ ascH (m.ψ mA) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have := congrArg c.ρ (show pcp * pa = pa * pcp from Certificates.certificate8950.2.2.1)
    rwa [map_mul, map_mul, c.ρ_pa] at this
  have h44 : c.ρ pcp * c.ρ pcp = 1 := by
    have := congrArg c.ρ (show pcp * pcp = 1 from Certificates.certificate8950.2.2.2.1)
    rwa [map_mul, map_one] at this
  have h14 : z * c.ρ pcp = c.ρ pcp * z := by
    have := congrArg c.ρ (show swap 0 1 * pcp = pcp * swap 0 1 from
      Certificates.certificate8950.2.2.2.2.1)
    rwa [map_mul, map_mul, c.ρ_z] at this
  have h43 : c.ρ pcp * c.u' * c.ρ pcp = m.ψ mA * c.u' := by
    have := congrArg c.ρ (show pcp * swap 4 5 * pcp = swap 2 3 from
      Certificates.certificate8950.2.2.2.2.2)
    rwa [map_mul, map_mul, c.ρ_u, c.ρ_au] at this
  obtain ⟨y, -, hyy, hy1, hy4, hy3⟩ := ma.exists_y_window hyp_a h1 h3 h4 c.u_facts.1 h44
    c.u_facts.2.2 h14 h43 (ma.mem_fSub_iff.1 hzF).2 (asc_z_ne_one hyp) (z_ne_a c)
    (u_notin_Qa hyp c)
  exact ⟨y, hyy, hy1, hy4, hy3⟩

end AscModel

end CFSG.Quasithin
