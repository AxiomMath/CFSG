module

public import CFSG.Sporadic.Recognition.JankoWongSec4VAct
public import CFSG.Sporadic.Recognition.JankoWongPresCert
public import CFSG.Sporadic.Recognition.JankoWongSec4K

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

namespace Setup

variable {G : Type} [Group G] [Finite G]

section Certs


theorem exists_jwRelations (S : Setup G) :
    ∃ (ι : ℤˣ) (e : JWElements G), JWRelations ι e ∧ Subgroup.closure e.gens ≠ ⊥ := by
  obtain ⟨c⟩ := S.exists_ctx
  obtain ⟨W, hW⟩ := c.exists_isW
  obtain ⟨a₁, v, v₁, h⟩ := c.exists_sec4Hyp
  obtain ⟨φ₁, hmem, hne, hz, ht⟩ := c.exists_phi₁
  have hφ : Phi1 c φ₁ := ⟨hmem, hne, hz, ht⟩
  obtain ⟨i, hi, hX1, hX2⟩ := hφ.exists_v1_action h
  obtain ⟨h18, h19⟩ := hφ.rel_7_8 h hW
  have h23 := hφ.phi3_by_v1 h hW hi hX1 hX2 h19
  obtain ⟨ι, hι⟩ : ∃ ι : ℤˣ, (ι : ℤ) = i := by
    rcases hi with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨-1, rfl⟩
  have h18' : cj (phi3 c a₁ φ₁) (cj (c.a : G) (c.t : G)) = φ₁⁻¹ * phi3 c a₁ φ₁ * (c.a : G) := by
    rw [c.cj_a_t]
    exact h18
  have hz' : cj φ₁ (a₁ ^ 2) = φ₁⁻¹ := by rw [h.a1_sq]; exact hφ.by_z
  have hcube' : ((c.t : G) * a₁ ^ 2 * phi3 c a₁ φ₁) ^ 3 = 1 := by
    rw [h.a1_sq]
    exact hφ.u_z_phi3_cube h hW
  refine ⟨ι, ⟨a₁, (c.a : G), (c.t : G), v, v₁, φ₁⟩, ?_, ?_⟩
  · exact
      { sigma1_cube := h.rel.sigma1_cube
        b1_sq := h.rel.b1_sq
        a1_by_v := h.rel.a1_by_v
        b1_by_sigma1 := h.rel.b1_by_sigma1
        a2_sq := h.rel.a2_sq
        a2_by_v := h.rel.a2_by_v
        sigma2_by_v := h.rel.sigma2_by_v
        a1_a2_comm := cmt_eq_one_iff'.mpr h.rel.a1_a2_comm
        a1_sigma2_comm := cmt_eq_one_iff'.mpr h.rel.a1_sigma2_comm
        sigma1_sigma2_comm := cmt_eq_one_iff'.mpr h.rel.sigma1_sigma2_comm
        v_sq := h.rel.v_sq
        u_sq := h.rel.u_sq
        v_by_u := h.rel.v_by_u
        v1_a2_cube := h.rel.v1_a2_cube
        v1_u_sq := h.rel.v1_u_sq
        phi1_by_z := hz'
        phi1_by_u := hφ.by_t
        phi3_by_sigma2 := h18'
        phi1_by_phi3 := h19
        phi1_phi4_comm := (hφ.cmt14_eq_one h hW).1
        u_z_phi3_cube := hcube'
        u_v_phi3_phi4_cube := hφ.u_v_phi3_phi4_cube h hW
        phi3_by_v1 := by rw [hι]; exact h23 }
  · intro hbot
    have hmem : (c.a : G) ∈ Subgroup.closure
        (JWElements.gens ⟨a₁, (c.a : G), (c.t : G), v, v₁, φ₁⟩) :=
      Subgroup.subset_closure (Or.inr (Or.inl rfl))
    rw [hbot, Subgroup.mem_bot] at hmem
    exact c.aG_ne_one hmem

theorem exists_subgroup_mulEquiv_mcl
    (S : Setup G) :
    ∃ H : Subgroup G, Nonempty (↥H ≃* CFSG.Blueprint.NativeSporadic.McL) := by
  obtain ⟨ι, e, hrel, hK⟩ := S.exists_jwRelations
  exact ⟨Subgroup.closure e.gens, exists_mulEquiv_mcl_of_relations_of_certificate hrel hK⟩

end Certs

end Setup

end CFSG.Sporadic.Recognition.JankoWong
