module

public import CFSG.Sporadic.Recognition.JankoWongSec4Comm
public import CFSG.Sporadic.Recognition.JankoWongSec4A4
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCoreQuotient

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

omit [Finite G] in
theorem cj_inv_of_cj {x y A : G} (hA : A * y = y * A) (e : cj x y = x * A) :
    cj x y⁻¹ = x * A⁻¹ := by
  have hA' : A⁻¹ * y = y * A⁻¹ := (Commute.inv_left (show Commute A y from hA)).eq
  have e1 : cj (x * A⁻¹) y = x := by
    rw [cj_mul_left, e, cj_eq_self_of_comm hA']
    group
  calc cj x y⁻¹ = cj (cj (x * A⁻¹) y) y⁻¹ := by rw [e1]
    _ = x * A⁻¹ := cj_cj_inv _ _

section NoCerts

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} (h : Sec4Hyp c a₁ v v₁)

omit [Finite G] in
theorem cmt_eq_one_iff' {x y : G} : cmt x y = 1 ↔ x * y = y * x := by
  unfold cmt
  constructor
  · intro e
    calc x * y = y * (y⁻¹ * x * y) := by group
      _ = y * x := by
        have : y⁻¹ * x * y = x := by
          calc y⁻¹ * x * y = x * (x⁻¹ * y⁻¹ * x * y) := by group
            _ = x := by rw [e, mul_one]
        rw [this]
  · intro e
    calc x⁻¹ * y⁻¹ * x * y = (y * x)⁻¹ * (x * y) := by group
      _ = 1 := by rw [e]; group

include h in
theorem Sec4Hyp.t_comm_u : (c.t : G) * cj (c.t : G) (c.a2 a₁) =
    cj (c.t : G) (c.a2 a₁) * (c.t : G) := by
  have ht : (c.t : G)⁻¹ = c.t := c.tG_inv
  have htt : (c.t : G) * c.t = 1 := by rw [← pow_two]; exact c.tG_sq'
  have R2 : (c.t : G) * a₁ * c.t = c.a2 a₁ := by
    unfold Ctx.a2 cj; rw [ht]
  have R2' : (c.t : G) * c.a2 a₁ * c.t = a₁ := by
    rw [← R2]
    calc (c.t : G) * ((c.t : G) * a₁ * c.t) * c.t = ((c.t : G) * c.t) * a₁ * ((c.t : G) * c.t) :=
          by group
      _ = a₁ := by rw [htt]; group
  have R3 : a₁ * c.a2 a₁ = c.a2 a₁ * a₁ := h.rel.a1_a2_comm
  have e1 : (c.t : G) * (c.a2 a₁)⁻¹ * c.t = a₁⁻¹ := by
    calc (c.t : G) * (c.a2 a₁)⁻¹ * c.t = ((c.t : G) * c.a2 a₁ * c.t)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, ht]; group
      _ = a₁⁻¹ := by rw [R2']
  have e2 : a₁⁻¹ * c.a2 a₁ = (c.a2 a₁)⁻¹ * a₁ := by
    rw [h.a1_inv, h.a2_inv]
    calc a₁ * S.z * c.a2 a₁ = a₁ * (S.z * c.a2 a₁) := by group
      _ = a₁ * (c.a2 a₁ * S.z) := by rw [h.a2_comm_z]
      _ = (a₁ * c.a2 a₁) * S.z := by group
      _ = (c.a2 a₁ * a₁) * S.z := by rw [R3]
      _ = c.a2 a₁ * (a₁ * S.z) := by group
      _ = c.a2 a₁ * (S.z * a₁) := by rw [h.a1_comm_z]
      _ = c.a2 a₁ * S.z * a₁ := by group
  unfold cj
  calc (c.t : G) * ((c.a2 a₁)⁻¹ * c.t * c.a2 a₁)
      = ((c.t : G) * (c.a2 a₁)⁻¹ * c.t) * c.a2 a₁ := by group
    _ = a₁⁻¹ * c.a2 a₁ := by rw [e1]
    _ = (c.a2 a₁)⁻¹ * a₁ := e2
    _ = (c.a2 a₁)⁻¹ * ((c.t : G) * c.a2 a₁ * c.t) := by rw [R2']
    _ = ((c.a2 a₁)⁻¹ * c.t * c.a2 a₁) * c.t := by group

theorem Sec4Hyp.u_sq : cj (c.t : G) (c.a2 a₁) ^ 2 = 1 := by
  rw [← cj_pow_left, c.tG_sq', cj_one_left]

theorem Sec4Hyp.u_ne_one : cj (c.t : G) (c.a2 a₁) ≠ 1 := fun e =>
  c.tG_ne_one (cj_injective_left (c.a2 a₁) (by
    show cj (c.t : G) (c.a2 a₁) = cj 1 (c.a2 a₁); rw [e, cj_one_left]))

include h in
theorem Sec4Hyp.u_mem_H : cj (c.t : G) (c.a2 a₁) ∈ S.H :=
  S.H.mul_mem (S.H.mul_mem (S.H.inv_mem h.a2_mem) c.t.2) h.a2_mem

include h in
theorem Sec4Hyp.z_comm_u : S.z * cj (c.t : G) (c.a2 a₁) = cj (c.t : G) (c.a2 a₁) * S.z :=
  (Ctx.zc h.u_mem_H).symm

variable (hφ : Phi1 c φ₁)

include hφ in
theorem Phi1.phi3_comm_u : phi3 c a₁ φ₁ * cj (c.t : G) (c.a2 a₁) =
    cj (c.t : G) (c.a2 a₁) * phi3 c a₁ φ₁ := by
  have e : c.a2 a₁ * cj (c.t : G) (c.a2 a₁) = (c.t : G) * c.a2 a₁ := by unfold cj; group
  have : cj (phi3 c a₁ φ₁) (cj (c.t : G) (c.a2 a₁)) = phi3 c a₁ φ₁ := by
    rw [cj_cj, e, cj_mul_right, hφ.by_t]
  exact comm_of_cj_eq this

theorem Ctx.a2_mul_t (c : Ctx S) (a₁ : G) : c.a2 a₁ * (c.t : G) = (c.t : G) * a₁ := by
  have ht : (c.t : G)⁻¹ = c.t := c.tG_inv
  have htt : (c.t : G) * c.t = 1 := by rw [← pow_two]; exact c.tG_sq'
  unfold Ctx.a2 cj
  rw [ht]
  calc (c.t : G) * a₁ * c.t * c.t = (c.t : G) * a₁ * (c.t * c.t) := by group
    _ = (c.t : G) * a₁ := by rw [htt, mul_one]

theorem Ctx.cj_a2_t (c : Ctx S) (a₁ : G) : cj (c.a2 a₁) (c.t : G) = a₁ := by
  have htt : (c.t : G) * c.t = 1 := by rw [← pow_two]; exact c.tG_sq'
  unfold cj
  rw [c.tG_inv]
  calc (c.t : G) * c.a2 a₁ * c.t = (c.t : G) * (c.a2 a₁ * c.t) := by group
    _ = (c.t : G) * ((c.t : G) * a₁) := by rw [Ctx.a2_mul_t c a₁]
    _ = ((c.t : G) * c.t) * a₁ := by group
    _ = a₁ := by rw [htt, one_mul]

include h in
theorem Sec4Hyp.a1_mul_v : a₁ * v = v * a₁⁻¹ := by
  have e : v⁻¹ * a₁ * v = a₁⁻¹ := h.rel.a1_by_v
  calc a₁ * v = v * (v⁻¹ * a₁ * v) := by group
    _ = v * a₁⁻¹ := by rw [e]

include h in
theorem Sec4Hyp.a2_mul_v' : c.a2 a₁ * v = v * (c.a2 a₁)⁻¹ := h.a2_mul_v

include h in
theorem Sec4Hyp.e_sq : (a₁ * c.a2 a₁) * (a₁ * c.a2 a₁) = 1 := by
  have hc : Commute a₁ (c.a2 a₁) := h.rel.a1_a2_comm
  rw [← pow_two, hc.mul_pow, h.a1_sq, h.a2_sq]
  exact Ctx.z_mul_z (S := S)

include h in
theorem Sec4Hyp.tv_sq : ((c.t : G) * v) * ((c.t : G) * v) = 1 := by
  have ht : (c.t : G)⁻¹ = c.t := c.tG_inv
  have e : (c.t : G)⁻¹ * v * c.t = v⁻¹ := h.rel.v_by_u
  rw [ht] at e
  calc ((c.t : G) * v) * ((c.t : G) * v) = ((c.t : G) * v * c.t) * v := by group
    _ = 1 := by rw [e]; group

include h in
theorem Sec4Hyp.tv_comm_e :
    ((c.t : G) * v) * (a₁ * c.a2 a₁) = (a₁ * c.a2 a₁) * ((c.t : G) * v) := by
  have hcj : cj (a₁ * c.a2 a₁) ((c.t : G) * v) = a₁ * c.a2 a₁ := by
    have e1 : cj (a₁ * c.a2 a₁) (c.t : G) = c.a2 a₁ * a₁ := by
      rw [cj_mul_left, Ctx.cj_a2_t c a₁]
      rfl
    rw [cj_mul_right, e1, cj_mul_left]
    have e2 : cj (c.a2 a₁) v = (c.a2 a₁)⁻¹ := h.rel.a2_by_v
    have e3 : cj a₁ v = a₁⁻¹ := h.rel.a1_by_v
    rw [e2, e3, ← mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right h.e_sq
  exact (comm_of_cj_eq hcj).symm

include h in
theorem Sec4Hyp.cj_t_v : cj (c.t : G) v = (c.t : G) * S.z := by
  have hvt : v * (c.t : G) = (c.t : G) * v⁻¹ := by
    have e : (c.t : G)⁻¹ * v * c.t = v⁻¹ := h.rel.v_by_u
    rw [c.tG_inv] at e
    calc v * (c.t : G) = (c.t : G) * ((c.t : G) * v * c.t) := by
          calc v * (c.t : G) = ((c.t : G) * c.t) * v * c.t := by
                rw [← pow_two, c.tG_sq', one_mul]
            _ = (c.t : G) * ((c.t : G) * v * c.t) := by group
      _ = (c.t : G) * v⁻¹ := by rw [e]
  have e1 : v⁻¹ * (c.t : G) = (c.t : G) * v := by
    calc v⁻¹ * (c.t : G) = v⁻¹ * (c.t : G) * v⁻¹ * v := by group
      _ = v⁻¹ * (v * (c.t : G)) * v := by
          calc v⁻¹ * (c.t : G) * v⁻¹ * v = v⁻¹ * ((c.t : G) * v⁻¹) * v := by group
            _ = v⁻¹ * (v * (c.t : G)) * v := by rw [hvt]
      _ = (c.t : G) * v := by group
  unfold cj
  calc v⁻¹ * (c.t : G) * v = ((c.t : G) * v) * v := by rw [e1]
    _ = (c.t : G) * (v * v) := by group
    _ = (c.t : G) * S.z := by rw [← pow_two, h.v_sq]

include h in
theorem Sec4Hyp.g_sq : ((c.t : G) * v * a₁ * c.a2 a₁) * ((c.t : G) * v * a₁ * c.a2 a₁) = 1 := by
  have hc := h.tv_comm_e
  have e : (c.t : G) * v * a₁ * c.a2 a₁ = ((c.t : G) * v) * (a₁ * c.a2 a₁) := by group
  rw [e]
  calc ((c.t : G) * v * (a₁ * c.a2 a₁)) * ((c.t : G) * v * (a₁ * c.a2 a₁))
      = ((c.t : G) * v) * ((a₁ * c.a2 a₁) * ((c.t : G) * v)) * (a₁ * c.a2 a₁) := by group
    _ = ((c.t : G) * v) * (((c.t : G) * v) * (a₁ * c.a2 a₁)) * (a₁ * c.a2 a₁) := by rw [← hc]
    _ = (((c.t : G) * v) * ((c.t : G) * v)) * ((a₁ * c.a2 a₁) * (a₁ * c.a2 a₁)) := by group
    _ = 1 := by rw [h.tv_sq, h.e_sq, mul_one]

include h in
theorem Sec4Hyp.g_comm_tv : ((c.t : G) * v * a₁ * c.a2 a₁) * ((c.t : G) * v) =
    ((c.t : G) * v) * ((c.t : G) * v * a₁ * c.a2 a₁) := by
  have hc := h.tv_comm_e
  have e : (c.t : G) * v * a₁ * c.a2 a₁ = ((c.t : G) * v) * (a₁ * c.a2 a₁) := by group
  rw [e]
  calc ((c.t : G) * v * (a₁ * c.a2 a₁)) * ((c.t : G) * v)
      = ((c.t : G) * v) * ((a₁ * c.a2 a₁) * ((c.t : G) * v)) := by group
    _ = ((c.t : G) * v) * (((c.t : G) * v) * (a₁ * c.a2 a₁)) := by rw [← hc]

include h in
theorem Sec4Hyp.g_mem_H : (c.t : G) * v * a₁ * c.a2 a₁ ∈ S.H :=
  S.H.mul_mem (S.H.mul_mem (S.H.mul_mem c.t.2 h.v_mem) h.a1_mem) h.a2_mem

include h in
theorem Sec4Hyp.g_comm_z : ((c.t : G) * v * a₁ * c.a2 a₁) * S.z =
    S.z * ((c.t : G) * v * a₁ * c.a2 a₁) := Ctx.zc h.g_mem_H

include h in
theorem Sec4Hyp.tv_mem_H : (c.t : G) * v ∈ S.H := S.H.mul_mem c.t.2 h.v_mem

include h hφ in
theorem Phi1.phi3_by_g :
    cj (phi3 c a₁ φ₁) ((c.t : G) * v * a₁ * c.a2 a₁) = phi4 c a₁ v φ₁ := by
  have e1 : cj (phi3 c a₁ φ₁) (c.t : G) = cj φ₁ a₁ := by
    rw [cj_cj, Ctx.a2_mul_t c a₁, cj_mul_right, hφ.by_t]
  have e2 : cj (cj φ₁ a₁) v = cj (cj φ₁ v) a₁⁻¹ := by
    rw [cj_cj, h.a1_mul_v, cj_mul_right]
  have e3 : cj (cj (cj φ₁ v) a₁⁻¹) a₁ = cj φ₁ v := by
    rw [cj_cj, inv_mul_cancel, cj_one_right]
  rw [cj_mul_right, cj_mul_right, cj_mul_right, e1, e2, e3]

include h hφ in
theorem Phi1.phi4_by_g :
    cj (phi4 c a₁ v φ₁) ((c.t : G) * v * a₁ * c.a2 a₁) = phi3 c a₁ φ₁ := by
  have e1 : cj (phi4 c a₁ v φ₁) (c.t : G) = (cj (cj φ₁ v) a₁)⁻¹ := by
    rw [cj_cj, Ctx.a2_mul_t c a₁, cj_mul_right, hφ.phi2_by_t h, cj_inv_left]
  have e2 : cj (cj (cj φ₁ v) a₁)⁻¹ v = cj φ₁ a₁⁻¹ := by
    rw [cj_inv_left, cj_cj, h.a1_mul_v, cj_mul_right, hφ.phi2_by_v h, cj_inv_left, inv_inv]
  have e3 : cj (cj φ₁ a₁⁻¹) a₁ = φ₁ := by
    rw [cj_cj, inv_mul_cancel, cj_one_right]
  rw [cj_mul_right, cj_mul_right, cj_mul_right, e1, e2, e3]

theorem z_mem_H' : S.z ∈ S.H := Subgroup.mem_centralizer_singleton_iff.mpr rfl

end NoCerts

section Certs


namespace Ctx

variable (c : Ctx S)

theorem mem_ocl_s_of_involutions {y w₁ w₂ : G} (hyN : y ∈ c.OG) (hy1 : y ≠ 1)
    (hw₁2 : w₁ ^ 2 = 1) (hw₂2 : w₂ ^ 2 = 1) (hw₁1 : w₁ ≠ 1) (hw₂1 : w₂ ≠ 1) (hne : w₁ ≠ w₂)
    (hcomm : w₂ * w₁ = w₁ * w₂) (hc : w₁ * y = y * w₁) (hi : w₂ * y * w₂⁻¹ = y⁻¹) :
    y ∈ c.ocl c.s := by
  have hmem : y ∈ (c.OG : Set G) \ {1} := ⟨hyN, hy1⟩
  rw [c.OG_sdiff_one_eq] at hmem
  rcases hmem with hs | ha
  · exact hs
  · exfalso
    obtain ⟨g, -, hyg⟩ := ha
    have hya : cj y g = (c.a : G) := by
      rw [hyg]; unfold cj; group
    have hcjinj : ∀ x x' : G, cj x g = cj x' g → x = x' := fun x x' e =>
      cj_injective_left g e
    refine c.false_of_centralizing_inverting_pair (v := cj w₁ g) (w := cj w₂ g) ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_
    · rw [← cj_pow_left, hw₁2, cj_one_left]
    · rw [← cj_pow_left, hw₂2, cj_one_left]
    · exact fun e => hw₁1 (hcjinj _ _ (e.trans (cj_one_left g).symm))
    · exact fun e => hw₂1 (hcjinj _ _ (e.trans (cj_one_left g).symm))
    · exact fun e => hne (hcjinj _ _ e)
    · rw [← hya, ← cj_mul_left, ← cj_mul_left, hc]
    · rw [← cj_mul_left, ← cj_mul_left, hcomm]
    · rw [← hya]
      calc cj w₂ g * cj y g * (cj w₂ g)⁻¹ = cj (w₂ * y * w₂⁻¹) g := by
            rw [cj_mul_left, cj_mul_left, cj_inv_left]
        _ = (cj y g)⁻¹ := by rw [hi, cj_inv_left]

theorem cube_mem_OG_of_centralizes {y i f : G} (hy : y ∈ c.ocl c.s) (hi2 : i ^ 2 = 1)
    (hf3 : f ^ 3 = 1) (hfN : f ∉ c.OG) (hic : i * y = y * i) (hfc : f * y = y * f) :
    (i * f) ^ 3 ∈ c.OG := by
  obtain ⟨g, hg, hyg⟩ := hy
  have hs : cj y g = c.s := by rw [hyg]; unfold cj; group
  have hcen : ∀ x : G, x * y = y * x → cj x g ∈ c.Cg := by
    intro x hx
    rw [c.mem_cg_iff]
    have e : cj x g * c.s = c.s * cj x g := by
      rw [← hs, ← cj_mul_left, ← cj_mul_left, hx]
    calc cj x g * c.s * (cj x g)⁻¹ = (c.s * cj x g) * (cj x g)⁻¹ := by rw [e]
      _ = c.s := by group
  have hi' := hcen i hic
  have hf' := hcen f hfc
  have h972 : Nat.card c.Cg = 972 := c.lemma14.2.1
  have hOcard : Nat.card (CFSG.oddCore ↥c.Cg) = 81 := by
    rw [c.card_oddCore_Cg, c.card_OG_eq_81]
  have hX : Nat.card (↥c.Cg ⧸ CFSG.oddCore ↥c.Cg) = 12 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥c.Cg)
    rw [h972, hOcard] at this
    omega
  have hKO : CFSG.oddCore (↥c.Cg ⧸ CFSG.oddCore ↥c.Cg) = ⊥ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_quotient_eq_bot
  have hodd : ∀ K : Subgroup (↥c.Cg ⧸ CFSG.oddCore ↥c.Cg), K.Normal → Odd (Nat.card K) →
      K = ⊥ := by
    intro K hKn hKodd
    have := le_oddCore_of_normal_odd K hKn hKodd
    rw [hKO] at this
    exact le_bot_iff.mp this
  have hfO : (⟨cj f g, hf'⟩ : ↥c.Cg) ∉ CFSG.oddCore ↥c.Cg := by
    rw [c.mem_oddCore_Cg_iff]
    intro hmem
    apply hfN
    have := c.conj_mem_OG_of_mem_NG hg hmem
    have e : g * cj f g * g⁻¹ = f := by unfold cj; group
    rwa [e] at this
  have key := cube_mem_of_card_twelve_quotient (CFSG.oddCore ↥c.Cg) hX hodd
    (i := ⟨cj i g, hi'⟩) (f := ⟨cj f g, hf'⟩)
    (Subtype.ext (by show (cj i g) ^ 2 = 1; rw [← cj_pow_left, hi2, cj_one_left]))
    (Subtype.ext (by show (cj f g) ^ 3 = 1; rw [← cj_pow_left, hf3, cj_one_left])) hfO
  rw [c.mem_oddCore_Cg_iff] at key
  have key' : (cj i g * cj f g) ^ 3 ∈ c.OG := key
  have hconj := c.conj_mem_OG_of_mem_NG hg key'
  have e : g * (cj i g * cj f g) ^ 3 * g⁻¹ = (i * f) ^ 3 := by
    rw [← cj_mul_left, ← cj_pow_left]; unfold cj; group
  rwa [e] at hconj

theorem pow_three_eq_one_of_cube_mem {x u₀ : G} (hu2 : u₀ ^ 2 = 1) (hu1 : u₀ ≠ 1)
    (hc : x * u₀ = u₀ * x) (hx : x ^ 3 ∈ c.OG) : x ^ 3 = 1 := by
  have h9 : x ^ (3 ^ 2) = 1 := by
    have := c.OG_pow_three _ hx
    rwa [← pow_mul] at this
  exact S.pow_three_of_commute_involution hu2 hu1 hc h9

end Ctx

namespace Phi1

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} {W : Subgroup G} (hφ : Phi1 c φ₁) (h : Sec4Hyp c a₁ v v₁)
  (hW : c.IsW W)

include hφ h hW in
theorem u_z_phi3_cube : ((c.t : G) * S.z * phi3 c a₁ φ₁) ^ 3 = 1 := by
  have hM3 := hφ.phi3_mem_MG h
  have hz2 : S.z ^ 2 = 1 := Ctx.z_sq (S := S)
  have ht2 : (c.t : G) ^ 2 = 1 := c.tG_sq'
  have htz : Commute (c.t : G) S.z := c.t_comm_z
  have hts2 : ((c.t : G) * S.z) ^ 2 = 1 := by rw [htz.mul_pow, ht2, hz2, one_mul]
  have hc : (c.t : G) * S.z * cj φ₁ v = cj φ₁ v * ((c.t : G) * S.z) := by
    have : cj (cj φ₁ v) ((c.t : G) * S.z) = cj φ₁ v := by
      rw [cj_mul_right, hφ.phi2_by_t h, cj_inv_left, hφ.phi2_by_z h, inv_inv]
    exact (comm_of_cj_eq this).symm
  have hy2 : cj φ₁ v ∈ c.ocl c.s := by
    refine c.mem_ocl_s_of_involutions (hφ.phi2_mem h) hφ.phi2_ne_one
      (w₁ := (c.t : G) * S.z) (w₂ := S.z) hts2 hz2 ?_ (Ctx.z_ne_one' (S := S)) ?_ ?_ hc ?_
    · intro e
      exact c.t_ne_z (Subtype.ext ((eq_inv_of_mul_eq_one_left e).trans (Ctx.zG_inv (S := S))))
    · intro e
      exact c.tG_ne_one (mul_right_cancel (e.trans (one_mul S.z).symm))
    · calc S.z * ((c.t : G) * S.z) = (S.z * c.t) * S.z := (mul_assoc _ _ _).symm
        _ = ((c.t : G) * S.z) * S.z := by rw [htz.eq]
    · have e := hφ.phi2_by_z h
      rw [cj, Ctx.zG_inv (S := S)] at e
      rw [Ctx.zG_inv (S := S)]
      exact e
  have hφ3N : phi3 c a₁ φ₁ ∉ c.OG := fun hmem => by
    have := hφ.indepN h 1 0 (by simpa using hmem)
    omega
  have hfc : phi3 c a₁ φ₁ * cj φ₁ v = cj φ₁ v * phi3 c a₁ φ₁ :=
    ((cmt_eq_one_iff'.mp (hφ.cmt14_eq_one h hW).2)).symm
  have hcp := c.cube_mem_OG_of_centralizes hy2 hts2 hφ.phi3_cube hφ3N hc hfc
  have hcomm : (c.t : G) * S.z * phi3 c a₁ φ₁ * cj (c.t : G) (c.a2 a₁) =
      cj (c.t : G) (c.a2 a₁) * ((c.t : G) * S.z * phi3 c a₁ φ₁) :=
    ((show Commute (c.t : G) _ from h.t_comm_u).mul_left
      (show Commute S.z _ from h.z_comm_u)).mul_left (show Commute (phi3 c a₁ φ₁) _ from
        hφ.phi3_comm_u)
  exact c.pow_three_eq_one_of_cube_mem (Sec4Hyp.u_sq (c := c) (a₁ := a₁))
    (Sec4Hyp.u_ne_one (c := c) (a₁ := a₁)) hcomm hcp

include hφ h hW in
theorem u_v_phi3_phi4_cube :
    ((c.t : G) * v * (phi3 c a₁ φ₁)⁻¹ * phi4 c a₁ v φ₁) ^ 3 = 1 := by
  obtain ⟨k, -, hk2, -⟩ := hφ.exists_k h hW
  have hM1 := hφ.phi1_mem_MG
  have hM2 := hφ.phi2_mem_MG h
  have hM3 := hφ.phi3_mem_MG h
  have hM4 := hφ.phi4_mem_MG h
  have hz2 : S.z ^ 2 = 1 := Ctx.z_sq (S := S)
  have hzz : S.z * S.z = 1 := Ctx.z_mul_z (S := S)
  have htz : Commute (c.t : G) S.z := c.t_comm_z
  have hA : (c.a : G) ^ k ∈ zpowers (c.a : G) := Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hA3 : (c.a : G) ^ k * phi3 c a₁ φ₁ = phi3 c a₁ φ₁ * (c.a : G) ^ k :=
    mem_zpowers_comm hA (Ctx.a_comm_MG hM3)
  have hA4 : (c.a : G) ^ k * phi4 c a₁ v φ₁ = phi4 c a₁ v φ₁ * (c.a : G) ^ k :=
    mem_zpowers_comm hA (Ctx.a_comm_MG hM4)
  have hc14 : φ₁ * phi4 c a₁ v φ₁ = phi4 c a₁ v φ₁ * φ₁ :=
    cmt_eq_one_iff'.mp (hφ.cmt14_eq_one h hW).1
  have hc23 : cj φ₁ v * phi3 c a₁ φ₁ = phi3 c a₁ φ₁ * cj φ₁ v :=
    cmt_eq_one_iff'.mp (hφ.cmt14_eq_one h hW).2
  have hcmt13 : cmt φ₁ (phi3 c a₁ φ₁) = (c.a : G) ^ k := by
    have := cj_eq_mul_cmt φ₁ (phi3 c a₁ φ₁)
    rw [hk2] at this
    exact (mul_left_cancel this).symm
  have hcmt24 : cmt (cj φ₁ v) (phi4 c a₁ v φ₁) = (c.a : G) ^ k :=
    (hφ.cmt24_eq h hW).trans hcmt13
  have hcj24 : cj (cj φ₁ v) (phi4 c a₁ v φ₁) = cj φ₁ v * (c.a : G) ^ k := by
    rw [cj_eq_mul_cmt, hcmt24]
  have c1 : cj φ₁ (phi3 c a₁ φ₁)⁻¹ = φ₁ * ((c.a : G) ^ k)⁻¹ := cj_inv_of_cj hA3 hk2
  have c2 : cj φ₁ (phi4 c a₁ v φ₁)⁻¹ = φ₁ :=
    cj_eq_self_of_comm (Commute.inv_right (show Commute φ₁ (phi4 c a₁ v φ₁) from hc14)).eq
  have c3 : cj (cj φ₁ v) (phi3 c a₁ φ₁)⁻¹ = cj φ₁ v :=
    cj_eq_self_of_comm
      (Commute.inv_right (show Commute (cj φ₁ v) (phi3 c a₁ φ₁) from hc23)).eq
  have c4 : cj (cj φ₁ v) (phi4 c a₁ v φ₁)⁻¹ = cj φ₁ v * ((c.a : G) ^ k)⁻¹ :=
    cj_inv_of_cj hA4 hcj24
  have cA4 : cj ((c.a : G) ^ k)⁻¹ (phi4 c a₁ v φ₁)⁻¹ = ((c.a : G) ^ k)⁻¹ :=
    cj_eq_self_of_comm
      (Commute.inv_inv (show Commute ((c.a : G) ^ k) (phi4 c a₁ v φ₁) from hA4)).eq
  have hy'N : φ₁ * (cj φ₁ v)⁻¹ ∈ c.OG :=
    c.OG.mul_mem hφ.mem (c.OG.inv_mem (hφ.phi2_mem h))
  have hy'1 : φ₁ * (cj φ₁ v)⁻¹ ≠ 1 := fun e => by
    have := hφ.indep12 h 1 (-1) (by simpa using e)
    omega
  have hw₁H : S.z * (c.t : G) * v ∈ S.H :=
    S.H.mul_mem (S.H.mul_mem z_mem_H' c.t.2) h.v_mem
  have hzcom : (S.z * (c.t : G) * v) * S.z = S.z * (S.z * (c.t : G) * v) := Ctx.zc hw₁H
  have hv_ne_z : v * v = S.z := by rw [← pow_two]; exact h.v_sq
  have hzne : S.z ≠ 1 := Ctx.z_ne_one' (S := S)
  have hw₁2 : (S.z * (c.t : G) * v) ^ 2 = 1 := by
    have hzt : ((c.t : G) * v) * S.z = S.z * ((c.t : G) * v) := Ctx.zc h.tv_mem_H
    rw [pow_two]
    calc S.z * (c.t : G) * v * (S.z * (c.t : G) * v)
        = S.z * (((c.t : G) * v) * S.z) * ((c.t : G) * v) := by group
      _ = S.z * (S.z * ((c.t : G) * v)) * ((c.t : G) * v) := by rw [hzt]
      _ = (S.z * S.z) * (((c.t : G) * v) * ((c.t : G) * v)) := by group
      _ = 1 := by rw [hzz, h.tv_sq, mul_one]
  have hw₁1 : S.z * (c.t : G) * v ≠ 1 := fun e => by
    have hv : v = (c.t : G) * S.z := by
      have e' : v = ((S.z * (c.t : G)))⁻¹ := eq_inv_of_mul_eq_one_right e
      rw [e', mul_inv_rev, c.tG_inv, Ctx.zG_inv (S := S)]
    have : v * v = 1 := by
      rw [hv, ← pow_two, htz.mul_pow, c.tG_sq', hz2, one_mul]
    exact hzne (hv_ne_z.symm.trans this)
  have hw₁z : S.z * (c.t : G) * v ≠ S.z := fun e => by
    have h1 : (c.t : G) * v = 1 := by
      have : S.z * ((c.t : G) * v) = S.z * 1 := by
        rw [mul_one]
        calc S.z * ((c.t : G) * v) = S.z * (c.t : G) * v := (mul_assoc _ _ _).symm
          _ = S.z := e
      exact mul_left_cancel this
    have hv : v = (c.t : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have : v * v = 1 := by
      rw [hv, c.tG_inv, ← pow_two, c.tG_sq']
    exact hzne (hv_ne_z.symm.trans this)
  have e1 : cj (φ₁ * (cj φ₁ v)⁻¹) S.z = φ₁⁻¹ * cj φ₁ v := by
    rw [cj_mul_left, cj_inv_left, hφ.by_z, hφ.phi2_by_z h, inv_inv]
  have e2 : cj (φ₁⁻¹ * cj φ₁ v) (c.t : G) = φ₁⁻¹ * (cj φ₁ v)⁻¹ := by
    rw [cj_mul_left, cj_inv_left, hφ.by_t, hφ.phi2_by_t h]
  have e3 : cj (φ₁⁻¹ * (cj φ₁ v)⁻¹) v = (cj φ₁ v)⁻¹ * φ₁ := by
    rw [cj_mul_left, cj_inv_left, cj_inv_left, hφ.phi2_by_v h, inv_inv]
  have hcomm12 : Commute φ₁ (cj φ₁ v) := hφ.phi12_comm h
  have hcjy : cj (φ₁ * (cj φ₁ v)⁻¹) (S.z * (c.t : G) * v) = φ₁ * (cj φ₁ v)⁻¹ := by
    rw [cj_mul_right, cj_mul_right, e1, e2, e3]
    exact (Commute.inv_right hcomm12).eq.symm
  have hcy : (S.z * (c.t : G) * v) * (φ₁ * (cj φ₁ v)⁻¹) =
      (φ₁ * (cj φ₁ v)⁻¹) * (S.z * (c.t : G) * v) := (comm_of_cj_eq hcjy).symm
  have hiy : S.z * (φ₁ * (cj φ₁ v)⁻¹) * S.z⁻¹ = (φ₁ * (cj φ₁ v)⁻¹)⁻¹ := by
    have e4 : cj (φ₁ * (cj φ₁ v)⁻¹) S.z = (φ₁ * (cj φ₁ v)⁻¹)⁻¹ := by
      rw [e1, mul_inv_rev, inv_inv]
      exact (Commute.inv_left hcomm12).eq
    rw [cj, Ctx.zG_inv (S := S)] at e4
    rw [Ctx.zG_inv (S := S)]
    exact e4
  have hy : φ₁ * (cj φ₁ v)⁻¹ ∈ c.ocl c.s :=
    c.mem_ocl_s_of_involutions hy'N hy'1 hw₁2 hz2 hw₁1 hzne hw₁z
      (by rw [← hzcom]) hcy hiy
  have hc34 : phi3 c a₁ φ₁ * phi4 c a₁ v φ₁ = phi4 c a₁ v φ₁ * phi3 c a₁ φ₁ :=
    hφ.phi34_comm h
  have hcomm34 : Commute (phi3 c a₁ φ₁)⁻¹ (phi4 c a₁ v φ₁)⁻¹ :=
    Commute.inv_inv (show Commute (phi3 c a₁ φ₁) (phi4 c a₁ v φ₁) from hc34)
  have hf3 : ((phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹) ^ 3 = 1 := by
    rw [hcomm34.mul_pow, inv_pow, inv_pow, hφ.phi3_cube, hφ.phi4_cube h, inv_one, mul_one]
  have hfN : (phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹ ∉ c.OG := fun hmem => by
    have := hφ.indepN h (-1) (-1) (by rw [zpow_neg_one, zpow_neg_one]; exact hmem)
    omega
  have hcjf : cj (φ₁ * (cj φ₁ v)⁻¹) ((phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹) =
      φ₁ * (cj φ₁ v)⁻¹ := by
    have s1 : cj (φ₁ * (cj φ₁ v)⁻¹) (phi3 c a₁ φ₁)⁻¹ =
        φ₁ * ((c.a : G) ^ k)⁻¹ * (cj φ₁ v)⁻¹ := by
      rw [cj_mul_left, cj_inv_left, c1, c3]
    rw [cj_mul_right, s1, cj_mul_left, cj_mul_left, c2, cA4, cj_inv_left, c4]
    group
  have hfc : ((phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹) * (φ₁ * (cj φ₁ v)⁻¹) =
      (φ₁ * (cj φ₁ v)⁻¹) * ((phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹) :=
    (comm_of_cj_eq hcjf).symm
  have hcp := c.cube_mem_OG_of_centralizes hy hw₁2 hf3 hfN hcy hfc
  have hg2 : ((c.t : G) * v * a₁ * c.a2 a₁) ^ 2 = 1 := by rw [pow_two]; exact h.g_sq
  have hg1 : (c.t : G) * v * a₁ * c.a2 a₁ ≠ 1 := fun e => by
    have h34 : phi3 c a₁ φ₁ = phi4 c a₁ v φ₁ := by
      have := hφ.phi3_by_g h
      rw [e, cj_one_right] at this
      exact this
    have := hφ.indep4 h 0 0 1 (-1) (by
      rw [zpow_zero, zpow_zero, one_mul, one_mul, zpow_one, zpow_neg_one, h34, mul_inv_cancel]
      exact one_mem _)
    omega
  have hgw : cj ((S.z * (c.t : G) * v) * ((phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹))
      ((c.t : G) * v * a₁ * c.a2 a₁) = (S.z * (c.t : G) * v) *
        ((phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹) := by
    have k1 : cj (S.z * (c.t : G) * v) ((c.t : G) * v * a₁ * c.a2 a₁) =
        S.z * (c.t : G) * v := by
      refine cj_eq_self_of_comm ?_
      have e : S.z * (c.t : G) * v = S.z * ((c.t : G) * v) := mul_assoc _ _ _
      rw [e]
      exact ((show Commute S.z _ from h.g_comm_z.symm).mul_left
        (show Commute ((c.t : G) * v) _ from h.g_comm_tv.symm)).eq
    have k2 : cj ((phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹)
        ((c.t : G) * v * a₁ * c.a2 a₁) = (phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹ := by
      rw [cj_mul_left, cj_inv_left, cj_inv_left, hφ.phi3_by_g h, hφ.phi4_by_g h]
      exact hcomm34.eq.symm
    rw [cj_mul_left, k1, k2]
  have hx2 : ((S.z * (c.t : G) * v) * ((phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹)) ^ 3 = 1 :=
    c.pow_three_eq_one_of_cube_mem hg2 hg1 (comm_of_cj_eq hgw) hcp
  have hc34' : (phi3 c a₁ φ₁)⁻¹ * phi4 c a₁ v φ₁ = phi4 c a₁ v φ₁ * (phi3 c a₁ φ₁)⁻¹ :=
    (Commute.inv_left (show Commute (phi3 c a₁ φ₁) (phi4 c a₁ v φ₁) from hc34)).eq
  have hzt : S.z * ((c.t : G) * S.z) = (c.t : G) := by
    calc S.z * ((c.t : G) * S.z) = (S.z * (c.t : G)) * S.z := (mul_assoc _ _ _).symm
      _ = ((c.t : G) * S.z) * S.z := by rw [htz.eq]
      _ = (c.t : G) * (S.z * S.z) := mul_assoc _ _ _
      _ = (c.t : G) := by rw [hzz, mul_one]
  have hcv : cj ((S.z * (c.t : G) * v) * ((phi3 c a₁ φ₁)⁻¹ * (phi4 c a₁ v φ₁)⁻¹)) v =
      (c.t : G) * v * (phi3 c a₁ φ₁)⁻¹ * phi4 c a₁ v φ₁ := by
    rw [cj_mul_left, cj_mul_left, cj_mul_left, cj_mul_left, cj_z_eq h.v_mem, h.cj_t_v,
      cj_eq_self_of_comm (rfl : v * v = v * v), cj_inv_left, cj_inv_left, hφ.phi3_by_v h,
      hφ.phi4_by_v h, inv_inv]
    calc S.z * ((c.t : G) * S.z) * v * (phi4 c a₁ v φ₁ * (phi3 c a₁ φ₁)⁻¹)
        = (c.t : G) * v * (phi4 c a₁ v φ₁ * (phi3 c a₁ φ₁)⁻¹) := by rw [hzt]
      _ = (c.t : G) * v * ((phi3 c a₁ φ₁)⁻¹ * phi4 c a₁ v φ₁) := by rw [hc34']
      _ = (c.t : G) * v * (phi3 c a₁ φ₁)⁻¹ * phi4 c a₁ v φ₁ := by group
  have := congrArg (fun x => cj x v) hx2
  simp only [cj_pow_left, cj_one_left] at this
  rw [hcv] at this
  exact this

end Phi1

end Certs

end Setup

end CFSG.Sporadic.Recognition.JankoWong
