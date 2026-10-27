module

public import CFSG.Timmesfeld.ARS.CaseHNb

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

theorem conj_symm_of_mul_self {g x y : G} (hg : g * g = 1) (h : g * x * g⁻¹ = y) :
    g * y * g⁻¹ = x := by
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [← h, hg', show g * (g * x * g) * g = (g * g) * x * (g * g) by group, hg, one_mul, mul_one]

variable {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]

@[expose] noncomputable def xmb (u : F) : G :=
  c.ψ (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) u)

@[expose] noncomputable def xm5 (w : E) : G := c.nb * c.xm1 w * c.nb⁻¹

@[expose] noncomputable def xm3 (r : E) : G := c.m * c.xm5 r * c.m⁻¹

@[expose] noncomputable def xm2 (v : F) : G := c.m * c.xmb v * c.m⁻¹

@[expose] noncomputable def xm4 (z : F) : G := c.nb * c.xm2 z * c.nb⁻¹

omit [CharP E 2] in
theorem xmb_mem (u : F) : c.xmb u ∈ ⁅A₀, P'⁆ := psi_tv_mem _ c.hψQ' u

theorem xm4_mem [CharP F 2] (z : F) : c.xm4 z ∈ A₀ := by
  have h1 : c.xm2 z ∈ ⁅A₀, P⁆ := by
    have := conj_mem_conjSub c.m (c.xmb_mem z)
    rwa [c.conjSub_Q'_m] at this
  have := conj_mem_conjSub c.nb h1
  rwa [c.conjSub_Q_nb] at this

theorem xm3_mem [CharP F 2] (r : E) : c.xm3 r ∈ shortRoot R P ⁅A₀, P'⁆ ⁅A₀, P⁆ := by
  have h1 : c.xm5 r ∈ shortRoot R P' ⁅A₀, P⁆ ⁅A₀, P'⁆ := by
    have := conj_mem_conjSub c.nb (c.xm1_mem r)
    rwa [conjSub_shortRoot' S.hyp.root, c.conjSub_A_nb, c.conjSub_A₀_nb, c.conjSub_P_nb] at this
  have := conj_mem_conjSub c.m h1
  rwa [conjSub_shortRoot' S.hyp.root, c.conjSub_P'_m, c.conjSub_Q_m, c.conjSub_Q'_m] at this

omit [CharP E 2] in
theorem nb_conj_x6 [CharP F 2] (u : F) : c.nb * c.x6 u * c.nb⁻¹ = c.xmb u :=
  c.nb_conj_psi _ (by decide) u

omit [CharP E 2] in
theorem nb_conj_xmb [CharP F 2] (u : F) : c.nb * c.xmb u * c.nb⁻¹ = c.x6 u :=
  conj_symm_of_mul_self c.nb_mul_self (c.nb_conj_x6 u)

omit [CharP E 2] in
theorem nb_conj_xm1 (s : E) : c.nb * c.xm1 s * c.nb⁻¹ = c.xm5 s := rfl

omit [CharP E 2] in
theorem nb_conj_xm5 [CharP F 2] (w : E) : c.nb * c.xm5 w * c.nb⁻¹ = c.xm1 w :=
  conj_symm_of_mul_self c.nb_mul_self rfl

theorem nb_conj_xm2 (v : F) : c.nb * c.xm2 v * c.nb⁻¹ = c.xm4 v := rfl

theorem nb_conj_xm4 [CharP F 2] (z : F) : c.nb * c.xm4 z * c.nb⁻¹ = c.xm2 z :=
  conj_symm_of_mul_self c.nb_mul_self rfl

theorem nb_conj_xm3 [CharP F 2] (r : E) : c.nb * c.xm3 r * c.nb⁻¹ = c.xm3 r := by
  rw [Subgroup.mem_centralizer_iff.1 (c.xm3_mem r).1 _ c.nb_mem, mul_inv_cancel_right]

theorem m_conj_xm1 (s : E) : c.m * c.xm1 s * c.m⁻¹ = c.x1 s :=
  conj_symm_of_mul_self c.m_mul_self (c.m_conj_x1 s)

theorem m_conj_xmb (u : F) : c.m * c.xmb u * c.m⁻¹ = c.xm2 u := rfl

theorem m_conj_xm2 (v : F) : c.m * c.xm2 v * c.m⁻¹ = c.xmb v :=
  conj_symm_of_mul_self c.m_mul_self rfl

theorem m_conj_xm5 (w : E) : c.m * c.xm5 w * c.m⁻¹ = c.xm3 w := rfl

theorem m_conj_xm3 (r : E) : c.m * c.xm3 r * c.m⁻¹ = c.xm5 r :=
  conj_symm_of_mul_self c.m_mul_self rfl

theorem m_conj_x5 (w : E) : c.m * c.x5 w * c.m⁻¹ = c.x3 w := rfl

theorem m_conj_x4 (z : F) : c.m * c.x4 z * c.m⁻¹ = c.x4 z := by
  rw [← Subgroup.mem_centralizer_iff.1 c.m_mem_centralizer _ (Subgroup.mem_sup_left (c.x4_mem z)),
    mul_inv_cancel_right]

theorem m_conj_xm4 [CharP F 2] (z : F) : c.m * c.xm4 z * c.m⁻¹ = c.xm4 z := by
  rw [← Subgroup.mem_centralizer_iff.1 c.m_mem_centralizer _ (Subgroup.mem_sup_right (c.xm4_mem z)),
    mul_inv_cancel_right]

theorem m_conj_x2 {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u)) (v : F) :
    c.m * c.x2 v * c.m⁻¹ = c.x6 (τ⁻¹ * v) := by
  refine conj_symm_of_mul_self c.m_mul_self ?_
  rw [hτ, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
