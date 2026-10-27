module

public import CFSG.Timmesfeld.ARS.CaseHAdX

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

theorem Setup.ad_congr (S : Setup R A A₀ P P') {g g' : G} (h : g = g')
    (hg : g ∈ Subgroup.normalizer (A : Set G)) (hg' : g' ∈ Subgroup.normalizer (A : Set G))
    (v : S.V) : S.ad hg v = S.ad hg' v := by
  subst h
  rfl

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]

theorem T_zero (s : E) : c.T s 0 = 0 := by
  have := S.hyp.finite
  apply c.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1)
  rw [c.x2_T, c.x3_zero, commutatorElement_one_right, c.x2_zero]

omit [CharP E 2] in
theorem F2_zero (s : E) : c.F2 s 0 = 0 := by
  have := S.hyp.finite
  apply c.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1)
  rw [c.x2_F2, c.x2_zero]
  have : (⟨_, (c.comm15_mem s 0).1⟩ : ↥(M R A)) = 1 :=
    Subtype.ext (by simp only [c.x5_zero, commutatorElement_one_right]; rfl)
  rw [this, map_one]
  rfl

theorem F3_zero (s : E) : c.F3 s 0 = 0 := by
  apply c.x3_injective
  rw [c.x3_F3, c.x3_zero]
  have : (⟨_, (c.comm15_mem s 0).1⟩ : ↥(M R A)) = 1 :=
    Subtype.ext (by simp only [c.x5_zero, commutatorElement_one_right]; rfl)
  rw [this, map_one]
  rfl

omit [CharP E 2] in
theorem conjSub_U3_k (μ : Eˣ) :
    conjSub (shortRoot R P ⁅A₀, P'⁆ A) (c.k μ) = shortRoot R P ⁅A₀, P'⁆ A := by
  have hQ' : conjSub ⁅A₀, P'⁆ (c.k μ) = ⁅A₀, P'⁆ := by
    change Subgroup.map _ ⁅A₀, P'⁆ = _
    rw [Subgroup.map_commutator]
    exact congrArg₂ (fun X Y => ⁅X, Y⁆) (c.conjSub_A₀_k μ) (c.conjSub_P'_k μ)
  rw [conjSub_shortRoot' S.hyp.root, c.conjSub_P_k, hQ', c.conjSub_A_k]

omit [CharP E 2] in
theorem k_mem_normalizer (μ : Eˣ) : c.k μ ∈ Subgroup.normalizer (A : Set G) :=
  conjSub_eq_self_iff.1 (c.conjSub_A_k μ)

variable [Finite F] [CharP F 2] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
include he

omit [CharP E 2] [Finite F] [CharP F 2] he in
theorem ad_x1_add (s₀ s : E) (v : S.V) :
    S.ad (c.x1_mem_normalizer (s₀ + s)) v =
      S.ad (c.x1_mem_normalizer s₀) (S.ad (c.x1_mem_normalizer s) v) := by
  rw [← S.ad_mul]
  exact S.ad_congr (c.x1_add s₀ s) _ _ v

theorem polar_N (s₀ s : E) : c.N (s₀ + s) = c.N s + c.N s₀ + c.F2 s₀ s + c.T s₀ (c.sharp s) := by
  have := S.hyp.finite
  have h := c.ad_x1_add s₀ s (c.vc 1 0 0 0)
  rw [c.ad_x1 e he, c.ad_x1 e he, c.ad_x1 e he] at h
  simp only [map_one, one_mul, zero_add, c.F3_zero, c.F2_zero, c.T_zero, add_zero] at h
  exact (c.vc_injective h).2.2.2.trans (by ring)

theorem polar_F2 (s₀ s w : E) :
    c.F2 (s₀ + s) w = c.F2 s w + c.F2 s₀ w + c.T s₀ (c.F3 s w) := by
  have := S.hyp.finite
  have h := c.ad_x1_add s₀ s (c.vc 0 w 0 0)
  rw [c.ad_x1 e he, c.ad_x1 e he, c.ad_x1 e he] at h
  simp only [map_zero, zero_mul, add_zero, zero_add, c.T_zero] at h
  obtain ⟨-, -, -, h4⟩ := c.vc_injective h
  rw [h4]

theorem polar_sharp (s₀ s : E) :
    c.sharp (s₀ + s) = c.sharp s + c.sharp s₀ + c.F3 s₀ s := by
  have := S.hyp.finite
  have h := c.ad_x1_add s₀ s (c.vc 1 0 0 0)
  rw [c.ad_x1 e he, c.ad_x1 e he, c.ad_x1 e he] at h
  simp only [map_one, one_mul, zero_add, c.F3_zero, c.F2_zero, c.T_zero, add_zero] at h
  exact (c.vc_injective h).2.2.1.trans (by ring)

theorem weyl_U5 {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
    {s : E} (hs : s ≠ 0) (w : E) :
    w + c.F3 s⁻¹ (c.F3 s w) + e (τ⁻¹ * c.F2 s w) * c.sharp s⁻¹ = 0 ∧
      τ⁻¹ * c.F2 s w * c.N s⁻¹ + c.F2 s⁻¹ (c.F3 s w) + c.T s⁻¹ w = 0 := by
  have := S.hyp.finite
  have hm := c.m_mem_normalizer
  have hW := c.x1_mul_xm1_mul_x1 hs
  have hxm : c.xm1 s⁻¹ = c.m * c.x1 s⁻¹ * c.m := by
    rw [← c.m_conj_x1, c.m_inv]
  have hlhs : S.ad (c.k_mem_normalizer (Units.mk0 s hs)) (S.ad hm (c.vc 0 w 0 0)) =
      S.ad (c.x1_mem_normalizer s) (S.ad hm (S.ad (c.x1_mem_normalizer s⁻¹)
        (S.ad hm (S.ad (c.x1_mem_normalizer s) (c.vc 0 w 0 0))))) := by
    simp only [← S.ad_mul]
    exact S.ad_congr (by rw [← hW, hxm]; group) _ _ _
  rw [c.ad_m hτ0 hτ, mul_zero, mul_zero] at hlhs
  obtain ⟨r', hr'⟩ := c.x3_surjective
    (c.conjSub_U3_k (Units.mk0 s hs) ▸ conj_mem_conjSub (c.k (Units.mk0 s hs)) (c.x3_mem w))
  have hk : S.ad (c.k_mem_normalizer (Units.mk0 s hs)) (c.vc 0 0 w 0) = c.vc 0 0 r' 0 := by
    rw [S.ad_apply]
    have e1 : (⟨c.k (Units.mk0 s hs) * S.lift (c.vc 0 0 w 0) * (c.k (Units.mk0 s hs))⁻¹,
        conj_mem_M_of_mem_normalizer S.hyp.root (c.k_mem_normalizer _)
          (S.lift (c.vc 0 0 w 0)).2⟩ : ↥(M R A)) = ⟨c.x3 r', Setup.U3_le_M (c.x3_mem r')⟩ := by
      apply Subtype.ext
      simp only [Setup.lift, vc, c.x6_zero, c.x5_zero, c.x2_zero, one_mul, mul_one]
      exact hr'.symm
    rw [e1, S.proj_U3 (c.x3_mem r')]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> apply Subtype.ext <;>
      simp [vc, c.x6_zero, c.x5_zero, c.x2_zero]
  rw [hk] at hlhs
  rw [c.ad_x1 e he, c.ad_m hτ0 hτ, c.ad_x1 e he, c.ad_m hτ0 hτ, c.ad_x1 e he] at hlhs
  simp only [map_zero, zero_mul, zero_add, add_zero, c.T_zero, mul_zero] at hlhs
  obtain ⟨h1, h2, -, -⟩ := c.vc_injective hlhs
  have hu : τ⁻¹ * (τ⁻¹ * c.F2 s w * c.N s⁻¹ + c.F2 s⁻¹ (c.F3 s w) + c.T s⁻¹ w) = 0 :=
    h1.symm
  have hu' : τ⁻¹ * c.F2 s w * c.N s⁻¹ + c.F2 s⁻¹ (c.F3 s w) + c.T s⁻¹ w = 0 := by
    rcases mul_eq_zero.1 hu with h | h
    · exact absurd h (inv_ne_zero hτ0)
    · exact h
  refine ⟨?_, hu'⟩
  rw [hu', mul_zero, map_zero, zero_mul, add_zero] at h2
  linear_combination h2.symm

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
