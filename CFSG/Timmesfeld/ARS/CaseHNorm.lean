module

public import CFSG.Timmesfeld.ARS.CaseHAdj

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

namespace Setup

variable (S : Setup R A A₀ P P')

theorem proj_conj_P {x : G} (hx : x ∈ shortRoot R A A₀ P') (g : ↥(M R A))
    (hg : x * g * x⁻¹ ∈ M R A) : (S.proj ⟨x * g * x⁻¹, hg⟩).1 = (S.proj g).1 := by
  have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
    conjSub_eq_self_iff.1 (conjSub_left_of_mem_shortRoot hx)
  obtain ⟨hK, hUU, -, -, -, -⟩ := S.facts
  obtain ⟨hU13, hU1P', -⟩ :=
    positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  rw [S.proj_conj hxN g]
  simp only [Prod.fst_mul]
  set p := (S.proj g).1
  set u := (S.proj g).2.1
  set u' := (S.proj g).2.2.1
  set p' := (S.proj g).2.2.2
  have h1 : (S.proj ⟨x * p * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (S.P_le_M p.2)⟩).1 = p := by
    have hH := commutator_mem_H S hx p.2
    have e : (⟨x * p * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (S.P_le_M p.2)⟩ :
        ↥(M R A)) = ⟨⁅x, (p : G)⁆, hH.1⟩ * ⟨p, S.P_le_M p.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, commutatorElement_def]; group)
    rw [e, map_mul, S.proj_P p.2, Prod.fst_mul, (S.proj_H hH).1, one_mul]
  have h2 : (S.proj ⟨x * u * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (U5_le_M u.2)⟩).1 = 1 := by
    have hk : ⁅x, (u : G)⁆ ∈ M R A ⊓ M R P' := hUU (Subgroup.commutator_mem_commutator hx u.2)
    have e : (⟨x * u * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (U5_le_M u.2)⟩ :
        ↥(M R A)) = ⟨⁅x, (u : G)⁆, hk.1⟩ * ⟨u, U5_le_M u.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, commutatorElement_def]; group)
    rw [e, map_mul, S.proj_U5 u.2, Prod.fst_mul, (S.proj_K hk).1, one_mul]
  have h3 : (S.proj ⟨x * u' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (U3_le_M u'.2)⟩).1 = 1 := by
    have hc : ⁅x, (u' : G)⁆ ∈ P' := hU13 (Subgroup.commutator_mem_commutator hx u'.2)
    have e : (⟨x * u' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (U3_le_M u'.2)⟩ :
        ↥(M R A)) = ⟨⁅x, (u' : G)⁆, S.P'_le_M hc⟩ * ⟨u', U3_le_M u'.2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, commutatorElement_def]; group)
    rw [e, map_mul, S.proj_U3 u'.2, S.proj_P' hc]
    simp
  have h4 : (S.proj ⟨x * p' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN
      (S.P'_le_M p'.2)⟩).1 = 1 := by
    have e : (⟨x * p' * x⁻¹, conj_mem_M_of_mem_normalizer S.hyp.root hxN (S.P'_le_M p'.2)⟩ :
        ↥(M R A)) = ⟨p', S.P'_le_M p'.2⟩ :=
      Subtype.ext (by simp only; rw [(hU1P' x hx _ p'.2).eq, mul_inv_cancel_right])
    rw [e, S.proj_P' p'.2]
  rw [h1, h2, h3, h4, mul_one, mul_one, mul_one]

end Setup

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E)

theorem k_mul (μ μ' : Eˣ) : c.k (μ * μ') = c.k μ * c.k μ' := Sec8Field.torPar_mul c.φ μ μ'

theorem k_one : c.k 1 = 1 := Sec8Field.torPar_one c.φ

section Nu

variable [Finite F] [CharP F 2]

@[expose] noncomputable def nu (μ : Eˣ) : F := Classical.choose (c.exists_torus_scalar μ)

theorem nu_ne_zero (μ : Eˣ) : c.nu μ ≠ 0 := (Classical.choose_spec (c.exists_torus_scalar μ)).1

theorem k_conj_x6 (μ : Eˣ) (u : F) : c.k μ * c.x6 u * (c.k μ)⁻¹ = c.x6 (c.nu μ * u) :=
  (Classical.choose_spec (c.exists_torus_scalar μ)).2 u

theorem nu_mul (μ μ' : Eˣ) : c.nu (μ * μ') = c.nu μ * c.nu μ' := by
  have := S.hyp.finite
  have hinj := c.x6_injective (S.hyp.root.card_eq S.hA S.hP.2.1)
  have h := c.k_conj_x6 (μ * μ') 1
  rw [c.k_mul, show c.k μ * c.k μ' * c.x6 1 * (c.k μ * c.k μ')⁻¹ =
    c.k μ * (c.k μ' * c.x6 1 * (c.k μ')⁻¹) * (c.k μ)⁻¹ by group, c.k_conj_x6, c.k_conj_x6]
    at h
  have := hinj h
  rw [mul_one, mul_one] at this
  exact this.symm

theorem nu_one : c.nu 1 = 1 := by
  have := S.hyp.finite
  have hinj := c.x6_injective (S.hyp.root.card_eq S.hA S.hP.2.1)
  have h := c.k_conj_x6 1 1
  rw [c.k_one, one_mul, inv_one, mul_one, mul_one] at h
  exact (hinj h).symm

theorem nu_inv (μ : Eˣ) : c.nu μ⁻¹ = (c.nu μ)⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (by rw [← c.nu_mul, inv_mul_cancel, c.nu_one])

end Nu

section Weyl

variable [CharP E 2]

theorem k_mul_m (μ : Eˣ) : c.k μ * c.m = c.m * c.k μ⁻¹ := by
  simp only [k, m, torPar, weylPar, ← Subgroup.coe_mul, ← map_mul]
  rw [weylElt_mul_diagElt, inv_inv]

theorem proj_m_conj_P' (g : ↥(M R A)) (hg : c.m * g * c.m⁻¹ ∈ M R A) :
    ((S.proj ⟨c.m * g * c.m⁻¹, hg⟩).2.2.2 : G) = c.m * (S.proj g).1 * c.m⁻¹ := by
  rw [S.proj_conj c.m_mem_normalizer g]
  have h1 := c.conj_m_mem c.conjSub_P_m (S.proj g).1.2
  have h2 := c.conj_m_mem c.conjSub_U5_m (S.proj g).2.1.2
  have h3 := c.conj_m_mem c.conjSub_U3_m (S.proj g).2.2.1.2
  have h4 := c.conj_m_mem c.conjSub_P'_m (S.proj g).2.2.2.2
  rw [S.proj_P' h1, S.proj_U3 h2, S.proj_U5 h3, S.proj_P h4]
  simp

theorem N_eq [Finite F] [CharP F 2] {τ : F} (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
    {s : E} (hs : s ≠ 0) : c.N s = τ * c.nu (Units.mk0 s hs)⁻¹ := by
  have := S.hyp.finite
  have hR := S.hyp.root
  have hinj := c.x2_injective (hR.card_eq S.hA S.hP'.2.1)
  set μ := Units.mk0 s hs
  have hkm : c.k μ * c.m * c.x6 1 * (c.k μ * c.m)⁻¹ = c.x2 (τ * c.nu μ⁻¹) := by
    rw [c.k_mul_m, show c.m * c.k μ⁻¹ * c.x6 1 * (c.m * c.k μ⁻¹)⁻¹ =
      c.m * (c.k μ⁻¹ * c.x6 1 * (c.k μ⁻¹)⁻¹) * c.m⁻¹ by group, c.k_conj_x6, mul_one, hτ]
  set y := c.x1 s * c.x6 1 * (c.x1 s)⁻¹ with hy
  have hyc : y = ⁅c.x1 s, c.x6 1⁆ * c.x6 1 := by
    rw [hy, commutatorElement_def]
    group
  have hyM : y ∈ M R A := by
    rw [hyc]
    exact Subgroup.mul_mem _ (c.comm1_mem s) (S.P_le_M (c.x6_mem 1))
  have hz : c.xm1 s⁻¹ * y * (c.xm1 s⁻¹)⁻¹ = c.x2 (τ * c.nu μ⁻¹) := by
    have hW := c.x1_mul_xm1_mul_x1 hs
    have hcomm : Commute (c.x1 s) (c.x2 (τ * c.nu μ⁻¹)) :=
      commuting_shortRoot_mid S.hyp S.hP'.2.1 _ (c.x1_mem s) _ (c.x2_mem _)
    calc c.xm1 s⁻¹ * y * (c.xm1 s⁻¹)⁻¹ = (c.x1 s)⁻¹ * ((c.x1 s * c.xm1 s⁻¹ * c.x1 s) * c.x6 1 *
          (c.x1 s * c.xm1 s⁻¹ * c.x1 s)⁻¹) * c.x1 s := by rw [hy]; group
      _ = (c.x1 s)⁻¹ * c.x2 (τ * c.nu μ⁻¹) * c.x1 s := by rw [hW, hkm]
      _ = c.x2 (τ * c.nu μ⁻¹) := by
        rw [mul_assoc, ← hcomm.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hmy : c.m * y * c.m⁻¹ ∈ M R A := conj_mem_M_of_mem_normalizer hR c.m_mem_normalizer hyM
  have hx1 : c.x1 s⁻¹ = c.m * c.xm1 s⁻¹ * c.m⁻¹ := by
    rw [← c.m_conj_x1, c.m_inv]
    simp only [← mul_assoc, c.m_mul_self, one_mul]
    rw [mul_assoc, c.m_mul_self, mul_one]
  have hw : c.x1 s⁻¹ * (c.m * y * c.m⁻¹) * (c.x1 s⁻¹)⁻¹ =
      c.m * (c.xm1 s⁻¹ * y * (c.xm1 s⁻¹)⁻¹) * c.m⁻¹ := by
    rw [hx1]
    group
  have hwM : c.x1 s⁻¹ * (c.m * y * c.m⁻¹) * (c.x1 s⁻¹)⁻¹ ∈ M R A :=
    conj_mem_M_of_mem_normalizer hR (conjSub_eq_self_iff.1 (conjSub_left_of_mem_shortRoot
      (c.x1_mem s⁻¹))) hmy
  have hzM : c.xm1 s⁻¹ * y * (c.xm1 s⁻¹)⁻¹ ∈ M R A := by
    rw [hz]
    exact S.P'_le_M (c.x2_mem _)
  have hzm : c.m * (c.m * (c.xm1 s⁻¹ * y * (c.xm1 s⁻¹)⁻¹) * c.m⁻¹) * c.m⁻¹ =
      c.xm1 s⁻¹ * y * (c.xm1 s⁻¹)⁻¹ := by
    rw [c.m_inv]
    simp only [← mul_assoc, c.m_mul_self, one_mul]
    rw [mul_assoc, c.m_mul_self, mul_one]
  have hP'z := c.proj_m_conj_P' ⟨_, hwM⟩ (conj_mem_M_of_mem_normalizer hR c.m_mem_normalizer hwM)
  have e1 : (⟨c.m * (c.x1 s⁻¹ * (c.m * y * c.m⁻¹) * (c.x1 s⁻¹)⁻¹) * c.m⁻¹,
      conj_mem_M_of_mem_normalizer hR c.m_mem_normalizer hwM⟩ : ↥(M R A)) =
      ⟨c.x2 (τ * c.nu μ⁻¹), S.P'_le_M (c.x2_mem _)⟩ :=
    Subtype.ext (by simp only; rw [hw, hzm, hz])
  rw [e1, S.proj_P' (c.x2_mem _), S.proj_conj_P (c.x1_mem s⁻¹) ⟨_, hmy⟩ hwM] at hP'z
  have hPmy := (c.proj_m_conj ⟨y, hyM⟩ hmy).1
  rw [hPmy] at hP'z
  have hpy : S.proj ⟨y, hyM⟩ = S.proj ⟨_, c.comm1_mem s⟩ * S.proj ⟨_, S.P_le_M (c.x6_mem 1)⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hyc
  rw [hpy, S.proj_P (c.x6_mem 1)] at hP'z
  simp only [Prod.snd_mul, mul_one] at hP'z
  change c.x2 (τ * c.nu μ⁻¹) = c.m * (c.m * c.n2 s * c.m⁻¹) * c.m⁻¹ at hP'z
  rw [c.m_inv, show c.m * (c.m * c.n2 s * c.m) * c.m = (c.m * c.m) * c.n2 s * (c.m * c.m) by
    group, c.m_mul_self, one_mul, mul_one, ← c.x2_N] at hP'z
  exact (hinj hP'z).symm

theorem N_one [Finite F] [CharP F 2] {τ : F} (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u)) :
    c.N 1 = τ := by
  rw [c.N_eq hτ one_ne_zero, show (Units.mk0 (1 : E) one_ne_zero)⁻¹ = 1 by
    ext; simp, c.nu_one, mul_one]

theorem N_mul [Finite F] [CharP F 2] {τ : F} (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
    (s s' : E) : τ * c.N (s * s') = c.N s * c.N s' := by
  have N0 : c.N 0 = 0 := by
    have := S.hyp.finite
    have hinj := c.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1)
    apply hinj
    rw [c.x2_N, c.x2_zero]
    change ((S.proj ⟨_, c.comm1_mem 0⟩).2.2.2 : G) = 1
    have : (⟨_, c.comm1_mem 0⟩ : ↥(M R A)) = 1 :=
      Subtype.ext (by simp only [c.x1_zero, commutatorElement_one_left]; rfl)
    rw [this, map_one]
    rfl
  by_cases hs : s = 0
  · rw [hs, zero_mul, N0, zero_mul, mul_zero]
  by_cases hs' : s' = 0
  · rw [hs', mul_zero, N0, mul_zero, mul_zero]
  rw [c.N_eq hτ hs, c.N_eq hτ hs', c.N_eq hτ (mul_ne_zero hs hs'),
    show Units.mk0 (s * s') (mul_ne_zero hs hs') = Units.mk0 s hs * Units.mk0 s' hs' by
      ext; simp, mul_inv, c.nu_mul]
  ring

end Weyl

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
