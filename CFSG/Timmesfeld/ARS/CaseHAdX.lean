module

public import CFSG.Timmesfeld.ARS.CaseHAd

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]

omit [CharP E 2] in
theorem x1_mem_normalizer (s : E) : c.x1 s ∈ Subgroup.normalizer (A : Set G) :=
  conjSub_eq_self_iff.1 (conjSub_left_of_mem_shortRoot (c.x1_mem s))

omit [CharP E 2] in
theorem comm15_mem (s w : E) : ⁅c.x1 s, c.x5 w⁆ ∈ M R A ⊓ M R P' :=
  S.facts.2.1 (Subgroup.commutator_mem_commutator (c.x1_mem s) (c.x5_mem w))

theorem comm13_mem (s r : E) : ⁅c.x1 s, c.x3 r⁆ ∈ P' :=
  (positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP').1
    (Subgroup.commutator_mem_commutator (c.x1_mem s) (c.x3_mem r))

@[expose] noncomputable def T (s r : E) : F :=
  Classical.choose (c.x2_surjective (c.comm13_mem s r))

theorem x2_T (s r : E) : c.x2 (c.T s r) = ⁅c.x1 s, c.x3 r⁆ :=
  Classical.choose_spec (c.x2_surjective (c.comm13_mem s r))

@[expose] noncomputable def F2 (s w : E) : F :=
  Classical.choose (c.x2_surjective (S.proj ⟨_, (c.comm15_mem s w).1⟩).2.2.2.2)

omit [CharP E 2] in
theorem x2_F2 (s w : E) : c.x2 (c.F2 s w) = (S.proj ⟨_, (c.comm15_mem s w).1⟩).2.2.2 :=
  Classical.choose_spec (c.x2_surjective (S.proj ⟨_, (c.comm15_mem s w).1⟩).2.2.2.2)

@[expose] noncomputable def F3 (s w : E) : E :=
  Classical.choose (c.x3_surjective (S.proj ⟨_, (c.comm15_mem s w).1⟩).2.2.1.2)

theorem x3_F3 (s w : E) : c.x3 (c.F3 s w) = (S.proj ⟨_, (c.comm15_mem s w).1⟩).2.2.1 :=
  Classical.choose_spec (c.x3_surjective (S.proj ⟨_, (c.comm15_mem s w).1⟩).2.2.1.2)

section Torus

variable [CharP F 2] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
include he

omit [CharP E 2] in
theorem d_conj_x5 (l : Fˣ) (w : E) : c.d l * c.x5 w * (c.d l)⁻¹ = c.x5 (e l * w) := by
  rw [x5, c.d_conj_c5, mul_one, he]
  rfl

theorem d_conj_x3 (l : Fˣ) (r : E) : c.d l * c.x3 r * (c.d l)⁻¹ = c.x3 (e l * r) := by
  rw [x3, x3, ← c.d_conj_x5 e he l r]
  calc c.d l * (c.m * c.x5 r * c.m⁻¹) * (c.d l)⁻¹ = (c.d l * c.m) * c.x5 r * (c.d l * c.m)⁻¹ := by
        group
    _ = (c.m * c.d l) * c.x5 r * (c.m * c.d l)⁻¹ := by rw [c.d_mul_m]
    _ = c.m * (c.d l * c.x5 r * (c.d l)⁻¹) * c.m⁻¹ := by group

theorem proj_comm_U3 (s : E) (u : F) :
    ((S.proj ⟨_, c.comm_mem s u⟩).2.2.1 : G) = c.x3 (e u * c.sharp s) := by
  by_cases hu : u = 0
  · subst hu
    have : (⟨_, c.comm_mem s 0⟩ : ↥(M R A)) = 1 :=
      Subtype.ext (by simp only [c.x6_zero, commutatorElement_one_right]; rfl)
    rw [this, map_one, map_zero, zero_mul, c.x3_zero]
    rfl
  · have hd := (S.proj_conj_of (conjSub_eq_self_iff.1 (c.conjSub_d _ c.hψA (Units.mk0 u hu)))
      (c.conjSub_d _ c.hψP _) (c.conjSub_U5_d _) (c.conjSub_U3_d _) (c.conjSub_d _ c.hψP' _)
      ⟨_, c.comm1_mem s⟩
      (by rw [c.d_conj_comm]; exact c.comm_mem s _)).2.2.1
    have e1 : (⟨c.d (Units.mk0 u hu) * ⁅c.x1 s, c.x6 1⁆ * (c.d (Units.mk0 u hu))⁻¹,
        by rw [c.d_conj_comm]; exact c.comm_mem s _⟩ : ↥(M R A)) = ⟨_, c.comm_mem s u⟩ :=
      Subtype.ext (by simp only; rw [c.d_conj_comm, Units.val_mk0, mul_one])
    rw [e1] at hd
    rw [hd]
    change c.d (Units.mk0 u hu) * c.n3 s * (c.d (Units.mk0 u hu))⁻¹ = _
    rw [← c.x3_sharp, c.d_conj_x3 e he, Units.val_mk0]

theorem ad_x1 [Finite F] (s : E) (u : F) (w r : E) (v : F) :
    S.ad (c.x1_mem_normalizer s) (c.vc u w r v) =
      c.vc u (w + e u * s) (r + e u * c.sharp s + c.F3 s w)
        (v + u * c.N s + c.F2 s w + c.T s r) := by
  have hx := c.x1_mem_normalizer s
  have hR := S.hyp.root
  obtain ⟨-, hU1P', -⟩ := positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  have h6 : S.ad hx (c.vc u 0 0 0) = c.vc u (e u * s) (e u * c.sharp s) (u * c.N s) := by
    rw [S.ad_apply]
    have hH := commutator_mem_H S (c.x1_mem s) (c.x6_mem u)
    have e1 : (⟨c.x1 s * S.lift (c.vc u 0 0 0) * (c.x1 s)⁻¹,
        conj_mem_M_of_mem_normalizer hR hx (S.lift (c.vc u 0 0 0)).2⟩ : ↥(M R A)) =
        ⟨_, c.comm_mem s u⟩ * ⟨c.x6 u, S.P_le_M (c.x6_mem u)⟩ := by
      apply Subtype.ext
      simp only [Setup.lift, vc, c.x5_zero, c.x3_zero, c.x2_zero, mul_one, Subgroup.coe_mul,
        commutatorElement_def]
      group
    rw [e1, map_mul, S.proj_P (c.x6_mem u)]
    obtain ⟨hp1, hp5⟩ := S.proj_H hH
    have hp1' : ((S.proj ⟨_, c.comm_mem s u⟩).1 : G) = 1 := by rw [hp1]; rfl
    have h3 := c.proj_comm_U3 e he s u
    have h2 := c.proj_comm_P' s u
    have hc5 : ((S.proj ⟨_, c.comm_mem s u⟩).2.1 : G) = c.x5 (e u * s) := by
      rw [hp5]
      change cxy S (c.x1 s) (c.x6 u) = c.x5 (e u * s)
      rw [← c5, he]
      rfl
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> apply Subtype.ext <;>
      simp [vc, hp1', hc5, h3, h2]
  have h5 : S.ad hx (c.vc 0 w 0 0) = c.vc 0 w (c.F3 s w) (c.F2 s w) := by
    rw [S.ad_apply]
    have hk := c.comm15_mem s w
    have e1 : (⟨c.x1 s * S.lift (c.vc 0 w 0 0) * (c.x1 s)⁻¹,
        conj_mem_M_of_mem_normalizer hR hx (S.lift (c.vc 0 w 0 0)).2⟩ : ↥(M R A)) =
        ⟨_, hk.1⟩ * ⟨c.x5 w, Setup.U5_le_M (c.x5_mem w)⟩ := by
      apply Subtype.ext
      simp only [Setup.lift, vc, c.x6_zero, c.x3_zero, c.x2_zero, one_mul, mul_one,
        Subgroup.coe_mul, commutatorElement_def]
      group
    rw [e1, map_mul, S.proj_U5 (c.x5_mem w)]
    obtain ⟨hk1, hk2⟩ := S.proj_K hk
    have hk1' : ((S.proj ⟨_, hk.1⟩).1 : G) = 1 := by rw [hk1]; rfl
    have hk2' : ((S.proj ⟨_, hk.1⟩).2.1 : G) = 1 := by rw [hk2]; rfl
    have h3 := c.x3_F3 s w
    have h2 := c.x2_F2 s w
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> apply Subtype.ext <;>
      simp [vc, hk1', hk2', ← h3, ← h2, c.x6_zero]
  have h3 : S.ad hx (c.vc 0 0 r 0) = c.vc 0 0 r (c.T s r) := by
    rw [S.ad_apply]
    have hc := c.comm13_mem s r
    have e1 : (⟨c.x1 s * S.lift (c.vc 0 0 r 0) * (c.x1 s)⁻¹,
        conj_mem_M_of_mem_normalizer hR hx (S.lift (c.vc 0 0 r 0)).2⟩ : ↥(M R A)) =
        ⟨_, S.P'_le_M hc⟩ * ⟨c.x3 r, Setup.U3_le_M (c.x3_mem r)⟩ := by
      apply Subtype.ext
      simp only [Setup.lift, vc, c.x6_zero, c.x5_zero, c.x2_zero, one_mul, mul_one,
        Subgroup.coe_mul, commutatorElement_def]
      group
    rw [e1, map_mul, S.proj_P' hc, S.proj_U3 (c.x3_mem r)]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> apply Subtype.ext <;>
      simp [vc, c.x6_zero, c.x5_zero, ← c.x2_T]
  have h2 : S.ad hx (c.vc 0 0 0 v) = c.vc 0 0 0 v := by
    rw [S.ad_apply]
    have e1 : (⟨c.x1 s * S.lift (c.vc 0 0 0 v) * (c.x1 s)⁻¹,
        conj_mem_M_of_mem_normalizer hR hx (S.lift (c.vc 0 0 0 v)).2⟩ : ↥(M R A)) =
        S.lift (c.vc 0 0 0 v) := by
      apply Subtype.ext
      simp only [Setup.lift, vc, c.x6_zero, c.x5_zero, c.x3_zero, one_mul]
      rw [(hU1P' _ (c.x1_mem s) _ (c.x2_mem v)).eq, mul_inv_cancel_right]
    rw [e1, S.proj_lift]
  rw [c.vc_eq u w r v, map_mul, map_mul, map_mul, h6, h5, h3, h2, ← c.vc_add, ← c.vc_add,
    ← c.vc_add]
  congr 1 <;> ring

end Torus

theorem ad_m [Finite F] [CharP F 2] {τ : F} (hτ0 : τ ≠ 0)
    (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u)) (u : F) (w r : E) (v : F) :
    S.ad c.m_mem_normalizer (c.vc u w r v) = c.vc (τ⁻¹ * v) r w (τ * u) := by
  have hR := S.hyp.root
  rw [S.ad_apply, S.proj_conj c.m_mem_normalizer]
  simp only [S.proj_lift]
  have hm2 : c.m * c.x2 v * c.m⁻¹ = c.x6 (τ⁻¹ * v) := by
    have h := hτ (τ⁻¹ * v)
    rw [← mul_assoc, mul_inv_cancel₀ hτ0, one_mul] at h
    rw [← h, c.m_inv]
    simp only [← mul_assoc, c.m_mul_self, one_mul]
    rw [mul_assoc, c.m_mul_self, mul_one]
  have hm3 : c.m * c.x3 r * c.m⁻¹ = c.x5 r := c.m_conj_x3 r
  have hm5 : c.m * c.x5 w * c.m⁻¹ = c.x3 w := rfl
  rw [show S.proj ⟨c.m * ((c.vc u w r v).1 : G) * c.m⁻¹, _⟩ =
      S.proj ⟨c.x2 (τ * u), S.P'_le_M (c.x2_mem _)⟩ from congrArg S.proj (Subtype.ext (hτ u)),
    show S.proj ⟨c.m * ((c.vc u w r v).2.1 : G) * c.m⁻¹, _⟩ =
      S.proj ⟨c.x3 w, Setup.U3_le_M (c.x3_mem w)⟩ from congrArg S.proj (Subtype.ext hm5),
    show S.proj ⟨c.m * ((c.vc u w r v).2.2.1 : G) * c.m⁻¹, _⟩ =
      S.proj ⟨c.x5 r, Setup.U5_le_M (c.x5_mem r)⟩ from congrArg S.proj (Subtype.ext hm3),
    show S.proj ⟨c.m * ((c.vc u w r v).2.2.2 : G) * c.m⁻¹, _⟩ =
      S.proj ⟨c.x6 (τ⁻¹ * v), S.P_le_M (c.x6_mem _)⟩ from congrArg S.proj (Subtype.ext hm2),
    S.proj_P' (c.x2_mem _), S.proj_U3 (c.x3_mem w), S.proj_U5 (c.x5_mem r),
    S.proj_P (c.x6_mem _)]
  simp [vc]

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
