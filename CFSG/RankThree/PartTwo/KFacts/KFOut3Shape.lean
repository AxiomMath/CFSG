module

public import CFSG.RankThree.PartTwo.KFacts.KFOut3
import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

section Transport

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev actQ (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ aschbacherSolvableCore 3 K) :=
  (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom

private theorem actQ_mk (K : Subgroup G) (g : Subgroup.normalizer (K : Set G)) (y : K) :
    actQ K g (y : K ⧸ aschbacherSolvableCore 3 K) =
      ((K.normalizerMonoidHom g y : K) : K ⧸ aschbacherSolvableCore 3 K) :=
  Sec4.thetaQuotMulAut_mk _ y

private theorem mem_sup_of_actQ_mem_inner (K : Subgroup G) {g : Subgroup.normalizer (K : Set G)}
    (hg : actQ K g ∈ inner (K ⧸ aschbacherSolvableCore 3 K)) :
    (g : G) ∈ K ⊔ Sec4.thetaQuotCentralizer K := by
  obtain ⟨x, hx⟩ := hg
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have hgN : (g : G) ∈ Subgroup.normalizer (K : Set G) := g.2
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hC : (g : G) * (k : G)⁻¹ ∈ Sec4.thetaQuotCentralizer K := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨mul_mem hgN (inv_mem hkN), fun l hl => ?_⟩
    set y : K := k⁻¹ * ⟨l, hl⟩ * k with hy
    have h1 := congrArg (fun σ : MulAut (K ⧸ aschbacherSolvableCore 3 K) =>
      σ (y : K ⧸ aschbacherSolvableCore 3 K)) hx
    simp only [MulAut.conj_apply] at h1
    rw [actQ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq] at h1
    have h3 : ((K.normalizerMonoidHom g y : K) : G) = (g : G) * (y : G) * (g : G)⁻¹ :=
      Sec4.normalizerMonoidHom_apply_coe _ y
    refine ⟨_, h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, h3]
    have hyG : (y : G) = (k : G)⁻¹ * l * (k : G) := by
      rw [hy]
      simp [mul_assoc]
    rw [hyG]
    group
  have e : (g : G) = ((g : G) * (k : G)⁻¹) * (k : G) := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup hC k.2

theorem kfOut3_of_le_inner
    (h : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → Sec4.IsList46 X →
      ∀ {β : MulAut X}, IsPGroup 3 (Subgroup.zpowers β) → ∀ {T : Subgroup (MulAut X)},
        IsPGroup 2 T → ⁅T, Subgroup.zpowers β⁆ = T → T ≤ inner X) : KFOut3 := by
  intro G _ _ K _ hKq hK46 β hβN hβ3 R hR2 hRN hβR hRβ
  set N := Subgroup.normalizer (K : Set G) with hNdef
  set b : N := ⟨β, hβN⟩ with hb
  set RN : Subgroup N := R.subgroupOf N with hRN'
  set T : Subgroup (MulAut (K ⧸ aschbacherSolvableCore 3 K)) := RN.map (actQ K) with hT
  have hT2 : IsPGroup 2 T :=
    (hR2.comap_of_injective N.subtype N.subtype_injective).map _
  have hzb : Subgroup.zpowers b = (Subgroup.zpowers β).subgroupOf N := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by simp [hb]⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa [hb] using hk)⟩
  have hb3 : IsPGroup 3 (Subgroup.zpowers b) := by
    rw [hzb]
    exact hβ3.comap_of_injective N.subtype N.subtype_injective
  have hbt3 : IsPGroup 3 (Subgroup.zpowers (actQ K b)) := by
    rw [← MonoidHom.map_zpowers]
    exact hb3.map _
  have hzN : Subgroup.zpowers β ≤ N := Subgroup.zpowers_le.mpr hβN
  have h1 : ⁅RN, (Subgroup.zpowers β).subgroupOf N⁆ = RN := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRN, inf_eq_left.mpr hzN, hRβ]
  have hTβ : ⁅T, Subgroup.zpowers (actQ K b)⁆ = T := by
    rw [← MonoidHom.map_zpowers, hzb, hT, ← Subgroup.map_commutator, h1]
  have hTI := h _ hKq hK46 hbt3 hT2 hTβ
  intro r hr
  have hrT : actQ K ⟨r, hRN hr⟩ ∈ T := ⟨⟨r, hRN hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  exact mem_sup_of_actQ_mem_inner K (hTI hrT)

end Transport

end CFSG.RankThree.PartTwo.KFacts
