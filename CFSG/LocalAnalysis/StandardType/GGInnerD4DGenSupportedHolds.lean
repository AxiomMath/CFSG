module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenContracts

public section

namespace CFSG.StandardType.GGInnerD4DGenParts

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.RankThree.PartOne.KCOrthogonal
open Polynomial

private lemma ltrdg3_restrict_conj
    {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {m : V ≃ₗ[K] V}
    (hm : m ∈ isometryCentralizer Q x) (g : ↥(supportedBlock Q x (X - 1))) :
    restrictFixed Q x ⟨m * (g : V ≃ₗ[K] V) * m⁻¹, conj_mem_supportedBlock hm g.2⟩ =
      isometryRestrictFixed Q x ⟨m, hm⟩ * restrictFixed Q x g *
        (isometryRestrictFixed Q x ⟨m, hm⟩)⁻¹ := by
  rw [← isometryRestrictFixed_restrictFixed (Q := Q) (x := x)
    (g := ⟨m * (g : V ≃ₗ[K] V) * m⁻¹, conj_mem_supportedBlock hm g.2⟩)]
  rw [show (⟨m * (g : V ≃ₗ[K] V) * m⁻¹,
        supportedBlock_le_isometryCentralizer _ (conj_mem_supportedBlock hm g.2)⟩ :
          ↥(isometryCentralizer Q x)) =
      ⟨m, hm⟩ * ⟨(g : V ≃ₗ[K] V), supportedBlock_le_isometryCentralizer _ g.2⟩ *
        ⟨m, hm⟩⁻¹
    from Subtype.ext rfl]
  rw [map_mul, map_mul, map_inv]
  rw [isometryRestrictFixed_restrictFixed g]

private lemma ltrdg3_restrictFixed_eq_coe_fixedBlockEquiv
    {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    (g : ↥(supportedBlock Q x (X - 1))) :
    restrictFixed Q x g =
      ((fixedBlockEquiv hx g :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :
        fixedSpace x ≃ₗ[K] fixedSpace x) := by
  ext w
  rw [coe_restrictFixed]
  exact (coe_fixedBlockEquiv hx g w).symm

theorem supportedFixedThreeInner_holds : S2MathAs51600Contracts.SupportedFixedThreeInner := by
  unfold S2MathAs51600Contracts.SupportedFixedThreeInner
  intro K _ _ _ V _ _ _ Q x hx hW c hc hc3
  let rLin : fixedSpace x ≃ₗ[K] fixedSpace x := isometryRestrictFixed Q x ⟨c, hc⟩
  let r : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
    ⟨rLin, isometryRestrictFixed_mem_orthogonalGroup ⟨c, hc⟩⟩
  let uF : ↥(supportedBlock Q x (X - 1)) := (fixedBlockEquiv hx).symm r
  have hc_pow : (⟨c, hc⟩ : ↥(isometryCentralizer Q x)) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hc3
  have hr3 : r ^ 3 = 1 := by
    have h : rLin ^ 3 = (1 : fixedSpace x ≃ₗ[K] fixedSpace x) := by
      have h2 : isometryRestrictFixed Q x (⟨c, hc⟩ ^ 3) = 1 := by
        rw [hc_pow, map_one]
      rwa [map_pow] at h2
    apply Subtype.ext
    simpa using h
  have hfb : fixedBlockEquiv hx uF = r :=
    MulEquiv.apply_symm_apply (fixedBlockEquiv hx) r
  have hcoe : restrictFixed Q x uF =
      ((fixedBlockEquiv hx uF :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :
        fixedSpace x ≃ₗ[K] fixedSpace x) :=
    ltrdg3_restrictFixed_eq_coe_fixedBlockEquiv hx uF
  have hu_restrict : restrictFixed Q x uF = isometryRestrictFixed Q x ⟨c, hc⟩ := by
    rw [hcoe, hfb]
  have huCent : (uF : V ≃ₗ[K] V) ∈ isometryCentralizer Q x :=
    supportedBlock_le_isometryCentralizer _ uF.2
  have hu_iso : isometryRestrictFixed Q x ⟨(uF : V ≃ₗ[K] V), huCent⟩ =
      isometryRestrictFixed Q x ⟨c, hc⟩ := by
    rw [isometryRestrictFixed_restrictFixed uF, hu_restrict]
  have hu3 : (uF : V ≃ₗ[K] V) ^ 3 = 1 := by
    have h : uF ^ 3 = 1 := by
      apply (fixedBlockEquiv hx).injective
      rw [map_pow, hfb, hr3, map_one]
    simpa using congrArg (fun z : ↥(supportedBlock Q x (X - 1)) => (z : V ≃ₗ[K] V)) h
  refine ⟨(uF : V ≃ₗ[K] V), ?_, hu3, ?_⟩
  · exact hx.mem_supportedFixedDerived_of_odd_pow hW uF.2 (n := 3) (by decide) hu3
  · intro g hg
    have hgB : g ∈ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock hg
    have ha : c * g * c⁻¹ ∈ supportedBlock Q x (X - 1) := conj_mem_supportedBlock hc hgB
    have hb : (uF : V ≃ₗ[K] V) * g * (uF : V ≃ₗ[K] V)⁻¹ ∈ supportedBlock Q x (X - 1) :=
      conj_mem_supportedBlock huCent hgB
    have hrestrict : restrictFixed Q x ⟨c * g * c⁻¹, ha⟩ =
        restrictFixed Q x ⟨(uF : V ≃ₗ[K] V) * g * (uF : V ≃ₗ[K] V)⁻¹, hb⟩ := by
      rw [ltrdg3_restrict_conj hc ⟨g, hgB⟩, ltrdg3_restrict_conj huCent ⟨g, hgB⟩,
        hu_iso]
    exact congrArg Subtype.val (restrictFixed_injective hx hrestrict)

end CFSG.StandardType.GGInnerD4DGenParts

end
