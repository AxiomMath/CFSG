module

public import CFSG.LocalAnalysis.StandardType.GGTBE6Torus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
import CFSG.LieType.AlgebraicGroups.KernelRootDescent
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.PairAuxSc
import CFSG.LieType.Steinberg.CentralExt.PerfectLift
import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
import CFSG.RankThree.PartOne.KLCE.Sector

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups


theorem kgLangS1EFixedLift_mem_torus_of_baseChange {τ : Tag} {K L : Type} [Field K] [Field L]
    (ι : K →+* L) {x : ModGL τ K} (hx : x ∈ adjointGroup τ K)
    (hxL : baseChangeGL ι x ∈ torusGroup τ L) : x ∈ torusGroup τ K := by
  have hker : ∀ F : Type, [Field F] → rootSpan τ F
      (kernelRoots (MonoidHom.id (Multiplicative (Fin τ.rank → ℤ)))) = ⊥ := by
    intro F _
    have hempty : kernelRoots (MonoidHom.id (Multiplicative (Fin τ.rank → ℤ))) =
        (∅ : Set _) := by
      ext α
      simp only [kernelRoots, Set.mem_setOf_eq, MonoidHom.id_apply, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hα h1
      exact hα.ne_zero (by simpa using h1)
    rw [hempty]
    simp [rootSpan]
  have h := mem_torus_sup_rootSpan_of_baseChangeGL_mem ι
    (MonoidHom.id (Multiplicative (Fin τ.rank → ℤ))) hx (by
      rw [hker L, sup_bot_eq]
      exact hxL)
  rwa [hker K, sup_bot_eq] at h

theorem kgLangS1EFixedLift_commute_of_isogeny_mem_torus {K : Type} [Field K] [Finite K]
    {w₁ w₂ : ↥(e6Data_valid.minGroup K)}
    (h₁ : ((e6Isogeny K w₁ : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K)
    (h₂ : ((e6Isogeny K w₂ : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) ∈ torusGroup Tag.E6 K) :
    w₁ * w₂ = w₂ * w₁ := by
  obtain ⟨a, ha⟩ := CFSG.StandardType.TBE6.mem_minTorus_range_of_isogeny_mem_torus h₁
  obtain ⟨b, hb⟩ := CFSG.StandardType.TBE6.mem_minTorus_range_of_isogeny_mem_torus h₂
  rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]

theorem kgLangS1EFixedLift_finiteCore {k k' : Type} [Field k] [Field k'] [Finite k']
    (κ : k →+* k') {U : Type} [Group U] [Group.IsPerfect U] (j : U →* ↥(e6Data_valid.minGroup k))
    (hj : Function.Injective j) (αU : MulAut U) {c' g' : ModGL Tag.E6 k'}
    (hc' : c' ∈ adjointGroup Tag.E6 k') (hg' : g' ∈ adjointGroup Tag.E6 k')
    (hconj : ∀ u : U,
      ((e6Isogeny k' (minBC e6Data_valid κ (j (αU u))) : ↥(adjointGroup Tag.E6 k')) :
          ModGL Tag.E6 k') =
        g' * ((e6Isogeny k' (minBC e6Data_valid κ (j u)) : ↥(adjointGroup Tag.E6 k')) :
          ModGL Tag.E6 k') * g'⁻¹)
    (hgT : c' * g' * c'⁻¹ ∈ torusGroup Tag.E6 k') {u₀ : U}
    (hu₀ : c' * ((e6Isogeny k' (minBC e6Data_valid κ (j u₀)) : ↥(adjointGroup Tag.E6 k')) :
        ModGL Tag.E6 k') * c'⁻¹ ∈ torusGroup Tag.E6 k') :
    αU u₀ = u₀ := by
  obtain ⟨h, hh⟩ := e6Isogeny_surjective (k := k') (⟨c', hc'⟩ : ↥(adjointGroup Tag.E6 k'))
  obtain ⟨a, ha⟩ := e6Isogeny_surjective (k := k') (⟨g', hg'⟩ : ↥(adjointGroup Tag.E6 k'))
  have hh' : ((e6Isogeny k' h : ↥(adjointGroup Tag.E6 k')) : ModGL Tag.E6 k') = c' :=
    congrArg Subtype.val hh
  have ha' : ((e6Isogeny k' a : ↥(adjointGroup Tag.E6 k')) : ModGL Tag.E6 k') = g' :=
    congrArg Subtype.val ha
  let jb : U →* ↥(e6Data_valid.minGroup k') := (minBC e6Data_valid κ).comp j
  have hjb : Function.Injective jb :=
    (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux.minBC_injective
      e6Data_valid κ).comp hj
  have hker : (e6Isogeny k').ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k') := by
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
  have hcomp : (e6Isogeny k').comp (jb.comp αU.toMonoidHom) =
      (e6Isogeny k').comp ((MulAut.conj a).toMonoidHom.comp jb) := by
    refine MonoidHom.ext fun u => ?_
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, Subgroup.coe_mul, Subgroup.coe_inv, ha']
    exact hconj u
  have heq := CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker hcomp
  have h1 : jb (αU u₀) = a * jb u₀ * a⁻¹ := DFunLike.congr_fun heq u₀
  have hcomm := kgLangS1EFixedLift_commute_of_isogeny_mem_torus
    (w₁ := h * a * h⁻¹) (w₂ := h * jb u₀ * h⁻¹)
    (by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hh', ha']
      exact hgT)
    (by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hh']
      exact hu₀)
  have h2 : a * jb u₀ = jb u₀ * a := by
    have h3 : h⁻¹ * ((h * a * h⁻¹) * (h * jb u₀ * h⁻¹)) * h =
        h⁻¹ * ((h * jb u₀ * h⁻¹) * (h * a * h⁻¹)) * h := by rw [hcomm]
    simpa [mul_assoc] using h3
  apply hjb
  rw [h1, mul_inv_eq_iff_eq_mul, h2]

end CFSG.StandardType
