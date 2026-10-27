module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Weyl
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.HardMathSupport.Timmesfeld.LangTorus.FiniteCentralizerRegular
import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

section TwCent


private abbrev e6OrbitRootList : List (Fin TwistTag.E6.tag.rank) :=
  (List.finRange TwistTag.E6.foldedTag.rank).flatMap fun a => TwistTag.E6.orbitWord a

private theorem e6OrbitRootList_count (i : Fin TwistTag.E6.tag.rank) :
    e6OrbitRootList.count i = 1 := by
  unfold e6OrbitRootList
  fin_cases i <;> decide

private theorem e6_orbitX_one_eq (R : Type) [Field R] (σ : R →+* R)
    (a : Fin TwistTag.E6.foldedTag.rank) :
    (orbitX TwistTag.E6 R σ a 1 : ModGL TwistTag.E6.tag R) =
      ((TwistTag.E6.orbitWord a).map fun j => xUnit TwistTag.E6.tag R j 1).prod := by
  rw [coe_orbitX_eq_orbitXProd]
  simp only [orbitXProd]
  congr 1
  exact List.map_congr_left fun j hj => by
    congr 1
    obtain ⟨k, hk, rfl⟩ :=
      TwistTag.exists_eq_perm_pow_orbitMin TwistTag.E6
        ((TwistTag.mem_orbitWord TwistTag.E6).1 hj)
    rw [orbitParam_pow TwistTag.E6 σ (1 : orbitField TwistTag.E6 R σ a) hk]
    simp

private theorem prod_map_flatMap {M : Type} [Monoid M] {α β : Type}
    (l : List α) (f : α → List β) (g : β → M) :
    (l.map fun a => ((f a).map g).prod).prod = ((l.flatMap f).map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append, List.prod_append, ih]

private theorem e6_prod_xUnit_isRegular (R : Type) [Field R] :
    CFSG.SignalizerFunctorTheorem.NonLocalExc.IsRegularUnipotent
      ((e6OrbitRootList.map fun j => xUnit TwistTag.E6.tag R j 1)).prod := by
  refine ⟨?_, fun i => ?_⟩
  · exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact CFSG.SignalizerFunctorTheorem.NonLocalExc.xUnit_mem_posUnipotent j 1
  · refine ⟨(e6OrbitRootList.count i : R), ?_, ?_⟩
    · rw [e6OrbitRootList_count i]
      norm_num
    · exact CFSG.HardMathSupport.Timmesfeld.LangTorus.hasCoord_list_prod
        (τ := TwistTag.E6.tag) (K := R) i e6OrbitRootList

private theorem baseChangeGL_e6OrbitProd (R S : Type) [Field R] [Field S]
    (σ : R →+* R) (ι : R →+* S) :
    baseChangeGL ι (((List.finRange TwistTag.E6.foldedTag.rank).map
        fun a => (orbitX TwistTag.E6 R σ a 1 : ModGL TwistTag.E6.tag R))).prod =
      ((e6OrbitRootList.map fun j => xUnit TwistTag.E6.tag S j 1)).prod := by
  have hpoint : ∀ a : Fin TwistTag.E6.foldedTag.rank,
      baseChangeGL ι (orbitX TwistTag.E6 R σ a 1 : ModGL TwistTag.E6.tag R) =
        ((TwistTag.E6.orbitWord a).map fun j => xUnit TwistTag.E6.tag S j 1).prod := by
    intro a
    rw [e6_orbitX_one_eq R σ a, map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply]
    rw [baseChangeGL_xUnit, map_one]
  have hmaps : List.map ((baseChangeGL ι) ∘ fun a =>
        (orbitX TwistTag.E6 R σ a 1 : ModGL TwistTag.E6.tag R))
        (List.finRange TwistTag.E6.foldedTag.rank) =
      List.map (fun a => ((TwistTag.E6.orbitWord a).map
        fun j => xUnit TwistTag.E6.tag S j 1).prod)
        (List.finRange TwistTag.E6.foldedTag.rank) :=
    List.map_congr_left fun a _ => by
      simp only [Function.comp_apply]
      exact hpoint a
  rw [map_list_prod, List.map_map, hmaps, prod_map_flatMap]

private theorem eq_one_of_commute_regular_longest {τ : Tag} {K : Type} [Field K]
    {u z : ModGL τ K} {w₀ : WeylGroup τ}
    (hu : CFSG.SignalizerFunctorTheorem.NonLocalExc.IsRegularUnipotent u)
    (hz : z ∈ adjointGroup τ K)
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀)
    (hcomm : z * u = u * z)
    (hn : z * canonicalRep (coxeterSystem τ) K w₀ = canonicalRep (coxeterSystem τ) K w₀ * z) :
    z = 1 := by
  have hcomm' : z⁻¹ * u * z = u := by rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  have hB : z ∈ borelGroup τ K :=
    CFSG.SignalizerFunctorTheorem.NonLocalExc.mem_borelGroup_of_conj_regular hu hz
      (by rw [hcomm']; exact hu.1)
  obtain ⟨-, hmap, hinf, -⟩ := opposite_Borel_intersection τ K w₀ hw₀
  have hB' : z ∈ torusGroup τ K ⊔ negUnipotent τ K := by
    rw [← hmap]
    refine ⟨z, hB, ?_⟩
    show canonicalRep (coxeterSystem τ) K w₀ * z * (canonicalRep (coxeterSystem τ) K w₀)⁻¹ = z
    rw [← hn, mul_assoc, mul_inv_cancel, mul_one]
  have hT : z ∈ torusGroup τ K := by
    rw [← hinf]
    exact Subgroup.mem_inf.2 ⟨hB, hB'⟩
  refine CFSG.HardMathSupport.Timmesfeld.LangTorus.torus_eq_one_of_conj_regular_field hu
    (one_mem _) hT ?_
  rw [inv_one, one_mul, mul_one, hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem e6LongestData_length_max (w : WeylGroup TwistTag.E6.tag) :
    (coxeterSystem TwistTag.E6.tag).length w ≤
      (coxeterSystem TwistTag.E6.tag).length e6LongestData.w := by
  obtain ⟨w₁, hmax₁, -, -, -, -⟩ := weyl_longest_element TwistTag.E6.tag
  have hsign₀ : ReversesSigns e6LongestData.w := by
    intro α hα hpos
    have himg := e6LongestData.image_smul_posRoots
    have hmem : e6LongestData.w • α ∈
        {β : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag β ∧ height β < 0} := by
      rw [← himg]
      exact ⟨α, ⟨hα, hpos⟩, rfl⟩
    exact hmem.2
  have heq : e6LongestData.w = w₁ :=
    hsign₀.eq (reversesSigns_of_forall_length_le hmax₁)
  rw [heq]
  exact hmax₁ w

theorem ggTwCentTriv {K L : Type} [Field K] [Field L] (σ : K →+* K)
    (hσ : Function.Surjective σ) (ι : K →+* L) {z : ModGL TwistTag.E6.tag L}
    (hz : z ∈ adjointGroup TwistTag.E6.tag L)
    (hc : ∀ h ∈ (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL ι), z * h = h * z) :
    z = 1 := by
  let uK : ModGL TwistTag.E6.tag K :=
    ((List.finRange TwistTag.E6.foldedTag.rank).map
      fun a => (orbitX TwistTag.E6 K σ a 1 : ModGL TwistTag.E6.tag K)).prod
  have huK : uK ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    unfold uK
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ
      (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ a 1)
  have huL : baseChangeGL ι uK =
      ((e6OrbitRootList.map fun j => xUnit TwistTag.E6.tag L j 1)).prod := by
    unfold uK
    exact baseChangeGL_e6OrbitProd K L σ ι
  have hreg : CFSG.SignalizerFunctorTheorem.NonLocalExc.IsRegularUnipotent
      (baseChangeGL ι uK) := by
    rw [huL]
    exact e6_prod_xUnit_isRegular L
  have hcomm_u : z * baseChangeGL ι uK = baseChangeGL ι uK * z :=
    hc _ ⟨uK, huK, rfl⟩
  have hnK : canonicalRep (coxeterSystem TwistTag.E6.tag) K e6LongestData.w ∈
      graphFixedRootGroup TwistTag.E6 K σ :=
    canonicalRep_mem_graphFixedRootGroup e6LongestData.mem
  have hnL : baseChangeGL ι (canonicalRep (coxeterSystem TwistTag.E6.tag) K e6LongestData.w) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L e6LongestData.w :=
    baseChangeGL_canonicalRep ι _
  have hcomm_n : z * canonicalRep (coxeterSystem TwistTag.E6.tag) L e6LongestData.w =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L e6LongestData.w * z := by
    have h := hc (baseChangeGL ι (canonicalRep (coxeterSystem TwistTag.E6.tag) K e6LongestData.w))
      ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) K e6LongestData.w, hnK, rfl⟩
    rwa [hnL] at h
  exact eq_one_of_commute_regular_longest hreg hz e6LongestData_length_max hcomm_u hcomm_n

end TwCent

end CFSG.StandardType.GGFinModel
