module

public import CFSG.RankThree.PartOne.FOC.UnitaryFactor

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne

universe u

section Factor

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

@[expose] def GoodSplitAll (hK : UnitaryFieldData ℓ f K) (B : V →ₛₗ[hK.bar] V →ₗ[K] K)
    (x : LinearMap.GeneralLinearGroup K V) : Prop :=
  ∀ a : primaryFactors (x : Module.End K V), IsGoodBlock hK x a →
    ∀ g ∈ orbitFactor B x (a : K[X]),
      ∃ z ∈ orbitFactor B x (a : K[X]),
        (∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
          ((z : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
            ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V)) ∧
        z⁻¹ * g ∈ specialBlock B x (a : K[X])

variable (H : UnitaryPrimaryData hK.bar B x)
include H

theorem exists_factor_orbit_all (hq : 2 ≤ ℓ ^ f)
    (hexc : ∀ a : primaryFactors (x : Module.End K V),
      2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) → IsGoodBlock hK x a)
    (hobs : GoodSplitAll hK B x) (a : primaryFactors (x : Module.End K V))
    {gO : LinearMap.GeneralLinearGroup K V} (hgO : gO ∈ orbitFactor B x (a : K[X])) :
    ∃ z ∈ unitaryCentralizer B x, (∀ m ∈ unitaryCentralizer B x, Commute z m) ∧
      ∃ k ∈ (⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
        specialBlock B x (a : K[X])), gO = z * k := by
  by_cases hgood : IsGoodBlock hK x a
  · obtain ⟨z, hz, hscal, hk⟩ := hobs a hgood gO hgO
    refine ⟨z, orbitFactor_le_unitaryCentralizer hz, fun m hm =>
      commute_of_commute_supported H (orbit_closed H a) hz (fun g hg =>
        commute_orbitFactor_of_scalar H a (orbitFactor_le_unitaryCentralizer hz) hscal hg) hm,
      z⁻¹ * gO, ?_, by simp⟩
    exact le_iSup (fun a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a} =>
      specialBlock B x (a : K[X])) ⟨a, hgood⟩ hk
  · have hm1 : primaryMultiplicity (x : Module.End K V) (a : K[X]) ≤ 1 := by
      by_contra hlt
      exact hgood (hexc a (by omega))
    have hF : SpecialBlockFacts B x a := by
      by_cases hself : dualPoly hK.bar (a : K[X]) = a
      · exact specialBlockFacts_of_selfDual hq a hself (selfDualPrimaryBlock H a hself)
          (fun h => absurd h (by omega))
      · exact specialBlockFacts_of_paired hq a (pairedPrimaryBlock H a (Ne.symm hself))
    refine ⟨gO, orbitFactor_le_unitaryCentralizer hgO, fun m hm' =>
      commute_of_commute_supported H (orbit_closed H a) hgO (fun g hg =>
        hF.abelian hm1 gO hgO g hg) hm', 1, one_mem _, by simp⟩

theorem exists_central_factor_all (hq : 2 ≤ ℓ ^ f)
    (hexc : ∀ a : primaryFactors (x : Module.End K V),
      2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) → IsGoodBlock hK x a)
    (hobs : GoodSplitAll hK B x) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ unitaryCentralizer B x) :
    ∃ z ∈ unitaryCentralizer B x, (∀ m ∈ unitaryCentralizer B x, Commute z m) ∧
      ∃ k ∈ (⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
        specialBlock B x (a : K[X])), g = z * k := by
  classical
  suffices key : ∀ F : Finset K[X], ∀ g ∈ unitaryCentralizer B x,
      (∀ b ∈ primaryFactors (x : Module.End K V), b ∉ F →
        ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v) →
      ∃ z ∈ unitaryCentralizer B x, (∀ m ∈ unitaryCentralizer B x, Commute z m) ∧
        ∃ k ∈ (⨆ a : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a},
          specialBlock B x (a : K[X])), g = z * k by
    exact key (primaryFactors (x : Module.End K V)) g hg fun b hb hbn => absurd hb hbn
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro g hg h
    have : g = 1 := eq_one_of_forall_apply_eq H.squarefree fun b hb v hv => h b hb (by simp) v hv
    exact ⟨1, one_mem _, fun m _ => Commute.one_left m, 1, one_mem _, by rw [this]; simp⟩
  | insert b F hbF ih =>
    intro g hg h
    by_cases hbΦ : b ∈ primaryFactors (x : Module.End K V)
    · set a : primaryFactors (x : Module.End K V) := ⟨b, hbΦ⟩ with ha
      set O : Set K[X] := {(a : K[X]), dualPoly hK.bar (a : K[X])} with hOdef
      obtain ⟨gO, hgO, hgOeq⟩ := exists_component H (orbit_closed H a) hg
      obtain ⟨hin, hout⟩ := peel_component hg hgO hgOeq
      have hg' : gO⁻¹ * g ∈ unitaryCentralizer B x :=
        mul_mem (inv_mem hgO.1) hg
      have hg'tr : ∀ c ∈ primaryFactors (x : Module.End K V), c ∉ F →
          ∀ v ∈ primaryComponent (x : Module.End K V) c,
            ((gO⁻¹ * g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
        intro c hc hcF v hv
        by_cases hcO : c ∈ O
        · exact hin c hc hcO v hv
        · rw [hout c hc hcO v hv]
          refine h c hc ?_ v hv
          simp only [Finset.mem_insert, not_or]
          refine ⟨fun hcb => hcO ?_, hcF⟩
          rw [hcb]
          exact Or.inl rfl
      obtain ⟨z', hz', hz'c, k', hk', hg'eq⟩ := ih (gO⁻¹ * g) hg' hg'tr
      obtain ⟨z₀, hz₀, hz₀c, k₀, hk₀, hgOeq'⟩ := exists_factor_orbit_all H hq hexc hobs a hgO
      have hk₀M : k₀ ∈ unitaryCentralizer B x :=
        (iSup_le (fun a' : {a : primaryFactors (x : Module.End K V) // IsGoodBlock hK x a} =>
          specialBlock_le_unitaryCentralizer) : (⨆ a : {a : primaryFactors (x : Module.End K V) //
            IsGoodBlock hK x a}, specialBlock B x (a : K[X])) ≤ unitaryCentralizer B x) hk₀
      refine ⟨z₀ * z', mul_mem hz₀ hz', fun m hm => (hz₀c m hm).mul_left (hz'c m hm),
        k₀ * k', mul_mem hk₀ hk', ?_⟩
      have h1 : g = gO * (gO⁻¹ * g) := by simp
      rw [h1, hg'eq, hgOeq']
      have hc : z' * k₀ = k₀ * z' := (hz'c k₀ hk₀M).eq
      calc z₀ * k₀ * (z' * k') = z₀ * (k₀ * z') * k' := by group
        _ = z₀ * (z' * k₀) * k' := by rw [hc]
        _ = z₀ * z' * (k₀ * k') := by group
    · refine ih g hg fun c hc hcF v hv => h c hc ?_ v hv
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun hcb => hbΦ (hcb ▸ hc), hcF⟩

end Factor

end CFSG.RankThree.PartOne.FOC
