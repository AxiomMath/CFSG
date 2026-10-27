module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientPairDescentPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ShortPairStabilizerPart2

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

open CFSG.LieType.Steinberg.Adjoint

open CFSG.LieType.Universal

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.RootBaseChange

open CFSG.StandardType.F4ExplicitPos.PinnedBaseChange

open CFSG.StandardType.F4ExplicitPos.PairStabilizerNative

open CFSG.StandardType.F4ExplicitPos.FixedImage

open CFSG.StandardType.F4ExplicitPos.AmbientAction

open CFSG.StandardType.F4ExplicitPos.AmbientPairDescent

open CFSG.StandardType

open CFSG.SeitzReduction

open CFSG.SeitzReduction.F4Pilot

open CFSG.LieType.Ree.ReeTag

open CFSG.StandardType.GGFinModel.G5

open scoped CFSG.ConvolutionPoints

namespace CFSG.StandardType.F4ExplicitPos.AmbientPairFinish

variable {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]

abbrev deltaF4 : Fin Tag.F4.rank → ℤ := F4.dualRoot (highRoot Tag.F4)

theorem dualRoot_highRoot_eq_rootS : deltaF4 = rootS := by
  decide +kernel

theorem isRoot_dualRoot_highRoot : IsRoot Tag.F4 deltaF4 := by
  rw [dualRoot_highRoot_eq_rootS]
  exact isRoot_rootS

theorem iform_highRoot_self : iform (highRoot Tag.F4) (highRoot Tag.F4) = 4 := by
  have h : highRoot Tag.F4 = rootR := rfl
  rw [h]
  exact iform_rootR_rootS_values.1

theorem iform_dualRoot_highRoot_self : iform deltaF4 deltaF4 = 2 := by
  rw [dualRoot_highRoot_eq_rootS]
  exact iform_rootR_rootS_values.2.1

theorem f4_exists_weyl_highRoot_or_dualRoot {α : Fin Tag.F4.rank → ℤ}
    (hα : IsRoot Tag.F4 α) :
    ∃ (β : Fin Tag.F4.rank → ℤ) (u : WeylGroup Tag.F4),
      (β = highRoot Tag.F4 ∨ β = deltaF4) ∧ u • β = α := by
  rcases iform_self_eq_two_or_four hα with h2 | h4
  · obtain ⟨u, hu⟩ := ggG5_orbit_F4 isRoot_dualRoot_highRoot hα
      (by rw [iform_dualRoot_highRoot_self, h2])
    exact ⟨deltaF4, u, Or.inr rfl, hu⟩
  · obtain ⟨u, hu⟩ := ggG5_orbit_F4 (isRoot_highRoot Tag.F4) hα
      (by rw [iform_highRoot_self, h4])
    exact ⟨highRoot Tag.F4, u, Or.inl rfl, hu⟩

section F4Short

variable [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem f4_frobTwistGL_one_mem_shortPairStabilizer
    (f : ℕ) {g : ModGL Tag.F4 Ω}
    (hg : g ∈ adjointGroup Tag.F4 Ω ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω deltaF4 : Set (ModGL Tag.F4 Ω)) ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-deltaF4) : Set (ModGL Tag.F4 Ω))) :
    frobTwistGL Tag.F4 Ω 2 f 1 g ∈ adjointGroup Tag.F4 Ω ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω deltaF4 : Set (ModGL Tag.F4 Ω)) ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-deltaF4) : Set (ModGL Tag.F4 Ω)) := by
  rw [ShortPairStabilizer.f4_short_pair_stabilizer_eq (Ω := Ω)] at hg ⊢
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  exact ShortPairStabilizer.f4_map_entrywiseFrobGL_torus_sup_rootSpan_le
    (Ω := Ω) 2 f CFSG.StandardType.F4ExplicitPos.ShortPairStabilizer.Sstar ⟨g, hg, rfl⟩

theorem f4_short_pair_descent
    (f : ℕ) (hf : 1 ≤ f)
    {g : ModGL Tag.F4 Ω} (hgA : g ∈ adjointGroup Tag.F4 Ω)
    (hstabplus : (rootSubgroup Tag.F4 Ω deltaF4).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω deltaF4).map (MulAut.conj g).toMonoidHom)
    (hstabminus : (rootSubgroup Tag.F4 Ω (-deltaF4)).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-deltaF4)).map (MulAut.conj g).toMonoidHom) :
    ∃ u ∈ adjointGroup Tag.F4 Ω, entrywiseFrobGL Tag.F4 Ω 2 f u = u ∧
      (rootSubgroup Tag.F4 Ω deltaF4).map (MulAut.conj u).toMonoidHom =
        (rootSubgroup Tag.F4 Ω deltaF4).map (MulAut.conj g).toMonoidHom ∧
      (rootSubgroup Tag.F4 Ω (-deltaF4)).map (MulAut.conj u).toMonoidHom =
        (rootSubgroup Tag.F4 Ω (-deltaF4)).map (MulAut.conj g).toMonoidHom := by
  have hFZ : ∀ x ∈ adjointGroup Tag.F4 Ω ⊓
      Subgroup.normalizer (rootSubgroup Tag.F4 Ω deltaF4 : Set (ModGL Tag.F4 Ω)) ⊓
      Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-deltaF4) : Set (ModGL Tag.F4 Ω)),
      frobTwistGL Tag.F4 Ω 2 f 1 x ∈
      adjointGroup Tag.F4 Ω ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω deltaF4 : Set (ModGL Tag.F4 Ω)) ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-deltaF4) : Set (ModGL Tag.F4 Ω)) :=
    fun x hx => f4_frobTwistGL_one_mem_shortPairStabilizer f hx
  have hZ : IsConnectedAlgebraicSubgroup Ω
      ((adjointGroup Tag.F4 Ω ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω deltaF4 : Set (ModGL Tag.F4 Ω)) ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-deltaF4) : Set (ModGL Tag.F4 Ω))).map
          (modGLPoint Tag.F4 Ω).toMonoidHom) :=
    ShortPairStabilizer.f4_isConnectedAlgebraicSubgroup_shortPairStabilizer
      (Ω := Ω)
  have hFA : ∀ x ∈ adjointGroup Tag.F4 Ω,
      frobTwistGL Tag.F4 Ω 2 f 1 x ∈ adjointGroup Tag.F4 Ω := by
    intro x hx
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    have hm : (entrywiseFrobGL Tag.F4 Ω 2 f : ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω) =
        bcGL (τ := Tag.F4) (iterateFrobenius Ω 2 f) := by
      rw [entrywiseFrobGL, bcGL, bcEndHom_eq_entrywiseHom]
    rw [hm]
    exact bcGL_mem_adjointGroup _ hx
  have hstabplus' : (rootSubgroup Tag.F4 Ω deltaF4).map
      (MulAut.conj (frobTwistGL Tag.F4 Ω 2 f 1 g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω deltaF4).map (MulAut.conj g).toMonoidHom := by
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]; exact hstabplus
  have hstabminus' : (rootSubgroup Tag.F4 Ω (-deltaF4)).map
      (MulAut.conj (frobTwistGL Tag.F4 Ω 2 f 1 g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-deltaF4)).map (MulAut.conj g).toMonoidHom := by
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]; exact hstabminus
  obtain ⟨u, huA, hFu, hplus, hminus⟩ :=
    exists_fixed_conj_eq_of_frobTwist_pair (τ := Tag.F4) 2 f hf
      (adjointGroup Tag.F4 Ω) (rootSubgroup Tag.F4 Ω deltaF4)
      (rootSubgroup Tag.F4 Ω (-deltaF4)) hFA hFZ hZ hgA hstabplus' hstabminus'
  refine ⟨u, huA, ?_, hplus, hminus⟩
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hFu
  exact hFu

end F4Short

section FiniteCore

variable [IsAlgClosed Ω] [CharP Ω 2]

theorem f4_pair_finite_endpoint_of_descent
    (f : ℕ) (hcard : Nat.card K = 2 ^ f)
    (β : Fin Tag.F4.rank → ℤ)
    {g u : ModGL Tag.F4 Ω}
    (huA : u ∈ adjointGroup Tag.F4 Ω)
    (hufix : entrywiseFrobGL Tag.F4 Ω 2 f u = u)
    (hplusU : (rootSubgroup Tag.F4 Ω β).map (MulAut.conj u).toMonoidHom =
      (rootSubgroup Tag.F4 Ω β).map (MulAut.conj g).toMonoidHom)
    (hminusU : (rootSubgroup Tag.F4 Ω (-β)).map (MulAut.conj u).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-β)).map (MulAut.conj g).toMonoidHom)
    {P Pm : Subgroup (ModGL Tag.F4 Ω)}
    (hPle : P ≤ (rootSubgroup Tag.F4 Ω β).map (MulAut.conj g).toMonoidHom)
    (hPmle : Pm ≤ (rootSubgroup Tag.F4 Ω (-β)).map (MulAut.conj g).toMonoidHom)
    (hPfix : ∀ x ∈ P, entrywiseFrobGL Tag.F4 Ω 2 f x = x)
    (hPmfix : ∀ x ∈ Pm, entrywiseFrobGL Tag.F4 Ω 2 f x = x)
    (hPcard : Nat.card P = Nat.card K)
    (hPmcard : Nat.card Pm = Nat.card K) :
    ∃ uK : adjointGroup Tag.F4 K,
      P = ((rootSubgroup Tag.F4 K β).map
            (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
            (MulAut.conj (bcGL (τ := Tag.F4) (algebraMap K Ω)
              (uK : ModGL Tag.F4 K))).toMonoidHom ∧
      Pm = ((rootSubgroup Tag.F4 K (-β)).map
            (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
            (MulAut.conj (bcGL (τ := Tag.F4) (algebraMap K Ω)
              (uK : ModGL Tag.F4 K))).toMonoidHom := by
  have hFr : ∀ c : Ω, iterateFrobenius Ω 2 f c = c ^ Nat.card K := by
    intro c; rw [iterateFrobenius_def, hcard]
  obtain ⟨uK0, huK0A, huK0⟩ := Subgroup.mem_map.1
    (f4_fixed_frobenius_mem_map (K := K) (Ω := Ω) f hcard huA hufix)
  refine ⟨⟨uK0, huK0A⟩, ?_, ?_⟩
  · rw [huK0]
    have hPleU : P ≤ (rootSubgroup Tag.F4 Ω β).map (MulAut.conj u).toMonoidHom := by
      rw [hplusU]; exact hPle
    have : Finite ↥(((rootSubgroup Tag.F4 K β).map
        (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
        (MulAut.conj u).toMonoidHom) :=
      finite_map_map_conj_rootSubgroup (K := K) (Ω := Ω) β u
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hxP
      have hxU := hPleU hxP
      have hxfix : x ∈ (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))).eqLocus
          (MonoidHom.id (ModGL Tag.F4 Ω)) := hPfix x hxP
      have hx : x ∈ ((rootSubgroup Tag.F4 Ω β).map
          (MulAut.conj u).toMonoidHom) ⊓
          (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))).eqLocus
            (MonoidHom.id (ModGL Tag.F4 Ω)) := ⟨hxU, hxfix⟩
      rw [f4_fixed_conj_rootSubgroup (K := K) (Ω := Ω) (iterateFrobenius Ω 2 f) hFr
        β hufix] at hx
      exact hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj u).injective,
        Subgroup.card_map_of_injective (bcGL_injective (τ := Tag.F4) (algebraMap K Ω)
          (FaithfulSMul.algebraMap_injective K Ω)),
        card_rootSubgroup]
      exact le_of_eq hPcard.symm
  · rw [huK0]
    have hPmleU : Pm ≤ (rootSubgroup Tag.F4 Ω (-β)).map (MulAut.conj u).toMonoidHom := by
      rw [hminusU]; exact hPmle
    have : Finite ↥(((rootSubgroup Tag.F4 K (-β)).map
        (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
        (MulAut.conj u).toMonoidHom) :=
      finite_map_map_conj_rootSubgroup (K := K) (Ω := Ω) (-β) u
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hxP
      have hxU := hPmleU hxP
      have hxfix : x ∈ (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))).eqLocus
          (MonoidHom.id (ModGL Tag.F4 Ω)) := hPmfix x hxP
      have hx : x ∈ ((rootSubgroup Tag.F4 Ω (-β)).map
          (MulAut.conj u).toMonoidHom) ⊓
          (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))).eqLocus
            (MonoidHom.id (ModGL Tag.F4 Ω)) := ⟨hxU, hxfix⟩
      rw [f4_fixed_conj_rootSubgroup (K := K) (Ω := Ω) (iterateFrobenius Ω 2 f) hFr
        (-β) hufix] at hx
      exact hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj u).injective,
        Subgroup.card_map_of_injective (bcGL_injective (τ := Tag.F4) (algebraMap K Ω)
          (FaithfulSMul.algebraMap_injective K Ω)),
        card_rootSubgroup]
      exact le_of_eq hPmcard.symm

end FiniteCore

section ShortEndpoint

variable [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem f4_short_pair_finite_endpoint
    (f : ℕ) (hf : 1 ≤ f) (hcard : Nat.card K = 2 ^ f)
    {g : ModGL Tag.F4 Ω} (hgA : g ∈ adjointGroup Tag.F4 Ω)
    (hstabplus : (rootSubgroup Tag.F4 Ω deltaF4).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω deltaF4).map (MulAut.conj g).toMonoidHom)
    (hstabminus : (rootSubgroup Tag.F4 Ω (-deltaF4)).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-deltaF4)).map (MulAut.conj g).toMonoidHom)
    {P Pm : Subgroup (ModGL Tag.F4 Ω)}
    (hPle : P ≤ (rootSubgroup Tag.F4 Ω deltaF4).map (MulAut.conj g).toMonoidHom)
    (hPmle : Pm ≤ (rootSubgroup Tag.F4 Ω (-deltaF4)).map (MulAut.conj g).toMonoidHom)
    (hPfix : ∀ x ∈ P, entrywiseFrobGL Tag.F4 Ω 2 f x = x)
    (hPmfix : ∀ x ∈ Pm, entrywiseFrobGL Tag.F4 Ω 2 f x = x)
    (hPcard : Nat.card P = Nat.card K)
    (hPmcard : Nat.card Pm = Nat.card K) :
    ∃ uK : adjointGroup Tag.F4 K,
      P = ((rootSubgroup Tag.F4 K deltaF4).map
            (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
            (MulAut.conj (bcGL (τ := Tag.F4) (algebraMap K Ω)
              (uK : ModGL Tag.F4 K))).toMonoidHom ∧
      Pm = ((rootSubgroup Tag.F4 K (-deltaF4)).map
            (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
            (MulAut.conj (bcGL (τ := Tag.F4) (algebraMap K Ω)
              (uK : ModGL Tag.F4 K))).toMonoidHom := by
  obtain ⟨u, huA, hufix, hplusU, hminusU⟩ :=
    f4_short_pair_descent (Ω := Ω) f hf hgA hstabplus hstabminus
  exact f4_pair_finite_endpoint_of_descent (K := K) (Ω := Ω) f hcard deltaF4
    huA hufix hplusU hminusU hPle hPmle hPfix hPmfix hPcard hPmcard

end ShortEndpoint

section Combined

variable [IsAlgClosed Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem f4_entrywiseFrobGL_canonicalRep
    (f : ℕ) (w : WeylGroup Tag.F4) :
    entrywiseFrobGL Tag.F4 Ω 2 f (canonicalRep (coxeterSystem Tag.F4) Ω w) =
      canonicalRep (coxeterSystem Tag.F4) Ω w := by
  have hm : (entrywiseFrobGL Tag.F4 Ω 2 f : ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω) =
      bcGL (τ := Tag.F4) (iterateFrobenius Ω 2 f) := by
    rw [entrywiseFrobGL, bcGL, bcEndHom_eq_entrywiseHom]
  rw [hm, bcGL_canonicalRep]

end Combined
end CFSG.StandardType.F4ExplicitPos.AmbientPairFinish
end

end
