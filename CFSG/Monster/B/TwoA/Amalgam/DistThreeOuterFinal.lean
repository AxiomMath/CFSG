module

public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeSplit
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootNative

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
  CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical

theorem native_distance_three_label_is_outer_local_involution_final
    {v u : CVert}
    (hu : u ∈ sphereDistThree v) :
    clabelS u ∈ vStab v ∧
    (∀ y : vStab v, (y : Shat) = clabelS u → y ∉ commutator (vStab v)) ∧
    ∀ ρ : vStab v →* GStar, Function.Surjective ρ → ∀ y : vStab v, (y : Shat) = clabelS u →
      (ρ y).right ≠ 1 ∧ ρ y ∉ E6.Ginl :=
  native_distance_three_label_is_outer_local_involution_of
    (distThreePathFact_of_ambient ambientRootOrbitsHyp) distThreeBaseTransvFact_holds hu

theorem native_distance_three_single_orbit_and_8064_paths_final :
    (∀ v u u' : CVert, u ∈ sphereDistThree v → u' ∈ sphereDistThree v →
      ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u') ∧
    (∀ v w : CVert, w ∈ sphereFour v →
      (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 8064 ∧
        ∀ u ∈ cgraph.neighborSet w ∩ sphereDistThree v,
          pairStabOrbit w v u = cgraph.neighborSet w ∩ sphereDistThree v) ∧
    (∀ v w : CVert, w ∈ sphereThree v → Disjoint (cgraph.neighborSet w) (sphereDistThree v)) ∧
    (∀ v u : CVert, u ∈ sphereDistThree v → (xSet v u).Nonempty ∧
      (∀ w ∈ xSet v u, ∀ w' ∈ xSet v u,
        ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u ∧ cvMul w g = w') ∧
      ∀ w ∈ xSet v u, Nat.card ↥(vStab v ⊓ vStab u ⊓ vStab w) = 3397386240) ∧
    (∀ v u : CVert, u ∈ sphereDistThree v → (xSet u v).Nonempty ∧
      (∀ w ∈ xSet u v, ∀ w' ∈ xSet u v,
        ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u ∧ cvMul w g = w') ∧
      ∀ w ∈ xSet u v, Nat.card ↥(vStab v ⊓ vStab u ⊓ vStab w) = 3397386240) :=
  distThreePaths_of_ambient ambientRootOrbitsHyp

theorem native_distance_three_pair_split_pinned_F4_final
    {v u : CVert}
    (hvu : cgraph.dist v u = 3) :
    pairF4 v u = ⁅vStab v ⊓ vStab u, vStab v ⊓ vStab u⁆ ∧
    (∃ e : pairF4 v u × Subgroup.closure ({clabelS v, clabelS u} : Set Shat) ≃*
        (vStab v ⊓ vStab u : Subgroup Shat), ∀ x, (e x : Shat) = x.1 * x.2) ∧
    (∃ s : vStab v, (s : Shat) = clabelS u ∧ ∃ (ρ : vStab v →* GStar)
        (iv : cgraph.neighborSet v ≃ rootClass), IsCompatLocal v ρ iv ∧ ρ s = betaStarElt) ∧
    ∃ Ψ : groupJ ≃* adjointGroup Tag.F4 (ZMod 2),
      (∀ (g : twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))) (x : groupJ),
        ((x : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) =
            baseChangeGL (algebraMap (ZMod 2) K) (g : ModGL TwistTag.E6.tag (ZMod 2)) →
          (Ψ x : ModGL Tag.F4 (ZMod 2)) = e6FixedToF4 (ZMod 2) g) ∧
      ∀ ρ : vStab v →* GStar, Function.Surjective ρ →
        (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) →
        ∀ s : vStab v, (s : Shat) = clabelS u → ρ s = betaStarElt →
          ∃ φ : pairF4 v u ≃* groupJ,
            (∀ (f : pairF4 v u) (y : vStab v), (y : Shat) = f →
              ρ y = SemidirectProduct.inl ⟨(φ f : ModGL Tag.E6 K), groupJ_le_stdGroup (φ f).2⟩) ∧
            (∃ e : pairF4 v u ≃* adjointGroup Tag.F4 (ZMod 2), ∀ f, e f = Ψ (φ f)) ∧
            (∃ e : pairF4 v u × Subgroup.zpowers (clabelS v) ≃* jStar.comap ρ,
              ∀ x, ((e x : vStab v) : Shat) = x.1 * x.2) ∧
            (pairF4 v u).subgroupOf (vStab v) ≤ jStar.comap ρ ∧
            Subgroup.zpowers (cStab v) ⊓ (pairF4 v u).subgroupOf (vStab v) = ⊥ ∧
            Subgroup.zpowers (cStab v) ⊔ (pairF4 v u).subgroupOf (vStab v) = jStar.comap ρ :=
  native_distance_three_pair_split_pinned_F4 (labelsInput_of_ambient ambientRootOrbitsHyp)
    (outerInput_of_ambient ambientRootOrbitsHyp) (pathInput_of_ambient ambientRootOrbitsHyp)
    (typeThreeBoundInput_of_ambient ambientRootOrbitsHyp) hvu

end CFSG.Monster.B.TwoA.Amalgam
