module

public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootNative

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap

theorem native_distance_three_canonical_F4_centralizer_image_final
    {v u : CVert}
    (hvu : cgraph.dist v u = 3) :
    ∃ s c : vStab v, (s : Shat) = clabelS u ∧ (c : Shat) = clabelS v ∧
      (∃ (ρ : vStab v →* GStar) (iv : cgraph.neighborSet v ≃ rootClass),
        IsCompatLocal v ρ iv ∧ ρ s = betaStarElt) ∧
      (∀ ρ : vStab v →* GStar, Function.Surjective ρ →
        (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) →
        ρ s = betaStarElt →
          (∀ n ∈ jStar.comap ρ, Commute n s) ∧
          jStar.comap ρ ⊓ Subgroup.zpowers s = ⊥ ∧
          jStar.comap ρ ⊔ Subgroup.zpowers s = Subgroup.centralizer {s} ∧
          (∃ e : (jStar.comap ρ) × Subgroup.zpowers s ≃* Subgroup.centralizer {s},
            ∀ x, (e x : vStab v) = (x.1 : vStab v) * x.2) ∧
          ρ.ker = Subgroup.zpowers c ∧ Subgroup.zpowers c ≤ Subgroup.center (vStab v) ∧
          (∃ φ : jStar.comap ρ →* groupJ, Function.Surjective φ ∧
            φ.ker = (Subgroup.zpowers c).subgroupOf (jStar.comap ρ)) ∧
          Nat.card (jStar.comap ρ) = 6622253206732800) ∧
      Nonempty (groupJ ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
      Nat.card (Subgroup.centralizer {s}) = 13244506413465600 ∧
      (vStab u).subgroupOf (vStab v) ≤ Subgroup.centralizer {s} ∧
      ((vStab u).subgroupOf (vStab v)).relIndex (Subgroup.centralizer {s}) ≤ 102 ∧
      clabelS v ∈ vStab v ⊓ vStab u ∧ clabelS u ∈ vStab v ⊓ vStab u ∧
      clabelS u ≠ clabelS v ∧ Commute (clabelS u) (clabelS v) :=
  native_distance_three_canonical_F4_centralizer_image (labelsInput_of_ambient ambientRootOrbitsHyp)
    (outerInput_of_ambient ambientRootOrbitsHyp)
    (pathInput_of_ambient ambientRootOrbitsHyp)
    (typeThreeBoundInput_of_ambient ambientRootOrbitsHyp) hvu

theorem native_distance_three_pair_is_full_local_centralizer_final
    {v u : CVert}
    (hvu : cgraph.dist v u = 3) :
    ∃ s : vStab v, (s : Shat) = clabelS u ∧
      (vStab u).subgroupOf (vStab v) = Subgroup.centralizer {s} ∧
      (∀ ρ : vStab v →* GStar, Function.Surjective ρ →
        (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) →
        ρ s = betaStarElt →
          (vStab u).subgroupOf (vStab v) = jStar.comap ρ ⊔ Subgroup.zpowers s ∧
          jStar.comap ρ ⊓ Subgroup.zpowers s = ⊥ ∧ ∀ n ∈ jStar.comap ρ, Commute n s) ∧
      (∃ φ : (vStab v ⊓ vStab u : Subgroup Shat) →* groupJ, Function.Surjective φ ∧
        φ.ker = (Subgroup.closure {clabelS v, clabelS u}).subgroupOf (vStab v ⊓ vStab u)) ∧
      Nat.card (vStab v ⊓ vStab u : Subgroup Shat) = 13244506413465600 ∧
      (xSet v u).ncard = 3898440 ∧ (sphereDistThree v).ncard = 23113728 :=
  native_distance_three_pair_is_full_local_centralizer (labelsInput_of_ambient ambientRootOrbitsHyp)
    (outerInput_of_ambient ambientRootOrbitsHyp)
    (pathInput_of_ambient ambientRootOrbitsHyp)
    (typeThreeBoundInput_of_ambient ambientRootOrbitsHyp) hvu

theorem native_distance_three_pair_two_local_root_orbits_final
    {v u : CVert}
    (hvu : cgraph.dist v u = 3) :
    (cgraph.induce (cgraph.neighborSet u)).Connected ∧
    (cgraph.neighborSet u ∩ sphereFour v).Nonempty ∧
    (cgraph.neighborSet u \ sphereFour v).Nonempty ∧
    (∀ g ∈ vStab v ⊓ vStab u, ∀ x ∈ cgraph.neighborSet u ∩ sphereFour v,
      cvMul x g ∈ cgraph.neighborSet u ∩ sphereFour v) ∧
    (∀ x ∈ cgraph.neighborSet u ∩ sphereFour v, ∀ x' ∈ cgraph.neighborSet u ∩ sphereFour v,
      ∃ s : Shat, cvMul v s = v ∧ cvMul u s = u ∧ cvMul x s = x') ∧
    (∀ g ∈ vStab v ⊓ vStab u, ∀ y ∈ cgraph.neighborSet u \ sphereFour v,
      cvMul y g ∈ cgraph.neighborSet u \ sphereFour v) ∧
    (∀ y ∈ cgraph.neighborSet u \ sphereFour v, ∀ y' ∈ cgraph.neighborSet u \ sphereFour v,
      ∃ s : Shat, cvMul v s = v ∧ cvMul u s = u ∧ cvMul y s = y') ∧
    (cgraph.neighborSet u ∩ sphereFour v).ncard = 3898440 ∧
    (cgraph.neighborSet u \ sphereFour v).ncard = 69615 ∧
    (∃ (hc : clabelS v ∈ vStab u) (ρ : vStab u →* GStar)
        (iu : cgraph.neighborSet u ≃ rootClass),
      IsCompatLocal u ρ iu ∧ ρ ⟨clabelS v, hc⟩ = betaStarElt ∧
      (ρ.comp (Subgroup.inclusion (inf_le_right : vStab v ⊓ vStab u ≤ vStab u))).range =
        Subgroup.centralizer {betaStarElt} ∧
      (∀ z : cgraph.neighborSet u, ((z : CVert) ∈ sphereFour v ↔ cvMul z (clabelS v) ≠ z)) ∧
      ∀ z : cgraph.neighborSet u, ((z : CVert) ∉ sphereFour v ↔
        ∃ j ∈ groupJ.subgroupOf stdGroup, (iu z : stdGroup) = j * rootInv * j⁻¹)) ∧
    {z | z ∈ cgraph.neighborSet u ∧ cvMul z (clabelS v) = z} =
      cgraph.neighborSet u \ sphereFour v ∧
    ∀ w : CVert, (cgraph.induce (cgraph.neighborSet w)).Connected :=
  native_distance_three_pair_two_local_root_orbits (labelsInput_of_ambient ambientRootOrbitsHyp)
    (outerInput_of_ambient ambientRootOrbitsHyp)
    (pathInput_of_ambient ambientRootOrbitsHyp)
    (typeThreeBoundInput_of_ambient ambientRootOrbitsHyp) hvu

end CFSG.Monster.B.TwoA.Amalgam
