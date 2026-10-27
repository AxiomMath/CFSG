module

public import CFSG.Monster.B.CTIB.DistThreeProductCent
public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootNative

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
  CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical

theorem distance_three_product_determines_endpoints_final
    {v w : CVert}
    (hvw : cgraph.dist v w = 3) :
    {a : Shat | IsConj (clabelS v) a ∧ IsConj (clabelS v) (clabelS v * clabelS w * a)} =
      {clabelS v, clabelS w} ∧
    ∀ a b : Shat, IsConj (clabelS v) a → IsConj (clabelS v) b →
      clabelS v * clabelS w = a * b → ({a, b} : Set Shat) = {clabelS v, clabelS w} :=
  distance_three_product_determines_endpoints (labelsInput_of_ambient ambientRootOrbitsHyp)
    (outerInput_of_ambient ambientRootOrbitsHyp) (pathInput_of_ambient ambientRootOrbitsHyp)
    (typeThreeBoundInput_of_ambient ambientRootOrbitsHyp) hvw

theorem distance_three_product_full_centralizer_final
    {v w : CVert} (hvw : cgraph.dist v w = 3)
    {R F C : Subgroup Shat}
    (hR : R = Subgroup.centralizer {clabelS v, clabelS w}) (hF : F = ⁅R, R⁆)
    (hC : C = Subgroup.centralizer {clabelS v * clabelS w}) :
    (∀ g : Shat, g ∈ C ↔
      (fun x => g * x * g⁻¹) '' {clabelS v, clabelS w} = {clabelS v, clabelS w}) ∧
    R = vStab v ⊓ vStab w ∧ R ≤ C ∧ R.relIndex C = 2 ∧ (F.subgroupOf C).Normal ∧
    Nat.card C = 26489012826931200 ∧ Nat.card C = 8 * Nat.card (adjointGroup Tag.F4 (ZMod 2)) ∧
    Nat.card (C ⧸ F.subgroupOf C) = 8 ∧ Nat.card F = 3311126603366400 ∧
    CFSG.IsComponent (F.subgroupOf C) ∧
    (∀ K : Subgroup C, CFSG.IsComponent K → K = F.subgroupOf C) ∧
    F = pairF4 v w ∧ IsSimpleGroup F ∧ IsSimpleGroup (adjointGroup Tag.F4 (ZMod 2)) ∧
    (∃ Ψ : groupJ ≃* adjointGroup Tag.F4 (ZMod 2),
      (∀ (g : twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))) (x : groupJ),
        ((x : ModGL Tag.E6 K) : ModGL TwistTag.E6.tag K) =
            baseChangeGL (algebraMap (ZMod 2) K) (g : ModGL TwistTag.E6.tag (ZMod 2)) →
          (Ψ x : ModGL Tag.F4 (ZMod 2)) = e6FixedToF4 (ZMod 2) g) ∧
      ∀ ρ : vStab v →* GStar, Function.Surjective ρ →
        (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) →
        ∀ s : vStab v, (s : Shat) = clabelS w → ρ s = betaStarElt →
          ∃ φ : F ≃* groupJ,
            (∀ (f : F) (y : vStab v), (y : Shat) = f →
              ρ y = SemidirectProduct.inl ⟨(φ f : ModGL Tag.E6 K), groupJ_le_stdGroup (φ f).2⟩) ∧
            ∃ e : F ≃* adjointGroup Tag.F4 (ZMod 2), ∀ f, e f = Ψ (φ f)) ∧
    ∀ K : Subgroup C, CFSG.IsComponent K →
      IsSimpleGroup (K ⧸ Subgroup.center K) ∧ 17 ∣ Nat.card (K ⧸ Subgroup.center K) :=
  distance_three_product_full_centralizer (labelsInput_of_ambient ambientRootOrbitsHyp)
    (outerInput_of_ambient ambientRootOrbitsHyp) (pathInput_of_ambient ambientRootOrbitsHyp)
    (typeThreeBoundInput_of_ambient ambientRootOrbitsHyp) hvw hR hF hC

end CFSG.Monster.B.CTIB
