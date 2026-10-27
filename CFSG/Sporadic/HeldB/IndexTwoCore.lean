module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.ComponentClassification CFSG.ComponentClassification.FixedCommutingProduct

theorem twoComponent_quasisimple_of_involutive {M : Type*} [Group M] [Finite M]
    [IsSimpleGroup M] (hnonab : ∃ a b : M, a * b ≠ b * a)
    (hfix : ∀ α : MulAut M, orderOf α = 2 → ∀ L : Subgroup (fixedSubgroup α),
      CFSG.IsPComponent 2 L → CFSG.IsQuasisimple L)
    (α : MulAut M) (hinv : Function.Involutive α) (L : Subgroup (fixedSubgroup α))
    (hL : TwoComponents.IsTwoComponent L) : CFSG.Open.IsQuasisimple L := by
  have hL2 := (CatalogueBAlternating.pComponent_two_iff L).mpr hL
  have hsq : α * α = 1 := MulEquiv.ext fun x => hinv x
  by_cases h1 : α = 1
  · subst h1
    have htop : fixedSubgroup (1 : MulAut M) = ⊤ := by
      ext x
      exact ⟨fun _ => Subgroup.mem_top x, fun _ => rfl⟩
    let e : fixedSubgroup (1 : MulAut M) ≃* M :=
      (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have hM : CFSG.IsQuasisimple M := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
    have hfix1 : CFSG.IsQuasisimple (fixedSubgroup (1 : MulAut M)) :=
      CatalogueBAlternating.quasisimple_iff_native.mpr
        (Components.quasisimple_of_equiv e (CatalogueBAlternating.quasisimple_iff_native.mp hM))
    have hLtop := CatalogueBAlternatingIsometry.pComponent_eq_top_of_quasisimple hfix1 2 L hL2
    rw [hLtop]
    exact Components.quasisimple_of_equiv Subgroup.topEquiv
      (CatalogueBAlternating.quasisimple_iff_native.mp hfix1)
  · exact CatalogueBAlternating.quasisimple_iff_native.mp
      (hfix α (orderOf_eq_prime (by rw [sq]; exact hsq) h1) L hL2)

theorem index_two_B_of_fixed_model {G M : Type} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)] [Group M] [Finite M]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (ψ : GeneralizedFitting.subgroup G ≃* M)
    (hfix : ∀ α : MulAut M, orderOf α = 2 → ∀ L : Subgroup (fixedSubgroup α),
      CFSG.IsPComponent 2 L → CFSG.IsQuasisimple L)
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G := by
  have : IsSimpleGroup M := ψ.symm.isSimpleGroup
  have hnonabM : ∃ a b : M, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨ψ a, ψ b, fun h => hab (ψ.injective (by rw [map_mul, map_mul, h]))⟩
  have hbad : ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := fun S hne htwo =>
    CatalogueRelativeB.local_bad_eq_bot_of_simple_generalizedFitting_model hnonab hindex ψ
      (twoComponent_quasisimple_of_involutive hnonabM hfix) hproper S hne htwo
  refine ⟨hbad, fun S hne htwo => ?_⟩
  rw [hbad S hne htwo, Subgroup.map_bot]
  exact bot_le

end CFSG.Sporadic.HeldB
