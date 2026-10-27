module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGRealQFour
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal

@[expose] def GGSecFiveTBJTypeD4Input
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (f : ℕ) (ψ : (ggU .POmegaPlus 4 f).K →* G), StatedLieAdmissible .POmegaPlus 4 2 f →
        ψ.ker ≤ Subgroup.center (ggU .POmegaPlus 4 f).K → ψ.range = L →
          StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 f

@[expose] def GGSecFiveOrthKSLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K J : Subgroup G) (x : G),
    orderOf x = 3 → x ∈ Subgroup.normalizer (K : Set G) →
    (¬ ∀ k ∈ K, ∃ c ∈ Subgroup.center ↥K, (c : G) = k * x * k⁻¹ * x⁻¹) →
    LargeEvenMarking K (fun lab _ _ I _ θ => lab.n = 1 ∧
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = x⁻¹ * l * x) φ) →
    CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({x} : Set G) ⊓ K) →
    (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 f) →
    ∃ m : ℕ, 8 ≤ m ∧ Subgroup.center ↥K = ⊥ ∧ Nonempty (↥K ≃* ↥(StatedSL m (ZMod 2)))
end CFSG.StandardType

end
