module

public import CFSG.LocalAnalysis.StandardType.GGE6KGLayerDefs
public import CFSG.LocalAnalysis.StandardType.GGFamCentralizerBridge
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelDefs

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.LayerSixE
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def kgExpVec (β : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ZMod 3 :=
  fun i => (((Tag.E6.cartan.mulVec β) i : ℤ) : ZMod 3)


@[expose] def KGAdjL1 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 → ∀ (ζ : Kˣ) (hζ : ζ ^ 3 = 1),
    orderOf ζ = 3 → ∀ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β →
      GGLayerOf ((famCentralizer {zetaVec ζ hζ (kgExpVec β)}).map (adjointGroup Tag.E6 K).subtype)
        (rootSpan Tag.E6 K (famKernel {zetaVec ζ hζ (kgExpVec β)}))

@[expose] def KGAdjL2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 → ∀ (ζ : Kˣ) (hζ : ζ ^ 3 = 1),
    orderOf ζ = 3 → ∀ α β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → IsRoot Tag.E6 β →
      iform α β = 0 →
      GGLayerOf
        ((famCentralizer {zetaVec ζ hζ (kgExpVec α + kgExpVec β)}).map
          (adjointGroup Tag.E6 K).subtype)
        (rootSpan Tag.E6 K (famKernel {zetaVec ζ hζ (kgExpVec α + kgExpVec β)}))

@[expose] def KGAdjL3i : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 → ∀ (ζ : Kˣ) (hζ : ζ ^ 3 = 1),
    orderOf ζ = 3 → ∀ α β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → IsRoot Tag.E6 β →
      iform α β = 0 →
      GGLayerOf
        ((famCentralizer {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)}).map
          (adjointGroup Tag.E6 K).subtype)
        (rootSpan Tag.E6 K (famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)}))

@[expose] def KGAdjL3ii : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 → ∀ (ζ : Kˣ) (hζ : ζ ^ 3 = 1),
    orderOf ζ = 3 → ∀ α β γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → IsRoot Tag.E6 β →
      iform α β = 0 → IsRoot Tag.E6 γ → iform γ α = 0 → iform γ β = 0 →
      rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec γ)) ∈
        rootSpan Tag.E6 K (famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)})

@[expose] def KGAdjL4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 → ∀ (ζ : Kˣ) (hζ : ζ ^ 3 = 1),
    orderOf ζ = 3 → ∀ α β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → IsRoot Tag.E6 β →
      iform α β = 0 →
      ∃ j ∈ rootSpan Tag.E6 K (famKernel {zetaVec ζ hζ (kgExpVec α + kgExpVec β)}),
        (∀ x ∈ hypE6, ∃ y ∈ hypE6,
          j * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * j⁻¹ = rootDiagUnit Tag.E6 (zetaVec ζ hζ y)) ∧
        j * rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) * j⁻¹ ≠
          rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α))

@[expose] def KGAdjM : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 → ∀ (ζ : Kˣ) (hζ : ζ ^ 3 = 1),
    orderOf ζ = 3 → ∀ α β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → IsRoot Tag.E6 β →
      iform α β = 0 →
      ∀ (N : Type) [Group N] [Finite N]
        (π : N →* ↥(rootSpan Tag.E6 K
          (famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)}))),
        Function.Surjective π → π.ker ≤ Subgroup.center N → commutator N = ⊤ →
          IsCyclic (Subgroup.center N)

@[expose] def KGFrameE6 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
    ∀ (ζ : Kˣ) (hζ : ζ ^ 3 = 1), orderOf ζ = 3 →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* RecipeGroup Tag.E6 K)
      (A : Subgroup (MulAut L')),
      GGTorusTBGroup 3 5 (RecipeGroup Tag.E6 K) (RecipeID Tag.E6 K) L' ψ A → Nat.card A = 3 ^ 5 →
      ∃ (g : ModGL Tag.E6 K) (κ : A →* Multiplicative (Fin 6 → ZMod 3)),
        g ∈ adjointGroup Tag.E6 K ∧ Function.Injective κ ∧
        (∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ hypE6) ∧
        (∀ (a : A) (l : L'),
          ((recipeEquiv Tag.E6 K (ψ ((a : MulAut L') l)) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
            (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹) *
              ((recipeEquiv Tag.E6 K (ψ l) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) *
              (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹)⁻¹) ∧
        (∀ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) →
          ∃ u : WeylGroup Tag.E6, ∀ a b : A,
            (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
              Multiplicative.toAdd (κ b) = adAct Tag.E6 3 u (Multiplicative.toAdd (κ a))) ∧
        (∀ i : Fin 6, ∃ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
          ∀ a b : A, (b : MulAut L') = MulAut.conj m * (a : MulAut L') * (MulAut.conj m)⁻¹ →
            Multiplicative.toAdd (κ b) = adRefl Tag.E6 3 i (Multiplicative.toAdd (κ a)))

end CFSG.StandardType.KGL

end
