module

public import CFSG.LocalAnalysis.StandardType.GGE6KGLayerDefs
public import CFSG.LocalAnalysis.StandardType.GGKGAutDict
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
public import CFSG.Open.StatedDefs

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.NoOffRest CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


structure KGTwFrame (n : ℕ) {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {R : Type} [Group R]
    (Θ : R ≃* ↥(twistedE6RootGroup K σ)) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1) {L' : Type} [Group L'] (ψ : L' →* R)
    (A : Subgroup (MulAut L')) (v : WeylGroup TwistTag.E6.tag)
    (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (κ : A →* Multiplicative (Fin 6 → ZMod 3))
    (t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K) : Prop where
  hFr : ∀ c, Fr c = c ^ 2 ^ n
  hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ
  hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K)
  hgF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
    g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v
  aut : KGAutFrame A κ
  ht : ∀ x, t x ∈ twistedE6InndiagGL K σ ∧
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
      g * rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) * g⁻¹
  conj : ∀ (a : A) (l : L'),
    ((Θ (ψ ((a : MulAut L') l)) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
      t (Multiplicative.toAdd (κ a)) *
        ((Θ (ψ l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
          (t (Multiplicative.toAdd (κ a)))⁻¹

@[expose] def GGTwKGFrame : Prop :=
  ∀ (n : ℕ), 1 ≤ n → 3 ∣ 2 ^ n + 1 → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (2 ^ n) ^ 2 → ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ 2 ^ n) →
    ∀ ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n,
      (∀ x : MulAut ↥(twistedE6RootGroup K σ),
        MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range) →
    ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K), (∀ c, Fr c = c ^ 2 ^ n) →
    ∀ (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1), orderOf ζ = 3 →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K n)
      (A : Subgroup (MulAut L')),
      GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A →
      Nat.card A = 3 ^ 5 →
      ∃ (v : WeylGroup TwistTag.E6.tag) (g : ModGL TwistTag.E6.tag (AlgebraicClosure K))
        (κ : A →* Multiplicative (Fin 6 → ZMod 3))
        (t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K),
        KGTwFrame n σ ε.symm Fr ζ hζ ψ A v g κ t

@[expose] def GGTwE6D4LayerInput : Prop :=
  ∀ (n : ℕ), 1 ≤ n → 3 ∣ 2 ^ n + 1 → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 2 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ 2 ^ n) →
    ∀ v : WeylGroup TwistTag.E6.tag,
      (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) →
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
    ∀ α β : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → IsRoot TwistTag.E6.tag β →
      iform α β = 0 →
    ∀ (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1), ζ ≠ 1 →
    ∀ t ∈ twistedE6InndiagGL K σ, ∀ ta ∈ twistedE6InndiagGL K σ,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
        rootDiagUnit TwistTag.E6.tag
          (TwE6RootAs.corootTuple α ζ * TwE6RootAs.corootTuple β ζ) →
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ta * g0 =
        rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple α ζ) →
      ∃ E : Subgroup ↥(twistedE6RootGroup K σ),
        GGLayerOf ((Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
          (twistedE6RootGroup K σ)) E ∧
        ∃ j ∈ E,
          (∀ x ∈ hypE6, ∃ y ∈ hypE6, ∀ s ∈ twistedE6InndiagGL K σ,
            g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) s * g0 =
                rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ x) →
              g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  ((j : ModGL TwistTag.E6.tag K) * s * (j : ModGL TwistTag.E6.tag K)⁻¹) * g0 =
                rootDiagUnit TwistTag.E6.tag (zetaVec (τ := Tag.E6) ζ hζ y)) ∧
          (j : ModGL TwistTag.E6.tag K) * ta * (j : ModGL TwistTag.E6.tag K)⁻¹ ≠ ta

@[expose] def GGTwE6A3LayerInput : Prop :=
  ∀ (n : ℕ), 1 ≤ n → 3 ∣ 2 ^ n + 1 → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 2 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ 2 ^ n) →
    ∀ v : WeylGroup TwistTag.E6.tag,
      (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) →
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
    ∀ α β : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → IsRoot TwistTag.E6.tag β →
      iform α β = 0 →
    ∀ (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1), ζ ≠ 1 →
    ∀ ta ∈ twistedE6InndiagGL K σ, ∀ tb ∈ twistedE6InndiagGL K σ,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ta * g0 =
        rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple α ζ) →
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) tb * g0 =
        rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple β ζ) →
      ∃ E : Subgroup ↥(twistedE6RootGroup K σ),
        GGLayerOf ((Subgroup.centralizer ({ta, tb} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
          (twistedE6RootGroup K σ)) E ∧
        Nonempty (↥E ≃* ↥(StatedSU 4 (2 ^ n) K)) ∧
        ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → iform γ α = 0 →
          iform γ β = 0 → ∀ tc ∈ twistedE6InndiagGL K σ,
            g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) tc * g0 =
                rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) →
              tc ∈ E.map (twistedE6RootGroup K σ).subtype

end CFSG.StandardType.KGL

end
