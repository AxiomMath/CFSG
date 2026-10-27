module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Open


@[expose] def TwE6EnnolaUpgrade : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → ringChar K = 2 → ∀ p : ℕ, p.Prime → p ∣ q + 1 →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ q) →
    ∀ v : WeylGroup TwistTag.E6.tag,
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
    ∀ t ∈ twistedE6InndiagGL K σ, ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ →
    ∀ ζ : (AlgebraicClosure K)ˣ, ζ ^ p = 1 → ζ ≠ 1 →
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
        rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ) →
      ∃ v' : WeylGroup TwistTag.E6.tag,
        (∀ γ' : Fin TwistTag.E6.tag.rank → ℤ, v' • permLattice TwistTag.E6.perm γ' = -γ') ∧
        ∃ g0' ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
          twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0' =
            g0' * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v' ∧
          g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0' =
            rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ)

@[expose] def TwE6CorootCoreGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → ringChar K = 2 → ∀ p : ℕ, p.Prime → p ∣ q + 1 →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ q) →
    ∀ v : WeylGroup TwistTag.E6.tag,
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
    ∀ t ∈ twistedE6InndiagGL K σ, ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ →
    ∀ ζ : (AlgebraicClosure K)ˣ, ζ ^ p = 1 → ζ ≠ 1 →
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
        rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ) →
      ∃ X D : Subgroup ↥(twistedE6RootGroup K σ),
        (Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
            (twistedE6RootGroup K σ) = X ⊔ D ∧
          IsCyclic X ∧ Odd (Nat.card X) ∧ X ≤ Subgroup.centralizer (D : Set _) ∧
          CFSG.IsQuasisimple D ∧ Subgroup.center D = ⊥ ∧ 7 ∣ Nat.card D ∧ q ^ 15 ∣ Nat.card D ∧
          ∀ s ∈ twistedE6InndiagGL K σ, s * t = t * s →
            (∀ d ∈ D, s * (d : ModGL TwistTag.E6.tag K) = (d : ModGL TwistTag.E6.tag K) * s) →
              s ∈ X.map (twistedE6RootGroup K σ).subtype

theorem twE6CorootCoreGen_of_upgrade (hU : TwE6EnnolaUpgrade) (hC : TwE6CorootCore) :
    TwE6CorootCoreGen := by
  intro K _ _ σ q hK hσ h2 p hp hpq Fr hFr v g0 hg0C hg0 t ht γ hγ ζ hζ hζ1 hcor
  obtain ⟨v', hv', g0', hg0'C, hg0', hcor'⟩ :=
    hU K σ q hK hσ h2 p hp hpq Fr hFr v g0 hg0C hg0 t ht γ hγ ζ hζ hζ1 hcor
  exact hC K σ q hK hσ h2 p hp hpq Fr hFr v' hv' g0' hg0'C hg0' t ht γ hγ ζ hζ hζ1 hcor'

theorem twE6CorootCore_of_gen (hG : TwE6CorootCoreGen) : TwE6CorootCore :=
  fun K _ _ σ q hK hσ h2 p hp hpq Fr hFr v _ g0 hg0C hg0 t ht γ hγ ζ hζ hζ1 hcor =>
    hG K σ q hK hσ h2 p hp hpq Fr hFr v g0 hg0C hg0 t ht γ hγ ζ hζ hζ1 hcor

@[expose] def TwE6OuterRankFour : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → ringChar K = 2 → 3 ∣ q + 1 →
    ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ twistedE6InndiagGL K σ → IsElemAbelian 3 A →
      Nat.card A = 3 ^ 4 →
      (∃ U : Subgroup (MulAut ↥(twistedE6RootGroup K σ)), U ≠ ⊥ ∧ IsPGroup 2 U ∧
          (∀ u ∈ U, u ∈ (twistedE6InndiagConj K σ).range → u = 1) ∧
          ∀ a : ↥(twistedE6InndiagGL K σ), (a : ModGL TwistTag.E6.tag K) ∈ A → ∀ u ∈ U,
            twistedE6InndiagConj K σ a * u * (twistedE6InndiagConj K σ a)⁻¹ ∈ U) →
      ∃ D : TwLangData K σ q A, D.c = 1 ∧ ∃ γ : Fin TwistTag.E6.tag.rank → ℤ,
        IsRoot TwistTag.E6.tag γ ∧ ∃ ζ : (AlgebraicClosure K)ˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧ ∃ x ∈ A,
          rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ) =
            D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0

end Open

end CFSG.StandardType.TwE6RootAs

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGEndNodeAdmLow (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → Nat.card A < p ^ (r + 1) →
      GGAdmissible p L' A →
      ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
        ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)

@[expose] def GGTwE6EndNodeThreeRankFour : Prop :=
  GGTwE6All fun p r R _ I => p = 3 → GGEndNodeAdmLow p r R I

end CFSG.StandardType

end
