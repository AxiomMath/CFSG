module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

@[expose] def KAdjAt (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ) :
    Prop :=
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  ∀ S : Sylow 2 ↥H,
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    let ℓ : Subgroup W := fixedPointSubgroup ↥S W
    let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
    let Kstar : Subgroup ↥H := Hinf Pℓ
    Kstar ≠ ⊥ →
    ∀ Tstar : Subgroup (MulAut W),
      Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
      IsPGroup 2 ↥Tstar →
      (S : Subgroup ↥H).map H.subtype ≤ Tstar →
      let Good : Subgroup ↥H → Prop := fun Pstar =>
        IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
        (∀ t ∈ Tstar,
          (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
        ¬ Pstar ≤ Pℓ
      ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
      ∀ r : ℕ, r.Prime → r ≠ 2 →
        ((∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
          (∃ k : ℕ, n = 2 ^ k ∧ r = 3)) →
      ∀ t ∈ Hinf Pstar ⊓ Pℓ, orderOf t = r → t ∉ fixingSubgroupOf ↥H W (ℓ : Set W) →
        ∃ m : ℕ, (m = n ∨ m = 2 * n ∨
          (n = 2 * m ∧ IsSUn ↥H 4 m ∧ NatSUn H ⊤ ⊥ 4 m)) ∧
        ∃ X₁ X₂ : Subgroup ↥H, X₁ ≤ Kstar ∧ X₂ ≤ Kstar ∧
          (∀ N : Subgroup ↥H, N ≤ Kstar →
            Kstar ≤ Subgroup.normalizer (N : Set ↥H) → X₁ ≤ N → X₂ ≤ N → N = Kstar) ∧
          ∀ X : Subgroup ↥H, (X = X₁ ∨ X = X₂) →
            IsSLn ↥X 2 m ∧ t ∈ Subgroup.normalizer (X : Set ↥H) ∧
              ∃ d ∈ X, orderOf d = r ∧ ∀ x ∈ X, t * x * t⁻¹ = d * x * d⁻¹

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
