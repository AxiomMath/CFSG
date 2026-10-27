module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_9_C2Emb (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 3 ≤ CFSG.Open.pRank 2 D.Z →
    ∀ hV : IsElemAbelian 2 c.V,
      let Lstar : Subgroup (MulAut (Vtil ⊥ c.V hV)) := barSub ⊥ c.V hV c.L
      let n : ℕ := CFSG.Open.pRank 2 D.Z
      (IsOmegaPlus ↥Lstar 6 n ∧ NatOmegaPlus Lstar ⊤ ⊥ 6 n) →
        ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card ↥(Hinf (D.M ⊓ c.L)) ∧
          ∀ x ∈ Hinf (D.M ⊓ c.L), orderOf x = p →
            Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ D.M

@[expose] def KGenO6p : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
    IsNaturalClassicalModule H n → ⁅H, H⁆ = H → 3 ≤ n →
      letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
      letI : MulAction ↥H W := MulAction.compHom W H.subtype
      letI : MulAction ↥H (Set W) := Set.mulActionSet
      ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        let ℓ : Subgroup W := fixedPointSubgroup ↥S W
        let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
        let Kstar : Subgroup ↥H := Hinf Pℓ
        (IsOmegaPlus ↥H 6 n ∧ NatOmegaPlus H ⊤ ⊥ 6 n) →
          ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card ↥Kstar →
            ∃ X : Subgroup ↥H, X ≤ Kstar ∧ Nat.card ↥X = p ∧
              ∃ w : ↥H, w ∉ Pℓ ∧ ∀ x ∈ X, w * x * w⁻¹ ∈ X

@[expose] def KSchurO6p : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal],
    ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ →
      Z ≤ Subgroup.center X → Odd (Nat.card ↥Z) →
      (∃ n : ℕ, 3 ≤ n ∧ IsOmegaPlus (X ⧸ Z) 6 n) →
      Z = ⊥

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
