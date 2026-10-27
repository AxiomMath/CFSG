module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def R18_1_1At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  V₀ ≠ ⊥ →
    (MBarGT D.M V₀ V (bBar (conjClosure D.M L) D.M V₀ V h.hyp125.isElemAbelian + 1) ∨
        calO 1 D.M V₀ V = ∅) →
    barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥ →
    (mBar D.M V₀ V h.hyp125.isElemAbelian : ℕ∞) < rMV D.M V

@[expose] def R18_1_2At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  V₀ ≠ ⊥ →
    (MBarGT D.M V₀ V (bBar (conjClosure D.M L) D.M V₀ V h.hyp125.isElemAbelian + 1) ∨
        calO 1 D.M V₀ V = ∅) →
    barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L) ≠ ⊥ →
    Concl18_1_2 D V₀ V h.hyp125.isElemAbelian

@[expose] def R18_2At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  V₀ ≠ ⊥ → ∀ (j : ℕ) (Δ : Set (Subgroup G)), Hyp1222 D V₀ V L j Δ →
    (conjClosure D.M L ⊔ D.T ∈ Δ) →
    (∀ H ∈ Δ, ((S17.oUpperTwo H).subgroupOf D.M).Normal) →
    (∀ K : Subgroup G, D.T ≤ K → K ≤ ⨆ H ∈ Δ, H →
        barSub V₀ V h.hyp125.isElemAbelian K =
          ⨆ H ∈ Δ, barSub V₀ V h.hyp125.isElemAbelian H →
        calMOf K = {D.M}) →
    (mBar D.M V₀ V h.hyp125.isElemAbelian : ℕ∞) ≤ fIndexMax Δ + 1

@[expose] def R18_3At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) : Prop :=
  IsAlt (Bar2 L) 5 → V₀ = ⊥ →
    UniqueMax D.M (D.M ⊓ normalizer (F12.Wi 1 D.T V : Set G)) →
    UniqueMax D.M (L ⊔ F12.Wi 1 D.T V)

@[expose] def R18_4At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) : Prop :=
  ¬ IsAlt (Bar2 L) 5

@[expose] def R18_8At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ¬ P18_6_5 D V₀ V p L h

@[expose] def R18_9At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ¬ P18_6_4 D V₀ V p L h

@[expose] def R18_10At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  P18_6_2 D V₀ V p L h →
    ∃ n : ℕ,
      IsSUn ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 n ∨
        IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 6 n ∨
        IsOmegaPlus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 n

@[expose] def R18_11At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ¬ ∃ n : ℕ, IsSp4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) n

@[expose] def R18_12At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ¬ ∃ n : ℕ, IsL2 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) n

@[expose] def R18_13At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  P18_13_1 D V₀ V p L h ∨ (∃ s : ℕ, P18_13_2 D V₀ V p L h s) ∨ P18_13_3 D V₀ V p L h

@[expose] def R18_14_1At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  let H := barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)
  ∀ (n : ℕ), 2 ≤ n → IsSUn ↥H 4 n → ∀ (F : Type) [Field F] [Finite F],
    Nat.card F = (2 ^ n) ^ 2 → ∀ (ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F))
      (ψ : Vtil V₀ V h.hyp125.isElemAbelian ≃* Multiplicative (Fin 4 → F)),
      NatCoordsSU4 H n F ε ψ → ∀ (v : G) (hv : v ∈ V), v ∉ V₀ →
        ((∑ i, (Multiplicative.toAdd (ψ (tilOf V₀ V h.hyp125.isElemAbelian v hv))) i ^
              (2 ^ n + 1)) ≠ 0 →
            IsSU3 (Bar2 (Opp p (centVec H (tilOf V₀ V h.hyp125.isElemAbelian v hv)))) n) ∧
          ((∑ i, (Multiplicative.toAdd (ψ (tilOf V₀ V h.hyp125.isElemAbelian v hv))) i ^
                (2 ^ n + 1)) = 0 →
            IsL2 (Bar2 (Opp p (centVec H (tilOf V₀ V h.hyp125.isElemAbelian v hv)))) n)

@[expose] def R18_14_2At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  let H := barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)
  (∃ s : ℕ, P18_13_2 D V₀ V p L h s) →
    ∀ (n : ℕ), 2 ≤ n → IsOmegaMinus ↥H 6 n →
      (∀ (v : G) (hv : v ∈ V), v ∉ V₀ →
          p ∈ piSet (Opp p (centVec H (tilOf V₀ V h.hyp125.isElemAbelian v hv)))) ∧
        (∀ (W' : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian))
            (hW' : ∀ x ∈ H, ∀ s ∈ W', x s ∈ W'), NatOmegaMinus H W' ⊥ 6 n →
          ∀ (F : Type) [Field F] [Finite F] (b c : F), Nat.card F = 2 ^ n →
            (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
            ∀ (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
              (ψ : W' ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
              NatCoordsOmegaMinusOn H W' hW' F b c ε ψ →
              ∀ (v : G) (hv : v ∈ V), v ∉ V₀ →
                ∀ hmem : tilOf V₀ V h.hyp125.isElemAbelian v hv ∈ W',
                  (StatedQuadMinus 3 F b c
                      (Multiplicative.toAdd (ψ ⟨tilOf V₀ V h.hyp125.isElemAbelian v hv, hmem⟩)) = 0 →
                    IsL2 (Bar2 (Opp p (centVec H
                      (tilOf V₀ V h.hyp125.isElemAbelian v hv)))) (2 * n)) ∧
                  (StatedQuadMinus 3 F b c
                      (Multiplicative.toAdd (ψ ⟨tilOf V₀ V h.hyp125.isElemAbelian v hv, hmem⟩)) ≠ 0 →
                    IsSp4 (Bar2 (Opp p (centVec H
                      (tilOf V₀ V h.hyp125.isElemAbelian v hv)))) n))

@[expose] def R18_14_3At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  let H := barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)
  ∀ (n : ℕ), 2 ≤ n → IsOmegaPlus ↥H 4 n → ∀ (F : Type) [Field F] [Finite F],
    Nat.card F = 2 ^ n → ∀ (ε : ↥H ≃* ↥(StatedOmega (StatedQuadPlus 2 F)))
      (ψ : Vtil V₀ V h.hyp125.isElemAbelian ≃* Multiplicative (Fin 2 ⊕ Fin 2 → F)),
      NatCoordsOmegaPlus H F ε ψ → ∀ (v : G) (hv : v ∈ V), v ∉ V₀ →
        (StatedQuadPlus 2 F
              (Multiplicative.toAdd (ψ (tilOf V₀ V h.hyp125.isElemAbelian v hv))) = 0 →
            Opp p (centVec H (tilOf V₀ V h.hyp125.isElemAbelian v hv)) = ⊥) ∧
          (StatedQuadPlus 2 F
                (Multiplicative.toAdd (ψ (tilOf V₀ V h.hyp125.isElemAbelian v hv))) ≠ 0 →
            IsL2 (Bar2 (Opp p (centVec H (tilOf V₀ V h.hyp125.isElemAbelian v hv)))) n)

@[expose] def R18_14At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  R18_14_1At D V₀ V p L h ∧ R18_14_2At D V₀ V p L h ∧ R18_14_3At D V₀ V p L h

@[expose] def R18_15At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) : Prop :=
  ∀ (v : G) (hv : v ∈ V), v ≠ 1 → p ∈ piSet (D.M ⊓ centralizer ({v} : Set G))

@[expose] def R18_16_1At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  P18_13_1 D V₀ V p L h → ((4 * S17.nOf L + 1 : ℕ) : ℕ∞) ≤ rMV D.M V

@[expose] def R18_16_2At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∀ s : ℕ, P18_13_2 D V₀ V p L h s → ((4 * S17.nOf L + 1 : ℕ) : ℕ∞) ≤ rMV D.M V

@[expose] def R18_17_1At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  P18_13_1 D V₀ V p L h → ((2 * S17.nOf L : ℕ) : ℕ∞) ≤ deltaInf D.M V

@[expose] def R18_17_2At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∀ s : ℕ, P18_13_2 D V₀ V p L h s → ((2 * S17.nOf L * s : ℕ) : ℕ∞) ≤ deltaInf D.M V

@[expose] def R18_17_3At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  P18_13_3 D V₀ V p L h → ((2 * S17.nOf L : ℕ) : ℕ∞) ≤ deltaInf D.M V

@[expose] def R18_17At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  R18_17_1At D V₀ V p L h ∧ R18_17_2At D V₀ V p L h ∧ R18_17_3At D V₀ V p L h

@[expose] def R18_19At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ¬ P18_13_3 D V₀ V p L h

@[expose] def R18_20At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∀ s : ℕ, P18_13_2 D V₀ V p L h s → s = 1

@[expose] def R18_21At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ¬ P18_13_1 D V₀ V p L h

@[expose] def R18_22At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  P18_13_2 D V₀ V p L h 1

@[expose] def R18_23At (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) : Prop :=
  centralizer (F12.Ci 2 D.T V : Set G) ≤ D.M

@[expose] def R18_24At (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  1 < mSub V₀

@[expose] def R18_24 (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V), R18_24At D V₀ V hV

@[expose] def R18_24Of1669At (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hm : MBarGT D.M V₀ V 3) : Prop :=
  1 < mSub V₀

@[expose] def R18_24Of1669 (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) (hm : MBarGT D.M V₀ V 3),
    R18_24Of1669At D V₀ V hV hm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
