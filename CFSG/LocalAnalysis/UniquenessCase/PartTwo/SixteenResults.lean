module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_8 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
    barSub V₀ V hV L ≠ ⊥ → Conc4_136 D V₀ V hV L →
    (∀ L' : Subgroup G, Setting16 D V₀ V L' → barSub V₀ V hV L' ≠ ⊥ →
      Conc4_136 D V₀ V hV L' → ¬ Concl167 D V₀ V hV L') →
    ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧ barSub V₀ V hV L' ≠ ⊥ ∧
      Conc4_136 D V₀ V hV L' ∧ Concl168 D V₀ V hV L'

@[expose] def Concl169 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  (V₀ ≤ centralizer (E3.wClos V D.k D.T : Set G) ∧
      ∀ v ∈ V, (∀ w ∈ E3.wClos V D.k D.T, ⁅v, w⁆ ∈ V₀) →
        v ∈ centralizer (E3.wClos V D.k D.T : Set G)) ∧
    ∀ B ∈ E3.gammaSet V D.k D.T, V₀ ≤ centralizer (B : Set G) ∧
      ∀ v ∈ V, (∀ b ∈ B, ⁅v, b⁆ ∈ V₀) → v ∈ centralizer (B : Set G)

@[expose] def R16_9 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    Concl169 D V₀ V

@[expose] def R16_10_1 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    ∀ H₀ : Subgroup G, Hyp124Min D H₀ →
      (H₀ ⊓ centralizer (E3.cClos V D.k D.T : Set G)) ⊔
        (H₀ ⊓ normalizer (E3.wClos V 0 D.T : Set G)) = H₀

@[expose] def R16_11 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M

@[expose] def R16_12 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
    ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M ∧ V₀ = ⊥ ∧
      (Case168_9 D V₀ V hV L → v1Sub D.M V₀ V hV L = ⊥)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
