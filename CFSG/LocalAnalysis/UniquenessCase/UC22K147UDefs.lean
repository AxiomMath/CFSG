module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147SzJ1Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F05

@[expose] def Case147SpU {G : Type} [Group G] (L : Subgroup G) (n : ℕ) : Prop :=
  (1 < n ∧ Odd n ∧ IsSp4 ↥(lgConj L) n ∧ ∃ g : G, ActsNontrivOnDiagramIn (lgConj L) g) ∨
    IsSU3 ↥(lgConj L) n

@[expose] def Case147L2 {G : Type} [Group G] (L : Subgroup G) (n : ℕ) : Prop :=
  2 < n ∧ IsL2 ↥L n ∧ numConj L ≤ 2

theorem case147_iff {G : Type} [Group G] {L : Subgroup G} {n : ℕ} :
    Case147 L n ↔ Case147SpU L n ∨ Case147SzJ1 L n ∨ Case147L2 L n := by
  constructor
  · rintro (h | h | ⟨⟨h2, hL | hSz⟩ | hJ, hc⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr ⟨h2, hL, hc⟩)
    · exact Or.inr (Or.inl ⟨Or.inl ⟨h2, hSz⟩, hc⟩)
    · exact Or.inr (Or.inl ⟨Or.inr hJ, hc⟩)
  · rintro ((h | h) | ⟨⟨h2, hSz⟩ | hJ, hc⟩ | ⟨h2, hL, hc⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨Or.inl ⟨h2, Or.inr hSz⟩, hc⟩)
    · exact Or.inr (Or.inr ⟨Or.inr hJ, hc⟩)
    · exact Or.inr (Or.inr ⟨Or.inl ⟨h2, Or.inl hL⟩, hc⟩)

@[expose] def K147SpU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V), CFSG.IsKGroup G → CFSG.pCore 2 G = ⊥ → Function.Injective ρ →
    ρ.IsIrreducible → ∀ L : Subgroup G, IsComponentOf L ⊤ → ∀ n : ℕ, 2 ≤ n → Case147SpU L n →
    mGV ρ ≤ n + 1 → IsL2 ↥L n

@[expose] def K147L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V), CFSG.IsKGroup G → CFSG.pCore 2 G = ⊥ → Function.Injective ρ →
    ρ.IsIrreducible → ∀ L : Subgroup G, IsComponentOf L ⊤ → ∀ n : ℕ, Case147L2 L n →
    mGV ρ ≤ n + 1 →
      ((∀ g : G, g ∉ normalizer (L : Set G) →
          commOn ρ L ⊤ ≤ fixSub ρ (L.map (MulAut.conj g).toMonoidHom)) ∧
        (NatL2 ρ L (commOn ρ L ⊤) ⊥ n ∨
          (∃ k : ℕ, n = 2 * k ∧
            (SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 (commOn ρ L ⊤) ⊥ ∨
              SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 (commOn ρ L ⊤) ⊥)) ∨
          (n = 3 ∧ IsL2 ↥L 3 ∧ SecIrr ρ L (commOn ρ L ⊤) ⊥ 8))) ∨
      NatOmegaPlus4 ρ (lgConj L) ⊤ ⊥ n

@[expose] def K147U : Prop := K147SpU ∧ K147SzJ1 ∧ K147L2

end CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
