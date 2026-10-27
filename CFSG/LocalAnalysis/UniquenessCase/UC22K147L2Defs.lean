module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147UDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F05

@[expose] def K147L2N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V), CFSG.IsKGroup G → CFSG.pCore 2 G = ⊥ → Function.Injective ρ →
    ρ.IsIrreducible → ∀ L : Subgroup G, IsComponentOf L ⊤ → ∀ n : ℕ, Case147L2 L n →
    numConj L = 1 → mGV ρ ≤ n + 1 →
      ((∀ g : G, g ∉ normalizer (L : Set G) →
          commOn ρ L ⊤ ≤ fixSub ρ (L.map (MulAut.conj g).toMonoidHom)) ∧
        (NatL2 ρ L (commOn ρ L ⊤) ⊥ n ∨
          (∃ k : ℕ, n = 2 * k ∧
            (SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 (commOn ρ L ⊤) ⊥ ∨
              SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 (commOn ρ L ⊤) ⊥)) ∨
          (n = 3 ∧ IsL2 ↥L 3 ∧ SecIrr ρ L (commOn ρ L ⊤) ⊥ 8))) ∨
      NatOmegaPlus4 ρ (lgConj L) ⊤ ⊥ n

@[expose] def K147L2P : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V), CFSG.IsKGroup G → CFSG.pCore 2 G = ⊥ → Function.Injective ρ →
    ρ.IsIrreducible → ∀ L : Subgroup G, IsComponentOf L ⊤ → ∀ n : ℕ, Case147L2 L n →
    numConj L = 2 → mGV ρ ≤ n + 1 →
      ((∀ g : G, g ∉ normalizer (L : Set G) →
          commOn ρ L ⊤ ≤ fixSub ρ (L.map (MulAut.conj g).toMonoidHom)) ∧
        (NatL2 ρ L (commOn ρ L ⊤) ⊥ n ∨
          (∃ k : ℕ, n = 2 * k ∧
            (SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 (commOn ρ L ⊤) ⊥ ∨
              SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 (commOn ρ L ⊤) ⊥)) ∨
          (n = 3 ∧ IsL2 ↥L 3 ∧ SecIrr ρ L (commOn ρ L ⊤) ⊥ 8))) ∨
      NatOmegaPlus4 ρ (lgConj L) ⊤ ⊥ n

theorem numConj_pos {G : Type} [Group G] [Finite G] (L : Subgroup G) : 0 < numConj L := by
  have hfin : {K : Subgroup G | ∃ g : G, K = L.map (MulAut.conj g).toMonoidHom}.Finite :=
    (Set.finite_range fun g : G => L.map (MulAut.conj g).toMonoidHom).subset (by
      rintro K ⟨g, rfl⟩
      exact ⟨g, rfl⟩)
  refine (Set.ncard_pos hfin).mpr ⟨L, 1, ?_⟩
  ext x
  simp

theorem K147L2.of_split (hN : K147L2N) (hP : K147L2P) : K147L2 := by
  intro G _ _ V _ _ _ ρ hK hO hρ hirr L hL n hcase hm
  have h0 := numConj_pos L
  have h2 : numConj L ≤ 2 := hcase.2.2
  rcases (show numConj L = 1 ∨ numConj L = 2 by omega) with h | h
  · exact hN G V ρ hK hO hρ hirr L hL n hcase h hm
  · exact hP G V ρ hK hO hρ hirr L hL n hcase h hm

end CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
