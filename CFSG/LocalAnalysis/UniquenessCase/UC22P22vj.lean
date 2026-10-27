module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront05

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F05

open CFSG.Open CFSG.RankThree.FFModules Subgroup

@[expose] def K516K : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.IsKGroup G →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (p : ℕ) (P T B : Subgroup G) (e : ℕ),
    Hyp51 p P T B e → Hyp53 ρ p P T B → Hyp515 B →
      e + 1 < mGV ρ ∨
      (∃ q ∈ alphaSet G, q ∣ Nat.card B ∧ ∃ Q ∈ calQ (G := G) q, 3 < CFSG.Open.pRank q Q) ∨
      (P ⊓ centralizer (B : Set G) ≠ ⊥ ∧ 3 < CFSG.Open.pRank p P ∧ ¬ InvertedIn ⊤ B)

theorem K516K_of_K516 (h : K516) : K516K :=
  fun G _ _ _ V _ _ _ ρ p P T B e h51 h53 h515 => h G V ρ p P T B e h51 h53 h515

end CFSG.LocalAnalysis.UniquenessCase.UC22.F05
