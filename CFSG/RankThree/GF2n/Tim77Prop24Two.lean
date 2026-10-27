module

public import CFSG.RankThree.GF2n.Tim77Prop24TwoSz
public import CFSG.RankThree.GF2n.Tim77Prop24TwoL2

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Open Matrix
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Prop24Setup

variable {A Ab L Lb M : Subgroup G} (S : Prop24Setup A Ab L Lb M)
include S

theorem tim77_2_4_two (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hMart : MartineauSzInput) :
    ∃ s : Finset (Subgroup G), s.SupIndep id ∧ s.sup id = M ∧
      (∀ W ∈ s, W ≤ M ∧ A ⊔ Ab ≤ Subgroup.normalizer (W : Set G) ∧ W ≠ ⊥ ∧
        ∀ U : Subgroup G, U ≤ W → A ⊔ Ab ≤ Subgroup.normalizer (U : Set G) → U = ⊥ ∨ U = W) ∧
      ((∃ f : ℕ, 2 ≤ f ∧ L.relIndex A = 2 ^ f ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
            (ψ : ↥(A ⊔ Ab) →* SL(2, F)), Nat.card F = 2 ^ f ∧ Function.Surjective ψ ∧
            ψ.ker = M.subgroupOf (A ⊔ Ab) ∧ ∀ W ∈ s,
              ∃ θ : (Fin 2 → F) → G, (∀ v v', θ (v + v') = θ v * θ v') ∧ Function.Injective θ ∧
                Set.range θ = W ∧ ∀ (x : ↥(A ⊔ Ab)) (v : Fin 2 → F),
                  θ ((ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = x * θ v * x⁻¹) ∨
        (∃ a : ℕ, 1 ≤ a ∧ L.relIndex A = 2 ^ (2 * a + 1) ∧
          ∃ ψ : ↥(A ⊔ Ab) →* GL (Fin 4) (GaloisField 2 (2 * a + 1)),
            ψ.range = Sz a ∧ ψ.ker = M.subgroupOf (A ⊔ Ab) ∧ ∀ W ∈ s,
              ∃ θ : (Fin 4 → GaloisField 2 (2 * a + 1)) → G, (∀ v v', θ (v + v') = θ v * θ v') ∧
                Function.Injective θ ∧ Set.range θ = W ∧ ∀ (x : ↥(A ⊔ Ab))
                  (v : Fin 4 → GaloisField 2 (2 * a + 1)),
                  θ (((ψ x : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
                    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ v) = x * θ v * x⁻¹) ∨
        (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ L.relIndex A = 2 ∧
          ∃ _ : (M.subgroupOf (A ⊔ Ab)).Normal,
            Nonempty (↥(A ⊔ Ab) ⧸ M.subgroupOf (A ⊔ Ab) ≃* DihedralGroup m))) := by
  obtain ⟨hN, -, hmod⟩ := S.tim77_2_4_one hCen hU
  rcases hmod with ⟨f, hf, hrel, ⟨e⟩⟩ | ⟨a, ha, hrel, ⟨e⟩⟩ | ⟨m, hm, h3, hrel, ⟨e⟩⟩
  · obtain ⟨F, hF, hFin, hchar, ψ, hcard, hψs, hψk, s, hs, hsM, hsW⟩ := S.tim77_2_4_two_psl hf e
    exact ⟨s, hs, hsM, fun W hW => ⟨(hsW W hW).1, (hsW W hW).2.1, (hsW W hW).2.2.1,
      (hsW W hW).2.2.2.1⟩, Or.inl ⟨f, hf, hrel, F, hF, hFin, hchar, ψ, hcard, hψs, hψk,
        fun W hW => (hsW W hW).2.2.2.2⟩⟩
  · obtain ⟨ψ, hψr, hψk, s, hs, hsM, hsW⟩ := S.tim77_2_4_two_sz hMart ha e
    exact ⟨s, hs, hsM, fun W hW => ⟨(hsW W hW).1, (hsW W hW).2.1, (hsW W hW).2.2.1,
      (hsW W hW).2.2.2.1⟩, Or.inr (Or.inl ⟨a, ha, hrel, ψ, hψr, hψk,
        fun W hW => (hsW W hW).2.2.2.2⟩)⟩
  · obtain ⟨s, hs, hsM, hsW⟩ := S.tim77_2_4_two_dihedral hrel
    exact ⟨s, hs, hsM, hsW, Or.inr (Or.inr ⟨m, hm, h3, hrel, hN, ⟨e⟩⟩)⟩

end Prop24Setup

end CFSG.RankThree.GF2n.Tim77
