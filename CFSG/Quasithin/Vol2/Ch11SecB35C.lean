module

public import CFSG.Quasithin.Background.E2TwoCCases
public import CFSG.Quasithin.Background.E2TwoCLie
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped MatrixGroups Pointwise

@[expose] def DerivedL2ListC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (H K : Subgroup G),
    Hyp11 G T L I n → IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ → 1 < E1.nParam H →
    K ∈ cComp H → H = K ⊔ T → CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) →
    E2.E22CasesC H T (H ⊓ Subgroup.normalizer (L : Set G)) K →
      ∃ k : ℕ, E1.nParam H ≤ k ∧ 2 ≤ k ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
          ∃ φ : ↥K ⧸ CFSG.pCore 2 ↥K →* Matrix.SpecialLinearGroup (Fin 2) F,
            Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem e22LieCases_of_e22CasesC {H T M K : Subgroup G} (hn : 1 < E1.nParam H)
    (h : E2.E22CasesC H T M K) : E2.E22LieCases H T M K := by
  dsimp only [E2.E22CasesC] at h
  dsimp only [E2.E22LieCases]
  rcases h with ⟨hJ, t, ht, hne, hM, ⟨n, hn2, hty, hB, -⟩ | ⟨_, _, _, _, _, _, h1⟩⟩ |
      ⟨hTK, hJ, ⟨n, hBen, hB, -⟩ | ⟨n, -, hK', hD, hB, hle, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h1⟩ | ⟨_, _, _, _, _, h1⟩⟩
  · exact Or.inl ⟨hJ, t, ht, hne, hM, n, hn2, hty, hB⟩
  · exact absurd hn (by rw [h1]; exact lt_irrefl 1)
  · exact Or.inr ⟨hTK, hJ, Or.inl ⟨n, hBen, hB⟩⟩
  · have hge : 2 ≤ n := E2.E22A.two_le_of_one_lt_of_le hn hle
    refine Or.inr ⟨hTK, hJ, Or.inr ⟨n, hge, ?_, hD, hB⟩⟩
    rcases hK' with hK' | hK'
    · exact Or.inl hK'
    · right
      rw [E2.IsSp4Prime] at hK'
      split_ifs at hK' with h1
      · omega
      · exact hK'
  · exact absurd hn (by rw [h1]; exact lt_irrefl 1)
  · exact absurd hn (by rw [h1]; exact lt_irrefl 1)

theorem isPSL_two_of_mulEquiv_SL2 {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    [CharP F 2] {k : ℕ} (hF : Nat.card F = 2 ^ k) (hk : 2 ≤ k) (e : X ≃* SL(2, F)) :
    IsPSL 2 2 k X := by
  have hk4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* SL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq KGNat.center_SL2_eq_bot).trans QuotientGroup.quotientBot
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_, fun h => ?_⟩, F, inferInstance,
    inferInstance, hF, ⟨e.trans (ePSL.symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F))⟩⟩
  · have := congrArg Prod.snd h
    simp only at this
    omega
  · have := congrArg Prod.snd h
    simp only at this
    omega

omit [Finite G] in
theorem e22Cases_of_e22CasesC_of_not_le {H T M K : Subgroup G} {k : ℕ} {F : Type} [Field F]
    [Finite F] [CharP F 2] (hc : E2.E22CasesC H T M K)
    (hTK : ¬ T ≤ Subgroup.normalizer (K : Set G)) (hk2 : 2 ≤ k) (hnk : E1.nParam H = k)
    (hF : Nat.card F = 2 ^ k) (e : ↥(E2.star M H K) ≃* SL(2, F)) : E2.E22Cases H T M K := by
  dsimp only [E2.E22CasesC] at hc
  dsimp only [E2.E22Cases]
  rcases hc with ⟨hJ, t, ht, hne, hM, h1⟩ | ⟨hTK', -⟩
  · refine Or.inl ⟨hJ, t, ht, hne, hM, Or.inl ⟨k, hk2, Or.inl
      (isPSL_two_of_mulEquiv_SL2 hF hk2 e), ?_, hnk⟩⟩
    rcases h1 with ⟨_, -, -, hB, -⟩ | ⟨_, _, _, _, _, _, h1⟩
    · exact hB
    · exfalso
      rw [hnk] at h1
      have : k = 1 := by exact_mod_cast h1
      omega
  · exact absurd hTK' hTK

end CFSG.Quasithin.Vol2.Ch11.SecB
