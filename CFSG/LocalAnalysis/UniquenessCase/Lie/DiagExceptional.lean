module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.DiagCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Glue

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

theorem uc22pdiag_invPairs_of_hasInvMax {M : Type} [Group M] [Finite M]
    (h : ∀ U : Subgroup M, IsSylowTwoOf U ⊤ → HasInvariantMaximalOvergroups M U)
    (V : Sylow 2 M) : uc22pdiag_InvPair M V := by
  obtain ⟨Q₁, Q₂, -, -, hsup, hn₁, hn₂, hinv⟩ :=
    h (V : Subgroup M) (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow V)
  exact ⟨Q₁, Q₂, fun h => hn₁ (h ▸ Subgroup.normal_top), fun h => hn₂ (h ▸ Subgroup.normal_top),
    hsup, hinv⟩

theorem uc22pdiag_invPairs_of_hasUnequalCovers {M : Type} [Group M] [Finite M] {n₁ n₂ : ℕ} (hn : n₁ ≠ n₂)
    (h : ∀ U : Subgroup M, IsSylowTwoOf U ⊤ → HasUnequalCovers M U n₁ n₂)
    (V : Sylow 2 M) : uc22pdiag_InvPair M V := by
  obtain ⟨P₁, P₂, hcov, h1, h2, hsup, hi₁, hi₂⟩ :=
    h (V : Subgroup M) (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow V)
  have hinv := CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.invariant_of_unequal_covers hcov
    (by rw [hi₁, hi₂]; exact hn)
  exact ⟨P₁, P₂, h1, h2, hsup, hinv⟩

end Glue

section Exceptional

open CFSG.Blueprint (LieModel ChevalleyExceptionalModel ReeTitsModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6

variable {M : Type} [Group M] [Finite M] [IsSimpleGroup M]

theorem uc22pdiag_all_g2 {n : ℕ} (h : LieModel M .G2 0 2 n) : uc22pdiag_All M := by
  have hX : ChevalleyExceptionalModel M .G2 2 n := h.chevalleyExceptionalModel (by decide)
  exact uc22pdiag_all_of_invPairs
    (uc22pdiag_invPairs_of_hasInvMax (even_G2_model_two_extensions hX).2.2.2)

theorem uc22pdiag_all_triD4 {n : ℕ} (h : LieModel M .trialityD4 0 2 n) : uc22pdiag_All M := by
  have hX : ChevalleyExceptionalModel M .trialityD4 2 n := h.chevalleyExceptionalModel (by decide)
  have hn : 1 ≤ n := hX.1.2.1
  exact uc22pdiag_all_of_invPairs (uc22pdiag_invPairs_of_hasUnequalCovers
    (n₁ := 2 ^ (3 * n) + 1) (n₂ := 2 ^ n + 1)
    (by
      intro hEq
      have h1 : 2 ^ (3 * n) = 2 ^ n := Nat.add_right_cancel hEq
      have := Nat.pow_right_injective (le_refl 2) h1
      omega)
    (even_triality_model_two_extensions hX).2.2.2)

theorem uc22pdiag_all_twF4 {n : ℕ} (h : LieModel M .twistedF4 0 2 n) : uc22pdiag_All M := by
  obtain ⟨-, hX⟩ := h.reeTitsModel (by decide)
  have hadm := hX.1
  have hn : 3 ≤ n := hadm.2.2.2.2.2
  exact uc22pdiag_all_of_invPairs (uc22pdiag_invPairs_of_hasUnequalCovers
    (n₁ := 2 ^ n + 1) (n₂ := 2 ^ (2 * n) + 1)
    (by
      intro hEq
      have h1 : 2 ^ n = 2 ^ (2 * n) := Nat.add_right_cancel hEq
      have := Nat.pow_right_injective (le_refl 2) h1
      omega)
    (large_Ree_model_two_extensions hX).2.2.2)

end Exceptional

end CFSG.LocalAnalysis.UniquenessCase.UC22
