module

public import CFSG.GroupTheory.PerfectCentralProd
public import CFSG.LocalAnalysis.EvenBN.Common.SL2CentralTwoSplit

public section

namespace CFSG.OddTranspositions.PartFour

open Matrix

theorem ker_eq_bot_of_perfect_central_sl2_prod {k : Type} [Field k] [Fintype k]
    (hk : 5 ≤ Nat.card k) (hk9 : Nat.card k ≠ 9) {E : Type} [Group E]
    (p : E →* Matrix.SpecialLinearGroup (Fin 2) k × Matrix.SpecialLinearGroup (Fin 2) k)
    (hp : Function.Surjective p) (hcen : p.ker ≤ Subgroup.center E)
    (hE : commutator E = ⊤) : p.ker = ⊥ := by
  refine CFSG.GroupTheory.ker_eq_bot_of_perfect_central_prod_of_forall hE p hp hcen ?_ ?_
  · intro E' hE' f hf hfc
    exact @CFSG.LocalAnalysis.EvenBN.Common.ker_eq_bot_of_perfect_central_sl2 k _ _ hk hk9
      ↥E' _ ⟨hE'⟩ f hf hfc
  · intro E' hE' f hf hfc
    exact @CFSG.LocalAnalysis.EvenBN.Common.ker_eq_bot_of_perfect_central_sl2 k _ _ hk hk9
      ↥E' _ ⟨hE'⟩ f hf hfc

theorem sl2_prod_cover_of_two_pow {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 3 ≤ f)
    (hF : Nat.card F = 2 ^ f) :
    ∀ (E : Type) [Group E] [Finite E]
      (p : E →* Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F),
      Function.Surjective p → p.ker ≤ Subgroup.center E → commutator E = ⊤ → p.ker = ⊥ := by
  have hk : 5 ≤ Nat.card F := by
    rw [hF]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hk9 : Nat.card F ≠ 9 := by
    rw [hF]
    intro h
    have hf4 : f ≤ 3 := by
      by_contra hlt
      have hlt' : 4 ≤ f := by omega
      have h16 : 16 ≤ 2 ^ f := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hlt'
      omega
    interval_cases f
    norm_num at h
  intro E _ _ p hp hcen hE
  exact @ker_eq_bot_of_perfect_central_sl2_prod F _ (Fintype.ofFinite F) hk hk9 E _ p hp
    hcen hE

end CFSG.OddTranspositions.PartFour
