module

public import CFSG.LieType.BorelTits.SpecialLinear
public import CFSG.Open.StatedAPI

public section

namespace CFSG.Quasithin.H13.KG12617L52.NormR

open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Module

@[expose] def flag3 {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A B : Submodule K V) : ℕ → Submodule K V
  | 0 => ⊥
  | 1 => A
  | 2 => B
  | _ + 3 => ⊤

theorem flag3_monotone {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {A B : Submodule K V} (hAB : A ≤ B) : Monotone (flag3 A B) := by
  refine monotone_nat_of_le_succ fun n => ?_
  match n with
  | 0 => exact bot_le
  | 1 => exact hAB
  | 2 => exact le_top
  | n + 3 => exact le_rfl

theorem exists_sylow_forall_stab (n : ℕ) (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] {A B : Submodule K (Fin n → K)} (hAB : A ≤ B) :
    ∃ S : Sylow p (StatedSL n K), ∀ g ∈ (S : Subgroup (StatedSL n K)),
      (∀ v ∈ A, natRep (StatedSL n K) g v ∈ A ∧ natRep (StatedSL n K) g⁻¹ v ∈ A) ∧
      (∀ v ∈ B, natRep (StatedSL n K) g v ∈ B ∧ natRep (StatedSL n K) g⁻¹ v ∈ B) := by
  obtain ⟨C, hC, hFC⟩ := exists_isCompleteFlag_forall_exists_eq (flag3_monotone hAB) ⟨3, rfl⟩
  obtain ⟨S, hS⟩ := hC.exists_sylow_normalizer_le_flagStab (natRep (StatedSL n K)) p
    (natRep_injective _) fun W hW =>
      (containsTransvections_natRep_statedSL n K).exists_eq_of_flagKernel_invariant hC hW
  refine ⟨S, fun g hg => ?_⟩
  have h := flagStab_le_flagStab (natRep (StatedSL n K)) hFC (hS (Subgroup.le_normalizer hg))
  exact ⟨h 1, h 2⟩

theorem card_sylow_two_statedSL_five {F : Type} [Field F] (hF : Nat.card F = 2)
    (S : Sylow 2 (StatedSL 5 F)) : Nat.card (S : Subgroup (StatedSL 5 F)) = 2 ^ 10 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity, CFSG.Open.StatedAPI.card_statedSL_five_of_card_eq_two hF]
  have h : (9999360 : ℕ) = 2 ^ 10 * 9765 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

end CFSG.Quasithin.H13.KG12617L52.NormR
