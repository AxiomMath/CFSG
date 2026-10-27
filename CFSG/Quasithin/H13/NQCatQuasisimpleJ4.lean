module

public import CFSG.Quasithin.H13.NQCatQuasisimple
public import CFSG.Sporadic.Schreier.J4SOuter

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem J4_outer_large_prime_sylow_order_bound
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T]
    (_hnonab : ∃ a b : T, a * b ≠ b * a) (hT : Nonempty (T ≃* NativeSporadic.J4)) :
    ∀ p : ℕ, p.Prime → 5 ≤ p →
      (p ∈ ({5, 7, 31} : Finset ℕ) → p ^ (Nat.card (Outer T)).factorization p ∣ p) ∧
      (p ∉ ({5, 7, 31} : Finset ℕ) → p ^ (Nat.card (Outer T)).factorization p = 1) ∧
      (∀ P : Sylow p (Outer T), IsCyclic P ∧ Nat.card P ≤ p) ∧ CFSG.pRank p (Outer T) ≤ 1 := by
  intro p hp hp5
  have : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  have hnd : ¬ p ∣ Nat.card (Outer T) := fun hd => by
    rcases (Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes hT).1 p hp hd
      with rfl | rfl <;> omega
  have hpart : p ^ (Nat.card (Outer T)).factorization p = 1 := by
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero]
  refine ⟨fun _ => by rw [hpart]; exact one_dvd p, fun _ => hpart, fun P => ?_,
    (pRank_eq_zero_of_not_dvd hp hnd).le.trans zero_le_one⟩
  have hP := sylow_eq_bot_of_not_dvd hp hnd P
  refine ⟨by rw [hP]; infer_instance, ?_⟩
  rw [hP, Subgroup.card_bot]
  omega

theorem sqtk_quasisimple_cyclic_large_prime_outer_sylows
    (J : Type) [Group J] [Finite J]
    (hJ : CFSG.IsQuasisimple J) (hsqtk : SectionRank.IsSQTKCat J) :
    ∀ p : ℕ, p.Prime → 5 ≤ p →
      (∀ P : Sylow p (Outer J), IsCyclic P) ∧ CFSG.pRank p (Outer J) ≤ 1 := by
  rcases sqtk_quasisimple_outer_prime_control_or_J4 J hJ hsqtk with he | h
  · intro p hp hp5
    obtain ⟨hperf, hsimple, hnonab⟩ := hJ
    have : Finite (MulAut J) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut J))
    have : Finite (MulAut (J ⧸ Subgroup.center J)) :=
      Finite.of_injective _ (DFunLike.coe_injective (F := MulAut (J ⧸ Subgroup.center J)))
    obtain ⟨-, -, hS, hrk⟩ :=
      J4_outer_large_prime_sylow_order_bound (J ⧸ Subgroup.center J) hnonab he p hp hp5
    exact sylow_isCyclic_pRank_le_one_of_injective _
      (LocalAnalysis.ComponentInitial.perfect_central_quotient_Schreier J).1 hp
      ⟨fun P => (hS P).1, hrk⟩
  · exact h

end CFSG.Quasithin.H13.NQCat
