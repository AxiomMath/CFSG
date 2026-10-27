module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam0

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Hering129C

theorem isCyclic_sylow_of_isL3_not_pi {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (he : 1 ≤ e)
    (hX : Sec4.IsSLThreeEpsAt X (p ^ e) ∨ Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨
      Nonempty (X ≃* projSU 3 p e))
    (hSL : ¬ Sec4.IsSLThreePiAny X) (Q : Sylow 3 X) : IsCyclic Q := by
  have h2 : ∀ n : ℕ, p ^ n % 3 ≠ 0 := fun n h0 => by
    have h3 : 3 ∣ p ^ n := Nat.dvd_of_mod_eq_zero h0
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  rcases hX with hX | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact Sec4.isCyclic_sylow_of_isSLThreeEpsAt hp3 hX (fun h => hSL (Or.inl ⟨_, h⟩)) Q
  · have hq : p ^ e % 3 = 2 := by
      have : p ^ e % 3 ≠ 1 := fun h1 => hSL (Or.inr ⟨p, e, inferInstance, he, Or.inl ⟨h1, ⟨φ⟩⟩⟩)
      have := h2 e
      omega
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega)
      (Or.inr ⟨hq, ⟨φ⟩⟩) Q
  · have hq : p ^ e % 3 = 1 := by
      have : p ^ e % 3 ≠ 2 := fun h1 => hSL (Or.inr ⟨p, e, inferInstance, he, Or.inr ⟨h1, ⟨φ⟩⟩⟩)
      have := h2 e
      omega
    exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega)
      (Or.inl ⟨hq, ⟨φ⟩⟩) Q

theorem census_false_of_cyclic_sylow {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q}
    {I X : Subgroup Q} {f : ↥I →* Lb} (hD : Census129 c a I X f)
    (hcyc : ∀ P : Sylow 3 Q, IsCyclic P) : False :=
  (ppair_self hD).false_of_abelian_sylow fun P a b ha hb => by
    letI := (hcyc P).commGroup
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : (P : Subgroup Q)) ⟨b, hb⟩)

@[expose] def KFCensus46TwoPi : Prop :=
  KFCensusOn (fun Q _ => Sec4.IsList46Two Q ∧ Sec4.IsSLThreePiAny Q)

theorem kFCensus46Two_of_pi (h : KFCensus46TwoPi) : KFCensus46Two := by
  intro Q Lb _ _ _ c a I X f hQ hD
  by_cases hπ : Sec4.IsSLThreePiAny Q
  · exact h Q Lb c a I X f ⟨hQ, hπ⟩ hD
  · exfalso
    obtain ⟨p, e, hp, hp3, he, -, hX⟩ := hQ
    exact census_false_of_cyclic_sylow hD
      (isCyclic_sylow_of_isL3_not_pi (by omega) he hX hπ)

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
