module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)


namespace Res417Three

@[expose] def K417RankOneL3 : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → p ^ e % 3 = 2 →
    CFSG.pRank 3 (projSL 3 (GaloisField p e)) ≤ 1 ∧
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ e → CFSG.pRank 3 (StatedSL 3 K) ≤ 1

@[expose] def K417RankOneU3 : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 3 → 1 ≤ e → p ^ e % 3 = 1 →
    CFSG.pRank 3 (projSU 3 p e) ≤ 1 ∧
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ e) ^ 2 →
        CFSG.pRank 3 (StatedSU 3 (p ^ e) K) ≤ 1

theorem pow_mod_three {p e : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    p ^ e % 3 = 1 ∨ p ^ e % 3 = 2 := by
  have h : ¬ 3 ∣ p ^ e := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  omega

end Res417Three

open Res417Three

section Certs


variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerOutConf417.false_of_theta_pRank (h : IsInnerOutConf417 L A E c m) {S : Type}
    [Group S] (φ : L ⧸ aschbacherSolvableCore 3 L ≃* S) (hS : CFSG.pRank 3 S ≤ 1) : False := by
  have : Finite S := Finite.of_equiv _ (h.centerEquiv.trans φ).toEquiv
  exact h.false_of_pRank_le_one (h.centerEquiv.trans φ) hS

theorem item417OutL3Eps_of (hL3 : K417RankOneL3) (hU3 : K417RankOneU3) : Item417OutL3Eps := by
  intro G _ _ L A E c m hconf ⟨p, e, _, hp3, he1, he2, hX⟩
  exfalso
  have hp : p.Prime := Fact.out
  have hSL : ¬ IsSLThreePiTheta L := hconf.2.2.2.2.2.2.2.1
  rcases pow_mod_three (e := e) hp hp3 with hq | hq
  ·
    rcases hX with ⟨K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact hSL ⟨p, e, inferInstance, he1, Or.inl ⟨K, inferInstance, inferInstance,
        Or.inl ⟨hK, hq, ⟨φ⟩⟩⟩⟩
    · exact hconf.false_of_theta_pRank φ ((hU3 p e (by omega) he1 hq).2 K hK)
    · exact hSL ⟨p, e, inferInstance, he1, Or.inr (Or.inl ⟨hq, ⟨φ⟩⟩)⟩
    · exact hconf.false_of_theta_pRank φ (hU3 p e (by omega) he1 hq).1
  ·
    rcases hX with ⟨K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact hconf.false_of_theta_pRank φ ((hL3 p e hp3 he1 hq).2 K hK)
    · exact hSL ⟨p, e, inferInstance, he1, Or.inl ⟨K, inferInstance, inferInstance,
        Or.inr ⟨hK, hq, ⟨φ⟩⟩⟩⟩
    · exact hconf.false_of_theta_pRank φ (hL3 p e hp3 he1 hq).1
    · exact hSL ⟨p, e, inferInstance, he1, Or.inr (Or.inr ⟨hq, ⟨φ⟩⟩)⟩

end Certs

end CFSG.RankThree.PartTwo.Sec4
