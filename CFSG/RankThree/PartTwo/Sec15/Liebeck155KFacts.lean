module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec15.Notation
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.RankThree.PartTwo.Sec15.SimsBaumannIndexTwo

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.Open (StatedClassicalModel)

@[expose] def EvenPerfectSection : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (e : ℕ), 1 ≤ e →
    (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; Sec4.IsoLThreePi X 2 e) →
    ∀ (Q : Type) [Group Q] [Finite Q] (H : Subgroup X) (N : Subgroup H) [N.Normal],
      Nonempty (Q ≃* ↥H ⧸ N) → Group.IsPerfect Q → Nontrivial Q → CFSG.pCore 2 Q = ⊥ →
      IsSimpleGroup Q ∧
      ((∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel Q .PSL 2 2 j) ∨
        StatedClassicalModel Q .PSL 2 3 2 ∨
        (∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧
          (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; IsLThreeEpsAt Q 2 f)))

@[expose] def SimpleOrderFacts : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    ((∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨ StatedClassicalModel K .PSL 2 3 2) →
    IsEmpty (K ≃* alternatingGroup (Fin 7)) ∧ IsEmpty (K ≃* alternatingGroup (Fin 10)) ∧
    (∀ (p f : ℕ) [Fact p.Prime], ¬ IsLThreeEpsAt K p f) ∧
    (∀ (p e : ℕ) [Fact p.Prime], ¬ Sec4.IsoLThreePi K p e) ∧
    IsEmpty (K ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
    IsEmpty (K ≃* CFSG.Blueprint.NativeSporadic.M12)

theorem nonempty_mulEquiv_alt5_of_statedClassicalModel {K : Type} [Group K]
    (hK : StatedClassicalModel K .PSL 2 2 2) : Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel hK
  obtain ⟨κ⟩ := Sec15.SimsBaumann.nonempty_projSL_four_equiv_alt5
  exact ⟨e.trans κ⟩

theorem three_dvd_card_quot_pCore_two {G : Type} [Group G] [Finite G] {A X : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hX : X ∈ scriptY4 A LB) :
    3 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
  by_contra h3
  have hcop : Nat.Coprime 3 (Nat.card (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have h1 : ∀ x ∈ X, ∀ k : ℕ, x ^ 3 ^ k = 1 → x = 1 := by
    intro x hx k hk
    set y : ↥X := ⟨x, hx⟩ with hy
    have hyk : y ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥X) y = 1 := by
      have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) ^ 3 ^ k = 1 := by
        rw [← map_pow, hyk, map_one]
      have h4 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one h2
      have h5 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) ∣
          Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := orderOf_dvd_natCard _
      have h6 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥X) y) ∣ 1 := by
        have := Nat.dvd_gcd h4 h5
        rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k hcop)] at this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h6)
    have hmem : y ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).mp hq
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥X)) ⟨y, hmem⟩
    have hm' : y ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h7 : orderOf y ∣ 1 := by
      have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyk) (orderOf_dvd_of_pow_eq_one hm')
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow k m (by norm_num))] at this
    have := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h7)
    simpa [hy] using congrArg Subtype.val this
  have hX1 : X = ⊥ := by
    rw [hX.2.1, oPrimeResidualOf_eq_closure, eq_bot_iff, Subgroup.closure_le]
    rintro x ⟨hxX, k, hxk⟩
    exact h1 x hxX k hxk
  exact ne_bot_of_mem_scriptY4 hX hX1

end CFSG.RankThree.PartTwo.Sec15.Liebeck155
