module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeCoverPsl

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)

theorem exists_model_sl {X : Type} [Group X] (hXq : IsQuasisimple X) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hX : IsSLThreePiAt X (p ^ e)) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π p e K ∧ ModThree π (p ^ e) ∧ 2 < p ^ e ∧
      Nonempty (X ≃* slPi π 3 (p ^ e) K) := by
  have hp : p.Prime := Fact.out
  have hpe2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
  obtain ⟨K, _, hfin, ⟨hK, hq3, ⟨eX⟩⟩ | ⟨hK, hq3, ⟨eX⟩⟩⟩ := hX
  · refine ⟨true, K, inferInstance, ⟨hp, he, hK⟩, hq3, ?_, ⟨eX⟩⟩
    omega
  · have hPi : PiField false p e K := ⟨hp, he, by rw [hK]; rfl⟩
    refine ⟨false, K, inferInstance, hPi, hq3, ?_, ⟨eX⟩⟩
    by_contra h2
    have hpe : p ^ e = 2 := by omega
    have hp2 : p = 2 := by
      have := (Nat.prime_two.eq_one_or_self_of_dvd p ⟨p ^ (e - 1), by
        rw [← pow_succ', Nat.sub_add_cancel he, hpe]⟩)
      rcases this with h | h
      · exact absurd h hp.one_lt.ne'
      · exact h
    have he1 : e = 1 := by
      rw [hp2] at hpe
      exact Nat.pow_right_injective le_rfl (show 2 ^ e = 2 ^ 1 by rw [hpe, pow_one])
    subst hp2
    subst he1
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K := hPi.unitary
    have hcardX : Nat.card X = 216 := by
      rw [Nat.card_congr eX.toEquiv]
      exact CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
    haveI : Finite X := Finite.of_equiv _ eX.symm.toEquiv
    haveI := Fintype.ofFinite X
    have hsolv : Group.IsSolvable X :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hcardX]; norm_num)
    have : Group.IsPerfect X := hXq.1
    have hnt : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hXq
    exact Group.IsPerfect.not_isSolvable X hsolv

theorem exists_pslPi_model_abs {X : Type} [Group X] (hXq : IsQuasisimple X) {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (hX : IsoLThreePi X p e) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π p e K ∧ ModThree π (p ^ e) ∧ 2 < p ^ e ∧
      Nonempty (X ≃* projImage (slPi π 3 (p ^ e) K)) := by
  have hX' : IsoLThreePi (⊤ : Subgroup X) p e := by
    rcases hX with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨hq, ⟨Subgroup.topEquiv.trans ψ⟩⟩
    · exact Or.inr ⟨hq, ⟨Subgroup.topEquiv.trans ψ⟩⟩
  obtain ⟨π, K, _, hK, hq, hq2, ⟨e'⟩⟩ := exists_pslPi_model (G := X) (L := (⊤ : Subgroup X)) he hX'
    (IsQuasisimple.of_mulEquiv Subgroup.topEquiv hXq)
  exact ⟨π, K, inferInstance, hK, hq, hq2, ⟨Subgroup.topEquiv.symm.trans e'⟩⟩

theorem exists_coverLift {X : Type} [Group X] [Finite X] (hXq : IsQuasisimple X) {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (hX : IsSLThreePiAt X (p ^ e) ∨ IsoLThreePi X p e) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π p e K ∧ ModThree π (p ^ e) ∧ 2 < p ^ e ∧
      CoverLift X π p e K := by
  rcases hX with hX | hX
  · obtain ⟨π, K, _, hK, hq, hq2, ⟨eX⟩⟩ := exists_model_sl hXq he hX
    exact ⟨π, K, inferInstance, hK, hq, hq2, coverLift_of_mulEquiv_sl eX⟩
  · obtain ⟨π, K, _, hK, hq, hq2, ⟨eX⟩⟩ := exists_pslPi_model_abs hXq he hX
    exact ⟨π, K, inferInstance, hK, hq, hq2, coverLift_of_mulEquiv_psl hXq.1 hK hq hq2 eX⟩

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
