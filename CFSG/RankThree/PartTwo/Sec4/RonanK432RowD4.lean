module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowD4Outer
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowD4Two
public import CFSG.RankThree.PartTwo.Sec4.RonanK432D4Y
public import CFSG.RankThree.PartTwo.Sec4.RonanK432D4XPlane
public import CFSG.RankThree.PartTwo.Sec4.RonanK432D4XExists

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Open CFSG.RankThree.PartTwo.Sec19

set_option linter.unusedSectionVars false

section D4


theorem listRow_C0 {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}
    (P : D4Par n X σ) (hn : 2 ≤ n)
    (hcard : Nat.card (C0 σ) = ordTrialityD4 (2 ^ n)) : ListRow (C0 σ) := by
  haveI : Finite (C0 σ) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    unfold ordTrialityD4
    have h1 : 0 < 2 ^ n := by positivity
    have h2 : 0 < (2 ^ n) ^ 12 * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1) := by positivity
    have h3 : 1 < (2 ^ n) ^ 6 := Nat.one_lt_pow (by omega) (Nat.one_lt_two_pow (by omega))
    have h4 : 1 < (2 ^ n) ^ 2 := Nat.one_lt_pow (by omega) (Nat.one_lt_two_pow (by omega))
    have : 0 < (2 ^ n) ^ 6 - 1 := by omega
    have : 0 < (2 ^ n) ^ 2 - 1 := by omega
    positivity)
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  have hz3 : z ^ 3 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    omega
  rcases three_conj_dichotomy σ n P.one_le P.card P.frob hz3 hz1 with hX | ⟨g, hg⟩
  · exact not_weaklyClosed_of_classX_of_plane P hX (exists_two_commuting_classX P hn)
  · exact not_weaklyClosed_of_conj_mem_Bsub P hn hcard hz3 hz1 hg

theorem rowOf_trialityD4 (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p = 2) :
    RowOf (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group := by
  intro S _ _ hs hna ⟨e⟩
  have hm : ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hq hq2 (by decide) e⟩
  rw [hq2] at hm
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      have ha : a ∈ Subgroup.center S := by
        rw [h]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  refine ⟨?_, outerRow_of_chevalleyExceptionalModel_trialityD4 hm hZ⟩
  by_cases hq1 : q.exponent = 1
  · exact listRowOf_trialityD4_two q hq hq2 hq1 S hs hna ⟨e⟩
  · obtain ⟨K, _, _, _, σ, hK, hσ, -, hf1, -, ⟨φ⟩⟩ :=
      Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
    have P : D4Par q.exponent K σ := ⟨hf1, hK, hσ⟩
    have hn : 2 ≤ q.exponent := by omega
    have hcard : Nat.card (C0 σ) = ordTrialityD4 (2 ^ q.exponent) := by
      rw [show Nat.card (C0 σ) = Nat.card S from (Nat.card_congr φ.toEquiv).symm,
        Timmesfeld.card_chevalleyExceptionalModel_two hm]
    haveI : Finite (C0 σ) := Finite.of_equiv S φ.toEquiv
    exact ListRow.of_mulEquiv φ.symm (listRow_C0 P hn hcard)

end D4

end CFSG.RankThree.PartTwo.Sec4.RonanK432
