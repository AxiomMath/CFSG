module

public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem perfectCore_eq_bot_of_abelian {G : Type*} [Group G]
    (hab : ¬ ∃ a b : G, a * b ≠ b * a) (H : Subgroup G) : perfectCore H = ⊥ := by
  push Not at hab
  refine le_bot_iff.mp ((perfectCore_le_derivedSeriesOf H 1).trans ?_)
  rw [derivedSeriesOf_succ, derivedSeriesOf_zero]
  refine le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x _ => ?_)
  exact Subgroup.mem_centralizer_iff.mpr fun y _ => hab y x

theorem stageLemma1413_of_a39 (h39 : A39ForSQTK) : StageLemma1413 := by
  intro G _ _ T hs hK hT hLf H hH U hU
  by_cases hnab : ∃ a b : G, a * b ≠ b * a
  · obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
    rw [← lemma_1_2_1_one hK hs hnab h39 hH.2]
    refine sSup_le fun L hL => ?_
    by_contra hnot
    refine hLf L (isFaithfulLocal_of_commutator_ne_bot hK.2.1 S hH hL hU fun hcomm => hnot ?_)
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  · rw [perfectCore_eq_bot_of_abelian hnab]
    exact bot_le

end CFSG.Quasithin
