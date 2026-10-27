module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2One
public import CFSG.Quasithin.EmptyFaithful.S151b110
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2Out1

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T Mc M K N : Subgroup G}

theorem NonBorelK.outcome1_false_nonsolvable (hEW : Res2.E215MemberW) (h110 : StageLemma15110)
    (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M) (hCE : IsCE1513 T M)
    (h15 : Lemma1515Concl T Mc M) (h157 : Lemma1517Concl T Mc M) (h158 : Lemma1518Concl T Mc M)
    (hK : NonBorelK T Mc M K N) (hVK : ¬ V154 T Mc M ≤ pCoreOf 2 K)
    (hns : ¬ Group.IsSolvable K) (hL3 : V154 T Mc M ≤ pCoreOf 2 N)
    (hnot3 : ¬ Case1517Three M (V154 T Mc M) (mBar0 T Mc M)) : False := by
  have hTM : T ≤ M := hMf.1.1.2
  have hel : IsElemAbelian 2 (V154 T Mc M) := h15.reduced.2.2.1
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    hTM.trans (le_normalizer_V154 T Mc M)
  have hqa : qhatOn M (V154 T Mc M) = 2 := by
    rcases h158 with h1 | ⟨h3, -⟩
    · exact h1.1
    · exact absurd h3 hnot3
  have hyp := hK.hyp28 h hMf h15 hVK hL3
  have hchar : CharTwo K := charTwo_of_inH' h.qtke h.sylow (hK.inH h)
  have hq : ¬ qhatOf (autI hyp.elem M) < ((2 : ℚ) : WithTop ℚ) := by
    have : qhatOf (autI hel M) = ((2 : ℚ) : WithTop ℚ) := by
      rw [← qhatOn_eq_qhatOf151b hel, hqa]
      norm_cast
    exact fun hlt => (lt_irrefl _) (this ▸ hlt)
  have hb4 := rank_bound_of_cases151b h hMf hel h15.reduced h157.1 hnot3
    (h110 G T Mc M h hMf hCE) (fun h6 => rank_bound_five151b hMf hel h6)
  exact Res2.outcome1_false_W hEW hyp hchar hns hTM hq (relIndex_le_of_card_autI_le hel hTV hb4)

end CFSG.Quasithin.Gap6R2
