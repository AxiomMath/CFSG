module

public import CFSG.Quasithin.EmptyFaithful.Gap6R2Push
public import CFSG.Quasithin.Vol2.Ch3Sec1Lem319
public import CFSG.Quasithin.EmptyFaithful.S151Dual

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T Mc M K N : Subgroup G}

@[expose] noncomputable def m0 (T Mc M : Subgroup G) : Subgroup G :=
  M ⊓ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)

theorem T_le_normalizer_R (hTM : T ≤ M) :
    T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) :=
  fun _ ht => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht,
    Gap6.normalizer_le_normalizer_centralizer_gap6 _ ((hTM.trans (le_normalizer_V154 T Mc M)) ht)⟩

theorem T_le_m0 (hTM : T ≤ M) : T ≤ m0 T Mc M := le_inf hTM (T_le_normalizer_R hTM)

theorem NonBorelK.inH (h : quasithinQTFE14Cat G T Mc) (hK : NonBorelK T Mc M K N) : InH T K := by
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (quasithinOmegaOneCenter_le_center T).trans inf_le_left
  have hZK : quasithinOmegaOneCenter T ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 (hZT.trans hK.T_le_K)
      (fun x hx => Subgroup.centralizer_le_normalizer _ (hK.le_centralizer hx))
      (h.sylow.1.to_le hZT)
  exact ⟨hK.T_le_K, fun hb => h.omegaOneCenter_ne_bot (le_bot_iff.mp (hZK.trans hb.le))⟩

theorem NonBorelK.d11Hyp (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M)
    (h159 : Lemma1519Concl T Mc M) (hK : NonBorelK T Mc M K N) :
    D11Hyp (m0 T Mc M) K T (V154 T Mc M) N := by
  have hTM : T ≤ M := hMf.1.1.2
  refine ⟨isSylowTwoOf_of_isSylowTwo h.sylow (T_le_m0 hTM), hK.minParabolic.isSylow,
    h159.six_reduced, V154_ne_bot h, hK.minParabolic.uniqueMax, h159.six_pCore, ?_⟩
  exact noNormal_of_not_exists
    (not_exists_normal_of_isUniqueM_of_not_le h159.five hK.not_K_le_M)

theorem qInt_m0 (h159 : Lemma1519Concl T Mc M) (h158 : Lemma1518Concl T Mc M)
    (hV : IsElemAbelian 2 (V154 T Mc M)) : qInt (m0 T Mc M) (V154 T Mc M) hV = 2 := by
  unfold m0
  rw [qInt_congr hV h159.six_autOn, ← qOn_eq hV]
  exact qOn_eq_two_of_lemma1518 h158

end CFSG.Quasithin.Gap6R2
