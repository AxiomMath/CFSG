module

public import CFSG.Quasithin.EmptyFaithful.T1515C7Q
public import CFSG.Quasithin.EmptyFaithful.T1515fSevenP
public import CFSG.Quasithin.EmptyFaithful.T1515C4Fin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem V154_eq_VZ_of_seven {T Mc M : Subgroup G} (h7 : Ce15Seven T Mc M) :
    V154 T Mc M = VZ T M := by
  by_cases hc : Case1512Six T Mc M
  · exfalso
    have h1 := h7.card_eq
    rw [V154_eq_uJ hc] at h1
    have h2 := hc.2.2.2.1
    omega
  · exact V154_eq_VZ hc

theorem exists_seven7Data {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h7 : Ce15Seven T Mc M) (hV : V154 T Mc M = VZ T M) :
    ∃ hVe : IsElemAbelian 2 (V154 T Mc M), ∃ d : Seven7Data (V154 T Mc M) M T hVe,
      mBar0 T Mc M = oTwoUpper (autOn M (V154 T Mc M)) ⊔ Subgroup.zpowers d.tt := by
  have hVe := isElemAbelian_V154_c4 hq hM
  refine ⟨hVe, ?_⟩
  let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hVe
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := by
    rw [hV]
    exact le_normalizer_VZ T M
  have hTM : T ≤ M := hM.1.1.2
  have hsyl : IsSylowTwoOf T M := isSylowTwoOf_of_le151 hq.sylow hTM
  have h7' := h7
  obtain ⟨hcardV, hP1, ⟨tt, htt2, hinv, hA₀⟩, hirr⟩ := h7'
  have hAM : mBar0 T Mc M ≤ autOn M (V154 T Mc M) := by
    unfold mBar0 JhatOn
    simp only [hVe, dite_true]
    exact Jhat_le _
  have htt : tt * tt = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [htt2])
  have httA : tt ∈ autOn M (V154 T Mc M) := by
    apply hAM
    rw [hA₀]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tt)
  have hctx : SevenCtx (autOn M (V154 T Mc M)) (autOn T (V154 T Mc M)) tt :=
    { sq := fun v => by
        apply Subtype.ext
        show (v : G) * v = 1
        rw [← pow_two]
        exact hVe.2 _ v.2
      card_V := hcardV
      P1 := hP1
      Tb_le := autOn_le_autOn _ hTM
      syl := isSylowTwoOf_autOn' hsyl hMN
      t_mem := httA
      t_sq := htt
      t_ne := by
        intro h1
        rw [h1, orderOf_one] at htt2
        omega
      t_inv := hinv
      irr := hirr }
  obtain ⟨τ, x, y, z, p, hg, hp, htp⟩ := SevenGen.exists_gen' hctx
  exact ⟨⟨hMN, hsyl, τ, x, y, z, tt, p, hctx, hg, hp, htp⟩, hA₀⟩

theorem exists_setting_seven {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (h7 : Ce15Seven T Mc M) (h15 : Lemma1515Concl T Mc M)
    (h19 : Lemma1519Concl T Mc M) (h113 : Lemma15113Four T Mc M) :
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, Setting1516X T Mc M Z₁ Z₂ V₁ V₂ := by
  have hV : V154 T Mc M = VZ T M := V154_eq_VZ_of_seven h7
  obtain ⟨hVe, d, hA₀⟩ := exists_seven7Data hq hM h7 hV
  let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hVe
  refine ⟨d.Z₁, d.Z₂, ⊥, d.V₂, ?_⟩
  have hJ : autOn (thompsonJi T 1) (V154 T Mc M) = Subgroup.zpowers d.τ := by
    rcases h113 with ⟨h1, -⟩ | ⟨h3, -⟩
    · rw [h1, hA₀]
      exact SevenGen.inf_A₀ d.ctx d.gen d.hp d.htp
    · exfalso
      have h4 := h3.1
      have h5 := h7.card_eq
      omega
  have hVT : V154 T Mc M ≤ T := by
    rw [hV]
    exact (isTwoReducedIn_VZ hq hM.1.1).2
  have hJC : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf (thompsonJ_le_self151 T) (le_centralizer_of_commutator_eq_bot h19.one_commute)
  have hrank : 1 < CFSG.Open.pRank 2 T :=
    one_lt_pRank_of_card hVe hVT (by have := h7.card_eq; omega)
  have hJR : thompsonJ T = thompsonJ (T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_of_le (by omega)
      (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJC) inf_le_left
  exact d.setting_of h7 rfl hV h15.centralizer_le hq.t_le_mc (not_le_mc_of_isMf hq hM) hJ
    (d.p_sub h19.six_autOn hJR) (d.seven1516P_of hA₀)

end CFSG.Quasithin
