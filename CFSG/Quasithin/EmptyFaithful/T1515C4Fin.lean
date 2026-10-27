module

public import CFSG.Quasithin.EmptyFaithful.T1515C4Q
public import CFSG.Quasithin.EmptyFaithful.T1515C6Fin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_V154_c4 {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) :
    IsElemAbelian 2 (V154 T Mc M) :=
  isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ hq hM.1.1)

theorem exists_gen_T4 {T Mc M : Subgroup G}
    (h4 : Nonempty (↥(autOn T (V154 T Mc M)) ≃* Multiplicative (ZMod 4))) :
    ∃ τ : MulAut (V154 T Mc M), τ ∈ autOn T (V154 T Mc M) ∧ orderOf τ = 4 ∧
      autOn T (V154 T Mc M) = Subgroup.zpowers τ := by
  obtain ⟨e⟩ := h4
  set τ₀ : ↥(autOn T (V154 T Mc M)) := e.symm (Multiplicative.ofAdd (1 : ZMod 4)) with hτ₀
  have hord : orderOf (τ₀ : MulAut (V154 T Mc M)) = 4 := by
    rw [Subgroup.orderOf_coe, hτ₀, MulEquiv.orderOf_eq, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one]
  refine ⟨τ₀, τ₀.2, hord, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le.mpr τ₀.2
  · rw [Nat.card_zpowers, hord, Nat.card_congr e.toEquiv]
    have : Nat.card (Multiplicative (ZMod 4)) = 4 := by
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card 4
    omega

theorem not_ce15Three_of_four {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h4 : Ce15Four T Mc M) : ¬ Ce15ThreeCase T Mc M := by
  rintro ⟨-, hMeq, -⟩
  obtain ⟨-, ⟨hel, -, tt, htt2, hinv, hA₀⟩, he⟩ := h4
  obtain ⟨τ, hτT, hτ4, -⟩ := exists_gen_T4 he
  have hVe := isElemAbelian_V154_c4 hq hM
  let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hVe
  have hTM : T ≤ M := hM.1.1.2
  have hτM : τ ∈ autOn M (V154 T Mc M) := autOn_le_autOn _ hTM hτT
  rw [hMeq, hA₀] at hτM
  have htt : tt * tt = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [htt2])
  exact tau_not_mem_of hτ4 hel.2 htt hinv hτM

theorem V154_eq_VZ_of_four {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h4 : Ce15Four T Mc M) (h17 : Lemma1517Concl T Mc M) : V154 T Mc M = VZ T M := by
  by_cases hc : Case1512Six T Mc M
  · exfalso
    have hle : V154 T Mc M ≤ VZ T M := V154_le_VZ T Mc M
    have hlt : V154 T Mc M < VZ T M := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      rw [V154_eq_uJ hc] at heq
      have hcle : cJ154 T M ≤ uJ154 T M := by
        rw [heq]
        exact inf_le_left
      have hbot : cJ154 T M = ⊥ := by
        have h1 : uJ154 T M ⊓ cJ154 T M = cJ154 T M := inf_eq_right.mpr hcle
        rw [← h1]
        exact hc.2.1
      exact hc.2.2.2.2.1 hbot
    exact not_ce15Three_of_four hq hM h4 (h17.2 hlt)
  · exact V154_eq_VZ hc

theorem exists_four4Data {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h4 : Ce15Four T Mc M) (hV : V154 T Mc M = VZ T M) :
    ∃ hVe : IsElemAbelian 2 (V154 T Mc M), ∃ d : Four4Data (V154 T Mc M) M T hVe,
      mBar0 T Mc M = oTwoUpper (autOn M (V154 T Mc M)) ⊔ Subgroup.zpowers d.tt := by
  have hVe := isElemAbelian_V154_c4 hq hM
  refine ⟨hVe, ?_⟩
  let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hVe
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := by
    rw [hV]
    exact le_normalizer_VZ T M
  have hTM : T ≤ M := hM.1.1.2
  have hsyl : IsSylowTwoOf T M := isSylowTwoOf_of_le151 hq.sylow hTM
  have h4' := h4
  obtain ⟨hcardV, ⟨hel, hc9, tt, htt2, hinv, hA₀⟩, he⟩ := h4'
  obtain ⟨τ, hτT, hτ4, hT⟩ := exists_gen_T4 he
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
  have hττ : IsSylowTwoOf (Subgroup.zpowers τ) (autOn M (V154 T Mc M)) := by
    rw [← hT]
    exact isSylowTwoOf_autOn' hsyl hMN
  have hctx : FourCtx (autOn M (V154 T Mc M)) τ tt :=
    { sq := fun v => by
        apply Subtype.ext
        show (v : G) * v = 1
        rw [← pow_two]
        exact hVe.2 _ v.2
      card_V := hcardV
      tau_mem := autOn_le_autOn _ hTM hτT
      tau_ord := hτ4
      syl := hττ
      card_P := hc9
      exp_P := hel.2
      comm_P := fun x hx y hy => congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      t_mem := httA
      t_sq := htt
      t_ne := by
        intro h1
        rw [h1, orderOf_one] at htt2
        omega
      t_inv := hinv }
  obtain ⟨g, hg⟩ := hctx.exists_gen
  exact ⟨⟨hMN, hsyl, τ, tt, g, hctx, hg, hT⟩, hA₀⟩

theorem exists_setting_four {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h4 : Ce15Four T Mc M) (h15 : Lemma1515Concl T Mc M) (h17 : Lemma1517Concl T Mc M)
    (h19 : Lemma1519Concl T Mc M) (h113 : Lemma15113Four T Mc M) :
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, Setting1516X T Mc M Z₁ Z₂ V₁ V₂ := by
  have hV : V154 T Mc M = VZ T M := V154_eq_VZ_of_four hq hM h4 h17
  obtain ⟨hVe, d, hA₀⟩ := exists_four4Data hq hM h4 hV
  let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hVe
  refine ⟨d.Z₁, d.Z₂, d.V₁, d.V₂, ?_⟩
  have hJ : autOn (thompsonJi T 1) (V154 T Mc M) = Subgroup.zpowers (d.τ * d.τ) := by
    rcases h113 with ⟨h1, -⟩ | ⟨h3, -⟩
    · rw [h1, d.hT, hA₀]
      exact FourCtx.inf_A₀ d.ctx
    · exact absurd h3 (not_ce15Three_of_four hq hM h4)
  have hVT : V154 T Mc M ≤ T := by
    rw [hV]
    exact (isTwoReducedIn_VZ hq hM.1.1).2
  have hZV : quasithinOmegaOneCenter T ≤ V154 T Mc M := by
    rw [hV]
    exact le_conjClosure _ _
  have hJC : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf (thompsonJ_le_self151 T) (le_centralizer_of_commutator_eq_bot h19.one_commute)
  have hrank : 1 < CFSG.Open.pRank 2 T :=
    one_lt_pRank_of_card hVe hVT (by have := h4.card_eq; omega)
  have hJR : thompsonJ T = thompsonJ (T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_of_le (by omega)
      (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJC) inf_le_left
  exact d.setting_of h4 rfl hV h15.centralizer_le hq.t_le_mc (not_le_mc_of_isMf hq hM) hJ hVT hZV
    (d.p_sub h19.six_autOn hJR)

end CFSG.Quasithin
