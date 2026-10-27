module

public import CFSG.Quasithin.Background.S1567W1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace Insp10

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem exists_tau_NR (c : Ctx153 G T Mc M V₁ V₂ t) (r49 : Res15349 T Mc M V₁)
    (L : LineData153 T M V₁ V₂ E) :
    ∃ τ ∈ pCoreOf 2 Mc, τ ∈ TE153 T E ∧ τ * τ ∈ Subgroup.centralizer (VZ T M : Set G) ∧
      ∃ e ∈ E, τ * e * τ⁻¹ ≠ e := by
  have h := c.hyp
  have hsylMc : IsSylowTwoOf T Mc :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.qtfe.sylow h.qtfe.t_le_mc
  have hQT : pCoreOf 2 Mc ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsylMc
  have hQn : T ≤ Subgroup.normalizer (pCoreOf 2 Mc : Set G) :=
    h.qtfe.t_le_mc.trans (le_normalizer_pCoreOf 2 Mc)
  have hQ : ¬ pCoreOf 2 Mc ≤ Subgroup.centralizer (VZ T M : Set G) := by
    intro hle
    have hcomm := r49.comm_ZS
    have hbot : ⁅ZS153 T M V₁, pCoreOf 2 Mc⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro z hz q hq
      have hc := Subgroup.mem_centralizer_iff.mp (hle hq) z hz.1
      have : ⁅z, q⁆ = 1 := by
        rw [commutatorElement_def, hc]; group
      rw [this]
      exact Subgroup.one_mem _
    rw [hbot] at hcomm
    have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := h.lemma_15_3_2_two.2
    have hZbot : quasithinOmegaOneCenter T = ⊥ := hcomm.symm
    rw [hZbot, Subgroup.card_bot] at hZ2
    omega
  obtain ⟨q, hq, hqTE, hqq, hqe⟩ := S1567.exists_central_move c L hQT hQn hQ
  exact ⟨q, hq, hqTE, hqq, hqe⟩

theorem mem_centralizer_E_of_alpha_eq_one_NR (h113 : StageLemma14113)
    (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E)
    {h1 : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G)} {q : G}
    (hq : q ∈ G0_153 T Mc M E s) (hqT : q ∈ TE153 T E)
    (h : S1567.alpha153 T Mc M E s h1 ⟨q, hq⟩ = 1) : q ∈ Subgroup.centralizer (E : Set G) := by
  have := isKleinFour_E c L
  obtain ⟨y, hyY, hyN, hε1, hε3⟩ := S1567.exists_y_eps h113 c L
  have hqN : q ∈ Subgroup.normalizer (E : Set G) := hqT.2
  have hcomm : q * y * q⁻¹ * y⁻¹ ∈ pCoreOf 2 (YE153 Mc M E) :=
    (S1567.alpha153_eq_one_iff hq).mp h y hyY
  rw [S1567.pCoreOf_YE c r66] at hcomm
  have hmemN : q * y * q⁻¹ * y⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _ hcomm.2
  have h0 : conjAct E ⟨q * y * q⁻¹ * y⁻¹, hmemN⟩ = 1 := (conjAct_eq_one_iff''' E _).2 hcomm.2
  have e : (⟨q * y * q⁻¹ * y⁻¹, hmemN⟩ : ↥(Subgroup.normalizer (E : Set G))) =
      ⟨q, hqN⟩ * ⟨y, hyN⟩ * ⟨q, hqN⟩⁻¹ * ⟨y, hyN⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h0
  have hc : conjAct E ⟨y, hyN⟩ * conjAct E ⟨q, hqN⟩ = conjAct E ⟨q, hqN⟩ * conjAct E ⟨y, hyN⟩ := by
    have h2 : conjAct E ⟨q, hqN⟩ * conjAct E ⟨y, hyN⟩ * (conjAct E ⟨q, hqN⟩)⁻¹ =
        conjAct E ⟨y, hyN⟩ := mul_inv_eq_one.mp h0
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  obtain ⟨n, hn⟩ := r67.sylow_GE.2.1 ⟨q, hqT⟩
  have hqn : q ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hσn : conjAct E ⟨q, hqN⟩ ^ 2 ^ n = 1 := by
    have hqnN : q ^ 2 ^ n ∈ Subgroup.normalizer (E : Set G) :=
      (Subgroup.normalizer _).pow_mem hqN _
    have e1 : conjAct E ⟨q, hqN⟩ ^ 2 ^ n = conjAct E ⟨q ^ 2 ^ n, hqnN⟩ := by
      rw [← map_pow]
      rfl
    rw [e1, conjAct_eq_one_iff''']
    show q ^ 2 ^ n ∈ Subgroup.centralizer (E : Set G)
    rw [hqn]
    exact Subgroup.one_mem _
  have hσ1 := S1567.mulAut_eq_one_of_commute_two_pow (conjAct E ⟨y, hyN⟩) (conjAct E ⟨q, hqN⟩)
    hε1 hε3 hc n hσn
  exact (conjAct_eq_one_iff''' E ⟨q, hqN⟩).1 hσ1

theorem exists_alpha153_ne_one_NR (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (r49 : Res15349 T Mc M V₁) (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E)
    (h1 : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G)) :
    ∃ (τ : G) (hτ : τ ∈ G0_153 T Mc M E s), S1567.alpha153 T Mc M E s h1 ⟨τ, hτ⟩ ≠ 1 := by
  obtain ⟨τ, -, hτT, -, e, he, hmove⟩ := exists_tau_NR c r49 L
  have hτG : τ ∈ G0_153 T Mc M E s :=
    ((le_sup_right : TE153 T E ≤ G1_153 T Mc M E s).trans le_sup_left) hτT
  refine ⟨τ, hτG, fun h => ?_⟩
  have hC := mem_centralizer_E_of_alpha_eq_one_NR h113 c L r66 r67 hτG hτT h
  apply hmove
  have := Subgroup.mem_centralizer_iff.mp hC e he
  calc τ * e * τ⁻¹ = (e * τ) * τ⁻¹ := by rw [this]
    _ = e := by group

theorem oTwoUpper_ne_top_NR (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (r49 : Res15349 T Mc M V₁) (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E)
    (h1 : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G))
    (h2 : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G))
    (h5 : CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) =
      (pCoreOf 2 (G0_153 T Mc M E s)).subgroupOf (G0_153 T Mc M E s)) :
    oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≠
      ⊤ := by
  intro htop
  have hK : CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≤ (S1567.alpha153 T Mc M E s h1).ker := by
    intro x hx
    rw [h5, Subgroup.mem_subgroupOf] at hx
    exact S1567.alpha153_eq_one_of_mem_centralizer_E c r66 (h1 := h1) x.2 (h2 hx)
  let α' := QuotientGroup.lift (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
    (S1567.alpha153 T Mc M E s h1) hK
  have hcard := S1567.card_mulAut_quot_YE h113 c L r66
  have hker : (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≤
      α'.ker := by
    rw [← htop]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact S1567.eq_one_of_odd_of_card_two hcard α' hx.2
  obtain ⟨τ, hτ, hne⟩ := exists_alpha153_ne_one_NR h113 c r49 L r66 r67 h1
  apply hne
  have := hker (Subgroup.mem_top (QuotientGroup.mk (⟨τ, hτ⟩ : ↥(G0_153 T Mc M E s))))
  rw [MonoidHom.mem_ker] at this
  exact this

end Insp10

end CFSG.Quasithin
