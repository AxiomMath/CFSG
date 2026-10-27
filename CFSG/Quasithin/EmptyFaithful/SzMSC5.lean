module

public import CFSG.Quasithin.MS93.C134L32CorrMOne
public import CFSG.Quasithin.EmptyFaithful.FLc6MSOne
public import CFSG.Quasithin.EmptyFaithful.FLc6NC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC134ResMain
public import CFSG.Quasithin.EmptyFaithful.S151U7
public import CFSG.Quasithin.EmptyFaithful.S152He15B
public import CFSG.Quasithin.Background.FLc6Cases
public import CFSG.Quasithin.EmptyFaithful.A38cA7
public import CFSG.Quasithin.EmptyFaithful.FLcFlagLocal
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.LRedNoBorel
public import CFSG.Quasithin.EmptyFaithful.S151WA
public import CFSG.Quasithin.EmptyFaithful.S151WE
public import CFSG.Quasithin.EmptyFaithful.S151WF
public import CFSG.Quasithin.EmptyFaithful.S151WH
public import CFSG.Quasithin.EmptyFaithful.S151YJ
public import CFSG.Quasithin.EmptyFaithful.S151ZY
public import CFSG.Quasithin.EmptyFaithful.S152UGen

public section

namespace CFSG.Quasithin

section Lemma15129

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Input15129NotC134Corr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → FlagData15129 T Mc M Z₁ Z₂ V₂ L n W →
    IsMSPair (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
        (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) →
    ∀ i : ℕ, ¬ MS93.IsC134CaseCorr i (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
      (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) (kPar15129 T Z₁ L n W)

@[expose] def Input15129NotC134CorrM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → FlagData15129 T Mc M Z₁ Z₂ V₂ L n W →
    IsMSPair (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
        (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) →
    ∀ i : ℕ, ¬ IsC134CaseM i (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
      (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) (kPar15129 T Z₁ L n W)

@[expose] def Input15129NotC134ResCorrM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → FlagData15129 T Mc M Z₁ Z₂ V₂ L n W →
    IsMSPair (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
        (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) →
    ∀ i : ℕ, 2 ≤ i → i ≤ 4 → ¬ IsC134CaseM i (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
      (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) (kPar15129 T Z₁ L n W)

theorem input15129NotC134CorrM_of_res (h : Input15129NotC134ResCorrM) :
    Input15129NotC134CorrM := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hMS i
  obtain ⟨D⟩ := nonempty_p0Setup15129 hc hF
  have hn := hF.n_eq
  have hULL : uLOf1527 Z₂ L ≤ L := uLOf1527_le_L hc.base
  have hUL : uLOf1527 Z₂ L ≤ L ⊔ s1516 T Z₁ := hULL.trans le_sup_left
  match i with
  | 0 => exact fun h0 => h0
  | 1 => exact D.not_isC134Case1 hn hUL hULL
  | 2 => exact h G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hMS 2 (by norm_num) (by norm_num)
  | 3 => exact h G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hMS 3 (by norm_num) (by norm_num)
  | 4 => exact h G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hMS 4 (by norm_num) (by norm_num)
  | 5 => exact D.not_isC134Case5 hn hUL hULL
  | k + 6 => exact fun h0 => h0

theorem input15129NotC134ResCorrM_holds : Input15129NotC134ResCorrM := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF _ i hi2 hi4
  have hcore := not_c134NotCentralizerCore_15129 hc hF
  interval_cases i
  · exact fun h => hcore h.2
  · exact fun h => hcore h.2
  · exact fun h => hcore h.2

theorem input15129NotC134CorrM_holds : Input15129NotC134CorrM :=
  input15129NotC134CorrM_of_res input15129NotC134ResCorrM_holds

theorem lemma15129InputU_of_named_inputs_corrM
    (h159 : StageLemma1519) (h1416 : StageLemma1416) (h15 : StageLemma1515CE)
    (hC34 : C134L32CorrM)
    (nZD : Input15129ZDiagonal) (nZO : Input15129ZOrder)
    (nFL : Input15129FlagLocal) (n3 : Input15129P0)
    (n5 : Input15129Rank2) (n6 : Input15129EndNode) (n7 : Input15129MSHypOne)
    (n8 : Input15129NotC134CorrM) (n9 : Input15129MFrattini) : Lemma15129InputU := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26 h27 h28 _
  have hc : Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L :=
    ⟨⟨hC, h17, h18, h19, hL, h22, h24, h25, h26, h27⟩, h28⟩
  have hq := hC.qtfe
  have hM := hC.mf
  have hCE := hC.ce
  have hS := hC.setting
  have n1 : Input15129CaseFour := caseFour15129_of nZD nZO
  have n2 : Input15129Flag := flag15129_of nFL
  obtain ⟨n, W, hF⟩ := n2 G T Mc M Z₁ Z₂ V₁ V₂ L hc (n1 G T Mc M Z₁ Z₂ V₁ V₂ L hc)
  have h19' : Lemma1519Concl T Mc M := h159 G T Mc M hq hM hCE
  obtain ⟨hP1a, hP1b, hP1c⟩ := n3 G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF
  have hQCS := cs15129 G T Mc M Z₁ Z₂ V₁ V₂ L hc hF.four
  obtain ⟨hR1, hR2, hR3⟩ := n5 G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF
  have hEnd := n6 G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hL.comp
  have hSG : s1516 T Z₁ ≤ g1_1516 Z₁ := s1516_le_g1 T Z₁
  have hSyl : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁) := h18.four
  have hSP : ∀ i, s1516 T Z₁ ≤ pPar15129 T Z₁ L n W i := fun i => by
    unfold pPar15129 flagParab
    exact le_inf le_sup_right (le_iInf₂ fun j hj => (hF.flag.2 j hj.1 hj.2.1).2.2.1)
  have hPG : ∀ i, pPar15129 T Z₁ L n W i ≤ g1_1516 Z₁ := fun i =>
    (flagParab_le _ n W i).trans (sup_le hLG hSG)
  have hPSyl : ∀ i, IsSylowTwoOf (s1516 T Z₁) (pPar15129 T Z₁ L n W i) := fun i =>
    FLc.isSylowTwoOf_restrict hSyl (hSP i) (hPG i)
  have hLN : L ⊔ s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hF.normalizes
  have hO2L : oTwoUpper (L ⊔ s1516 T Z₁) ≤ L :=
    Der6A.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hLN) hSyl.2.1 le_sup_right le_rfl
  have hP1d : ¬ oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ mZ1516 Mc Z₁ := by
    intro hY
    apply hP1a
    have hYL : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ L :=
      (oTwoUpper_mono (flagParab_le _ n W 1)).trans hO2L
    have hYN : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ Subgroup.normalizer (W 1 : Set G) := by
      have h : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤
          L ⊓ Subgroup.normalizer (zUOf1528 Z₂ L : Set G) := h28.2.2.2 ▸ le_inf hY hYL
      rw [← hF.w1] at h
      exact fun x hx => (h hx).2
    have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (W 1 : Set G) :=
      (hF.flag.2 1 le_rfl (by rcases hF.n_eq with h | h <;> omega)).2.2.1
    exact (eq_oTwoUpper_sup_of_isSylowTwoOf (hPSyl 1)).le.trans (sup_le hYN hSN)
  have hT2 : IsPGroup 2 T := hq.sylow.1
  have hZT : quasithinOmegaOneCenter T ≤ T := (quasithinOmegaOneCenter_le_center T).trans inf_le_left
  have hT1 : T ≠ ⊥ := fun hbot => hq.omegaOneCenter_ne_bot (le_bot_iff.mp (hZT.trans hbot.le))
  have hJM : Subgroup.normalizer (thompsonJ T : Set G) ≤ M :=
    (S1414.normalizer_thompsonJ_le_CGS hT2 hT1).trans h19'.one_cgs
  have hJle : thompsonJ (s1516 T Z₁) ≤ pCoreOf 2 (pPar15129 T Z₁ L n W 1) := by
    rw [hP1b]
    refine le_inf (B6.thompsonJ_le _) ?_
    rw [h17.jS]
    have h1 : thompsonJ T ≤ Subgroup.centralizer (V154 T Mc M : Set G) :=
      Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h19'.one_commute)
    exact h1.trans (Subgroup.centralizer_le hS.v2_le)
  have hQS : pCoreOf 2 (pPar15129 T Z₁ L n W 1) ≤ s1516 T Z₁ := by
    rw [hP1b]; exact inf_le_left
  have hJQ : thompsonJ (pCoreOf 2 (pPar15129 T Z₁ L n W 1)) = thompsonJ (s1516 T Z₁) :=
    B6.thompsonJ_eq_of_le hJle hQS
  have hP1J : pPar15129 T Z₁ L n W 1 ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    intro x hx
    have h1 : x ∈ Subgroup.normalizer (pCoreOf 2 (pPar15129 T Z₁ L n W 1) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx
    have h2 := normalizer_le_normalizer_thompsonJ (pCoreOf 2 (pPar15129 T Z₁ L n W 1)) h1
    rw [hJQ, h17.jS] at h2
    exact h2
  have hP1M : pPar15129 T Z₁ L n W 1 ≤ M := fun x hx => hJM (hP1J hx)
  have hY₀Y : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) :=
    hP1c.trans (oPrimeResidualOf_mono1516 3 (le_inf hP1M (hPG 1)))
  have hY₀V : ⁅V₂, oTwoUpper (pPar15129 T Z₁ L n W 1)⁆ = V₂ :=
    (h24.three _ (oTwoUpper_idem _) hY₀Y hP1d).1
  have hTM : T ≤ M := hM.1.1.2
  have hQT : T ≤ Subgroup.normalizer (pCoreOf 2 (pPar15129 T Z₁ L n W 1) : Set G) := by
    rw [hP1b, hQCS]
    have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans (le_normalizer_V154 T Mc M)
    have hTC := hTV.trans (normalizer_le_normalizer_centralizer (V154 T Mc M))
    exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hTC hx⟩
  have hY2 : ∀ t ∈ T, conjByElt t (oTwoUpper (pPar15129 T Z₁ L n W 2)) =
      oTwoUpper (pPar15129 T Z₁ L n W 2) := by
    intro t ht
    rcases hEnd t ht with h | h
    · exact h
    · exfalso
      apply hR2
      intro x hx
      have hx' : t * x * t⁻¹ ∈ pCoreOf 2 (oTwoUpper (pPar15129 T Z₁ L n W (n - 1))) := by
        rw [← h, conjByElt, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj t)]
        exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
      exact (Subgroup.mem_normalizer_iff.mp (hQT ht) x).mpr (hR1 hx')
  have hTS : T ≤ Subgroup.normalizer (s1516 T Z₁ : Set G) :=
    (hS.extra_small (Or.inl hF.four)).s_normal
  have hTP2 : T ≤ Subgroup.normalizer (pPar15129 T Z₁ L n W 2 : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have e : pPar15129 T Z₁ L n W 2 = oTwoUpper (pPar15129 T Z₁ L n W 2) ⊔ s1516 T Z₁ :=
      eq_oTwoUpper_sup_of_isSylowTwoOf (hPSyl 2)
    have h1 := hY2 t ht
    have h2 : (s1516 T Z₁).map (MulAut.conj t).toMonoidHom = s1516 T Z₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTS ht)
    unfold conjByElt at h1
    conv_lhs => rw [e]
    rw [Subgroup.map_sup]
    exact (congrArg₂ (· ⊔ ·) h1 h2).trans e.symm
  have hTQ2 : T ≤ Subgroup.normalizer (pCoreOf 2 (pPar15129 T Z₁ L n W 2) : Set G) := fun t ht =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hTP2 ht)
  have hCex : ∃ C : Subgroup G, C ≤ pCoreOf 2 (pPar15129 T Z₁ L n W 2) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (pCoreOf 2 (pPar15129 T Z₁ L n W 2))).Characteristic ∧
      kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2) ≤ Subgroup.normalizer (C : Set G) := by
    by_contra hno
    have hno' : ∀ C : Subgroup G, C ≤ pCoreOf 2 (pPar15129 T Z₁ L n W 2) → C ≠ ⊥ →
        (C.subgroupOf (pCoreOf 2 (pPar15129 T Z₁ L n W 2))).Characteristic →
        ¬ kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2) ≤
          Subgroup.normalizer (C : Set G) := fun C h1 h2 h3 h4 => hno ⟨C, h1, h2, h3, h4⟩
    obtain ⟨hms, hcc, hset, hα⟩ := n7 G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hno'
    obtain ⟨i, hi⟩ := hC34 G _ _ _ hms hcc hset hα
    exact n8 G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hms i hi
  obtain ⟨C, hCQ, hCne, hCchar, hCK⟩ := hCex
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := by
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := pCoreOf 2 (pPar15129 T Z₁ L n W 2)) (C.subgroupOf (pCoreOf 2 (pPar15129 T Z₁ L n W 2)))
    rw [Subgroup.map_subgroupOf_eq_of_le hCQ] at this
    exact hTQ2.trans this
  have hKC : kPar15129 T Z₁ L n W ≤ Subgroup.normalizer (C : Set G) := le_sup_left.trans hCK
  have hCp : IsPGroup 2 C :=
    IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (pPar15129 T Z₁ L n W 2)) hCQ
  have hNCne : pCoreOf 2 (Subgroup.normalizer (C : Set G)) ≠ ⊥ := fun hb =>
    hCne (le_bot_iff.mp (hb ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      Subgroup.le_normalizer le_rfl hCp))
  have hXle : T ⊔ oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ Subgroup.normalizer (C : Set G) :=
    sup_le hTC ((le_sup_left : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ kPar15129 T Z₁ L n W).trans hKC)
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) := fun x hx =>
    normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer hx)
  have hXJ : T ⊔ oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
    sup_le hTJ ((oTwoUpper_le _).trans hP1J)
  have hXpc : pCoreOf 2 (T ⊔ oTwoUpper (pPar15129 T Z₁ L n W 1)) ≠ ⊥ := by
    intro hb
    apply S1414.thompsonJ_ne_bot hT2 hT1
    refine le_bot_iff.mp (hb ▸ ?_)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((C1GN.thompsonJ_le T).trans le_sup_left) hXJ (IsPGroup.to_le hT2 (C1GN.thompsonJ_le T))
  have hXM : T ⊔ oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ M :=
    sup_le hTM ((oTwoUpper_le _).trans hP1M)
  have hU : IsUniqueM (T ⊔ oTwoUpper (pPar15129 T Z₁ L n W 1)) M :=
    isUniqueM_of_isOrdMaximalIn hM.1 ⟨le_sup_left, hXpc⟩ hXM
      (n9 G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF)
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hNCne
  have hM'M : M' = M := hU.2 M' ⟨hM'.1, hXle.trans hM'.2⟩
  have hNCM : Subgroup.normalizer (C : Set G) ≤ M := hM'M ▸ hM'.2
  have hKM : kPar15129 T Z₁ L n W ≤ M := hKC.trans hNCM
  have hred : IsTwoReducedIn M (V154 T Mc M) := (h15 G T Mc M hq hM hCE).reduced
  have hinf : perfectCore M ≤ Subgroup.centralizer (V154 T Mc M : Set G) :=
    (h1416 G T Mc hq).1 M (V154 T Mc M) hM.1.1 hred
  have hKV : kPar15129 T Z₁ L n W ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
    have := (perfectCore_mono hKM).trans hinf
    rwa [hR3] at this
  have hY₀V1 : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ Subgroup.centralizer (V₂ : Set G) :=
    ((le_sup_left : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ kPar15129 T Z₁ L n W).trans hKV).trans
      (Subgroup.centralizer_le hS.v2_le)
  have hcomm : ⁅V₂, oTwoUpper (pPar15129 T Z₁ L n W 1)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp hY₀V1
  rw [hcomm] at hY₀V
  have h4 := (hS.ranks_four hF.four).2.1
  rw [← hY₀V, Subgroup.card_bot] at h4
  exact absurd h4 (by norm_num)

end Lemma15129

section Residue

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Input15129NotC134ResCorr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) (n : ℕ) (W : ℕ → Subgroup G),
    Ctx15129 T Mc M Z₁ Z₂ V₁ V₂ L → FlagData15129 T Mc M Z₁ Z₂ V₂ L n W →
    IsMSPair (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
        (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) →
    ∀ i : ℕ, 2 ≤ i → i ≤ 4 → ¬ MS93.IsC134CaseCorr i (kPar15129 T Z₁ L n W ⊔ pCoreOf 2 (pPar15129 T Z₁ L n W 2))
      (pCoreOf 2 (pPar15129 T Z₁ L n W 2)) (kPar15129 T Z₁ L n W)

theorem input15129NotC134Corr_of_res (h : Input15129NotC134ResCorr) :
    Input15129NotC134Corr :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hMS i hi =>
    (input15129NotC134CorrM_of_res input15129NotC134ResCorrM_holds)
      G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hMS i hi.toCaseM

theorem input15129NotC134ResCorr_holds : Input15129NotC134ResCorr :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hMS i hi2 hi4 hi =>
    input15129NotC134ResCorrM_holds G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hMS i hi2 hi4 hi.toCaseM

end Residue

structure Inputs151XR12Corr : Prop where
  lj : Input15120LJ
  b42List : Input15120B42List
  l2Block : Input15120L2Block
  rankTwoExcl : Input15120RankTwoExcl
  twoB : Input15120TwoB
  compList : Input15120CompList
  mlA : Input15120MLA
  mlB : Input15120MLB
  mlC : Input15120MLC
  mlD : Input15120MLD
  dichotomy : Input15122Dichotomy
  l3WreathStar : Input15122L3WreathStar
  threeCLoc : Input15122ThreeCLoc
  threeCZL2 : Input15122ThreeCZL2
  threeEFlip4 : Input15122ThreeEFlip4
  threeDHSRu : Input15122ThreeDHSRu
  threeDM11 : Input15122ThreeDM11
  threeDLoc : Input15122ThreeDLoc
  threeDZL2 : Input15122ThreeDZL2
  sevenV2InQ : Input15124SevenV2InQ
  offenderTransfer : Input15128OffenderTransfer
  ml28 : Input15128ML
  natural : Input15128Natural
  sumNatDual : Input15128SumNatDual
  zDiagonal : Input15129ZDiagonal
  zOrder : Input15129ZOrder
  endNode : Input15129EndNode
  msHyp : Input15129MSHyp
  notC134 : Input15129NotC134Corr
  mFrattini : Input15129MFrattini

structure Inputs151XR12CorrM : Prop where
  lj : Input15120LJ
  b42List : Input15120B42List
  l2Block : Input15120L2Block
  rankTwoExcl : Input15120RankTwoExcl
  twoB : Input15120TwoB
  compList : Input15120CompList
  mlA : Input15120MLA
  mlB : Input15120MLB
  mlC : Input15120MLC
  mlD : Input15120MLD
  dichotomy : Input15122Dichotomy
  l3WreathStar : Input15122L3WreathStar
  threeCLoc : Input15122ThreeCLoc
  threeCZL2 : Input15122ThreeCZL2
  threeEFlip4 : Input15122ThreeEFlip4
  threeDHSRu : Input15122ThreeDHSRu
  threeDM11 : Input15122ThreeDM11
  threeDLoc : Input15122ThreeDLoc
  threeDZL2 : Input15122ThreeDZL2
  sevenV2InQ : Input15124SevenV2InQ
  offenderTransfer : Input15128OffenderTransfer
  ml28 : Input15128ML
  natural : Input15128Natural
  sumNatDual : Input15128SumNatDual
  zDiagonal : Input15129ZDiagonal
  zOrder : Input15129ZOrder
  endNode : Input15129EndNode
  msHyp : Input15129MSHyp
  notC134 : Input15129NotC134CorrM
  mFrattini : Input15129MFrattini

theorem Inputs151XR12Corr.toCorrM (h : Inputs151XR12Corr) : Inputs151XR12CorrM where
  lj := h.lj
  b42List := h.b42List
  l2Block := h.l2Block
  rankTwoExcl := h.rankTwoExcl
  twoB := h.twoB
  compList := h.compList
  mlA := h.mlA
  mlB := h.mlB
  mlC := h.mlC
  mlD := h.mlD
  dichotomy := h.dichotomy
  l3WreathStar := h.l3WreathStar
  threeCLoc := h.threeCLoc
  threeCZL2 := h.threeCZL2
  threeEFlip4 := h.threeEFlip4
  threeDHSRu := h.threeDHSRu
  threeDM11 := h.threeDM11
  threeDLoc := h.threeDLoc
  threeDZL2 := h.threeDZL2
  sevenV2InQ := h.sevenV2InQ
  offenderTransfer := h.offenderTransfer
  ml28 := h.ml28
  natural := h.natural
  sumNatDual := h.sumNatDual
  zDiagonal := h.zDiagonal
  zOrder := h.zOrder
  endNode := h.endNode
  msHyp := h.msHyp
  mFrattini := h.mFrattini
  notC134 := input15129NotC134CorrM_holds

theorem lemma151XR12_inputs_of_corrM
    (h : Inputs151XR12CorrM) (h159 : StageLemma1519) (h1416 : StageLemma1416) (h15 : StageLemma1515CE)
    (hC34 : C134L32CorrM) (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hF : A318Facts) (h36 : A36ForSQTK) (hK : KnownFacts15122Types) :
    Lemma15120InputU ∧ Lemma15122InputU ∧ Lemma15124InputU ∧ Lemma15128InputU ∧ Lemma15129InputU :=
  ⟨lemma15120InputU_of_named_inputs h.lj h.b42List h.l2Block h.rankTwoExcl input15120L45_holds
      h.twoB h.compList h.mlA h.mlB h.mlC h.mlD input15120MLE_holds,
    lemma15122InputU_of_corrected_inputs h.dichotomy input15122NoBorel_proved
      (input15122A7_of_inputs h118 h126 h37 h38 a7NotA38Type_holds)
      (input15122Rank2Block_of_wreath h118 h126 h37 h38 h.l3WreathStar)
      (input15122L45Block'_holds h118 h126 h37 h38)
      (input15122ThreeC_of' h118 h126 h37 h38 rankTwoSimpleNotA38_holds h.threeCLoc h.threeCZL2)
      (input15122ThreeD'_of_loc h118 h126 h37 h38 sporadicSixNotA38_holds h.threeDHSRu h.threeDM11
        h.threeDLoc h.threeDZL2)
      (input15122ThreeE_of' h118 h126 h37 h38 l45NotA38Type_holds input15122ThreeENoFlip_holds
        h.threeEFlip4),
    lemma15124InputU_of_named_inputs (input15124SevenBlock_holds hF h36 h38 hK)
      (input15124BlockV2_of hK h15 h.sevenV2InQ) (input15124NotBlock_of' h37 h38 hK h15 h1416),
    lemma15128InputU_of_named_inputs hC27 h.offenderTransfer h.ml28 h.natural h.sumNatDual,
    lemma15129InputU_of_named_inputs_corrM h159 h1416 h15 hC34 h.zDiagonal h.zOrder input15129FlagLocal_holds
      input15129P0_holds input15129Rank2_holds h.endNode input15129MSHypOne_holds h.notC134 h.mFrattini⟩

end CFSG.Quasithin
