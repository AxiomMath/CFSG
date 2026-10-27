module

public import CFSG.Quasithin.EmptyFaithful.SzN4YC
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

section Pointwise

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN4_structure (h113 : StageLemma14113) (kS : Lin2Setup) (kL : Lin2YLLabel)
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)
    (hYY : Yp = Y153 Mc M) (hYLV : ¬ YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G))
    (hYC : YC153 Yp L ≤ Subgroup.centralizer (L : Set G)) :
    (YL153 Yp L = oTwoUpper (Yp ⊓ Subgroup.centralizer (V₁ : Set G)) ∧
        YC153 Yp L = oTwoUpper (Yp ⊓ Subgroup.centralizer (V₂ : Set G))) ∨
      (YL153 Yp L = oTwoUpper (Yp ⊓ Subgroup.centralizer (V₂ : Set G)) ∧
        YC153 Yp L = oTwoUpper (Yp ⊓ Subgroup.centralizer (V₁ : Set G))) := by
  have hlab := kL G T Mc M V₁ V₂ Yp I L t c hn hYLV
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  obtain ⟨hYpeq, hE9, -⟩ := kS G T Mc M V₁ V₂ Yp I L t c hn
  have hVL := szN3_VZ_le_normalizer_L c
  subst hYY
  have hcore := szN3_core_eq h113 hh.hyp hE9
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, -⟩ := hh.decomp.model
  rcases hlab with hl | hl
  · exact Or.inl (szN3_key h113 hh.hyp hS hV₁ hV₂ hcore hYpeq hYC hVL c.c16.YL_ne hl)
  · exact Or.inr (szN3_key h113 hh.hyp hS.symm hV₂ hV₁ hcore hYpeq hYC hVL c.c16.YL_ne hl)

theorem szN4_S_le_normalizer_YL (h113 : StageLemma14113) (kS : Lin2Setup) (kL : Lin2YLLabel)
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)
    (hYY : Yp = Y153 Mc M) (hYLV : ¬ YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G))
    (hYC : YC153 Yp L ≤ Subgroup.centralizer (L : Set G)) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (YL153 Yp L : Set G) := by
  have hLC := szN4_structure h113 kS kL c hn hYY hYLV hYC
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hSV₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
    hh.hyp.Sgp153_le_normalizer_V₂ hh.decomp
  subst hYY
  rcases hLC with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]
    exact szN3_S_le_normalizer_oTwoUpper hh.hyp inf_le_left inf_le_right
  · rw [h1]
    exact szN3_S_le_normalizer_oTwoUpper hh.hyp inf_le_left hSV₂

theorem szN4_swap (h113 : StageLemma14113) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kS : Lin2Setup) (kL : Lin2YLLabel) (c : Ctx15316 T Mc M V₁ V₂ Yp I L t)
    (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n) (hYY : Yp = Y153 Mc M)
    (hYLV : ¬ YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G))
    (hYC : YC153 Yp L ≤ Subgroup.centralizer (L : Set G)) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ t₁ ∈ T, t₁ ∉ Sgp153 T V₁ ∧ B6.conjSub t₁ (YL153 Yp L) = YC153 Yp L := by
  have hSYL := szN4_S_le_normalizer_YL h113 kS kL c hn hYY hYLV hYC
  have hLC := szN4_structure h113 kS kL c hn hYY hYLV hYC
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  refine ⟨szN3_S_le_normalizer_L h37 h38 c hSYL, ?_⟩
  subst hYY
  exact szN3_exists_swap hh.hyp hh.decomp hLC

theorem szN4_UInYL (h113 : StageLemma14113) (kS : Lin2Setup) (kL : Lin2YLLabel) (kZ : Lin2ZLInYL)
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)
    (hYY : Yp = Y153 Mc M) (hYLV : ¬ YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G))
    (hYC : YC153 Yp L ≤ Subgroup.centralizer (L : Set G)) :
    blockU L ≤ YL153 Yp L := by
  have hSYL := szN4_S_le_normalizer_YL h113 kS kL c hn hYY hYLV hYC
  have hZ := kZ G T Mc M V₁ V₂ Yp I L t c hn hYY hYLV
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hOS : pCoreOf 2 L ≤ Sgp153 T V₁ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hLI)).trans
      c.facts.sylow.pCoreOf_le
  have hUN : blockU L ≤ Subgroup.normalizer (YL153 Yp L : Set G) := fun u hu =>
    hSYL (hOS (S153F.blockU_le_pCoreOf hu))
  have hYLL : YL153 Yp L ≤ L := (oTwoUpper_le _).trans inf_le_right
  obtain ⟨x, hxY, hxo, hx1⟩ : ∃ x ∈ YL153 Yp L, Odd (orderOf x) ∧ x ≠ 1 := by
    by_contra hno
    push Not at hno
    apply c.c16.YL_ne
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hy, ho⟩
    exact Subgroup.mem_bot.mpr (hno y (mem_oTwoUpper_of_odd hy ho) ho)
  obtain ⟨n, -, hnL⟩ := hn
  exact szN3_blockU_le_of_Z hnL hZ hYLL hUN hxY hxo hx1

theorem szN4_closing (h113 : StageLemma14113) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kS : Lin2Setup) (kL : Lin2YLLabel) (kZ : Lin2ZLInYL)
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)
    (hYY : Yp = Y153 Mc M) (hYLV : ¬ YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G))
    (hYC : YC153 Yp L ≤ Subgroup.centralizer (L : Set G)) :
    ∃ W : Subgroup G, W ≠ ⊥ ∧ IsPGroup 2 ↥W ∧ L ≤ Subgroup.normalizer (W : Set G) ∧
      T ≤ Subgroup.normalizer (W : Set G) ∧ Yp ≤ Subgroup.normalizer (W : Set G) := by
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  obtain ⟨hYpeq, -, -⟩ := kS G T Mc M V₁ V₂ Yp I L t c hn
  obtain ⟨hS, t₁, ht₁, ht₁S, hconj⟩ := szN4_swap h113 h37 h38 kS kL c hn hYY hYLV hYC
  have hUY := szN4_UInYL h113 kS kL kZ c hn hYY hYLV hYC
  have hYLL : YL153 Yp L ≤ L := (oTwoUpper_le _).trans inf_le_right
  have hU : blockU L ≤ pCoreOf 2 (YL153 Yp L) :=
    le_pCoreOf_of_le_normalizer 2 hUY
      (fun g hg => S153F.mem_normalizer_blockU (Subgroup.le_normalizer (hYLL hg)))
      ((pCoreOf_isPGroup 2 L).to_le S153F.blockU_le_pCoreOf)
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    hh.hyp.T_le_normalizer_Sgp153 hh.decomp
  have hidx : (Sgp153 T V₁).relIndex T = 2 := hh.decomp.relIndex_nS hh.hyp
  obtain ⟨n, -, hnL⟩ := hn
  obtain ⟨W, hW0, hW2, hWL, hWT, hWY⟩ := S153F.exists_closing_subgroup (L := L)
    (S := Sgp153 T V₁) (T := T) (YL := YL153 Yp L) (YC := YC153 Yp L) (t₁ := t₁) hS hTS ht₁ ht₁S
    (fun x hx => S153F.mem_or_mem_of_relIndex_eq_two hidx ht₁ ht₁S hx)
    (oTwoUpper_le _ |>.trans inf_le_right) hconj.symm hYC (S153F.blockU_ne_bot_of_isLin2Type hnL) hU
  exact ⟨W, hW0, hW2, hWL, hWT, hYpeq ▸ hWY⟩

end Pointwise


section NotCentralized

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem lin2NotCentralized_of_kL (kS : Lin2Setup) (kL : Lin2YLLabel) : Lin2NotCentralized := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hn hYLV
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hLn : ¬ L ≤ M := fun h => c.conc.2.1 (le_inf h hLle)
  have hLN : ∀ {V' : Subgroup G}, V' ≤ VZ T M → YL153 Yp L ≤ Subgroup.centralizer (V' : Set G) →
      L ≤ Subgroup.normalizer (V' : Set G) := by
    intro V' hV' hYLV'
    have hVC := szN3_le_centralizer_of_YL_noZ kS c hn hV' hYLV'
    intro l hl
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (hVC hv) l hl).symm
  rcases kL G T Mc M V₁ V₂ Yp I L t c hn hYLV with hl | hl
  · exact fun hN => hLn fun l hl' => hN (hLN hh.decomp.le₁ hl hl')
  · exact fun hN => hLn fun l hl' =>
      szN3_normalizer_V₂_le hh.hyp hh.decomp hN (hLN hh.decomp.le₂ hl hl')

end NotCentralized

section Final

theorem input15318_of_kL (h113 : StageLemma14113) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kS : Lin2Setup) (kL : Lin2YLLabel) (kZ : Lin2ZLInYL) : Input15318 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c _ hB
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  obtain ⟨hLc, hLn, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hn : ∃ n : ℕ, 1 < n ∧ IsLin2Type L n := hB.2
  have hsh : IsShort2 L := hB.1.1
  obtain ⟨hYpeq, hE9, hVdec⟩ := kS G T Mc M V₁ V₂ Yp I L t c hn
  by_cases hYLV : YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G)
  ·
    obtain ⟨n, -, hn⟩ := hn
    obtain ⟨y, hyY, hyo, hy1⟩ : ∃ y ∈ Yp ⊓ L, Odd (orderOf y) ∧ y ≠ 1 := by
      by_contra hno
      push Not at hno
      apply c.c16.YL_ne
      rw [eq_bot_iff]
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hx, ho⟩
      exact Subgroup.mem_bot.mpr (hno x hx ho)
    have hyYL : y ∈ YL153 Yp L := mem_oTwoUpper_of_odd hyY hyo
    have hVC : VZ T M ≤ Subgroup.centralizer (L : Set G) := by
      intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := hVdec v hv
      have hyv : a * b * y = y * (a * b) := Subgroup.mem_centralizer_iff.mp (hYLV hyYL) (a * b) hv
      have hyb : y * b = b * y := Subgroup.mem_centralizer_iff.mp hb y hyY.2
      have hay : a * y = y * a := by
        have h3 : a * y * b = y * a * b := by
          calc a * y * b = a * (y * b) := by group
            _ = a * (b * y) := by rw [hyb]
            _ = a * b * y := by group
            _ = y * (a * b) := hyv
            _ = y * a * b := by group
        exact mul_right_cancel h3
      have hya : y * a * y⁻¹ = a := by
        rw [← hay]
        group
      have haC := S153F.lin2NatFixedPoints_proved G L n hn y hyY.2 hyo hy1 a ha.1 hya
      exact mul_mem haC hb
    have hLV : L ≤ Subgroup.centralizer (VZ T M : Set G) := fun l hl =>
      Subgroup.mem_centralizer_iff.mpr fun v hv =>
        (Subgroup.mem_centralizer_iff.mp (hVC hv) l hl).symm
    have hHv : M = Subgroup.normalizer (VZ T M : Set G) := hh.hyp.isHv_of_inM' hh.hyp.inM
    have hLM : L ≤ M := by
      rw [hHv]
      exact fun l hl => Subgroup.centralizer_le_normalizer _ (hLV hl)
    exact hLn (le_inf hLM hLle)
  ·
    have hN1 : ¬ Subgroup.normalizer (V₁ : Set G) ≤ M :=
      lin2NotCentralized_of_kL kS kL G T Mc M V₁ V₂ Yp I L t c hn hYLV
    have hYY : Yp = Y153 Mc M := by
      rcases hh.cases with hY | ⟨hU, -⟩
      · exact hY
      · exact absurd (Hyp153.normalizer_V_le h113 hh.hyp hh.decomp hU).1 hN1
    have hYC := szN4_yc_central h113 h37 h38 kS kL c hn hsh hYY hYLV
    obtain ⟨W, hW0, hW2, hWL, hWT, hWY⟩ := szN4_closing h113 h37 h38 kS kL kZ c hn hYY hYLV hYC
    have hCO : W ≤ pCoreOf 2 (Subgroup.normalizer (W : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hW2
    have hXN : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (W : Set G) := sup_le (hYY ▸ hWY) hWT
    have hH : InH (Y153 Mc M ⊔ T) (Subgroup.normalizer (W : Set G)) :=
      ⟨hXN, fun hb => hW0 (le_bot_iff.mp (hb ▸ hCO))⟩
    have hNM : Subgroup.normalizer (W : Set G) ≤ M :=
      le_of_isUniqueM (Hyp153.lemma_15_3_7_unique h113 hh.hyp) hH
    exact hLn (le_inf (hWL.trans hNM) hLle)

end Final

end CFSG.Quasithin
