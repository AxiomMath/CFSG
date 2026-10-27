module

public import CFSG.Quasithin.EmptyFaithful.T1515cD2
public import CFSG.Quasithin.EmptyFaithful.T1515cF
public import CFSG.Quasithin.EmptyFaithful.T1515cTop

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

structure Lemma15119Used (T Mc M Z₁ V₂ : Subgroup G) : Prop where
  one : oddCoreIn (g1_1516 Z₁) = ⊥
  two : ∀ K : Subgroup G, K ≤ g1_1516 Z₁ → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
    mZ1516 Mc Z₁ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ mZ1516 Mc Z₁
  three : oTwoFIn (g1_1516 Z₁) ≤ mZ1516 Mc Z₁
  four : ∀ H : Subgroup G, mZ1516 Mc Z₁ ≤ H → H ≤ g1_1516 Z₁ → oTwoFstarIn H ≤ mZ1516 Mc Z₁ →
    H = mZ1516 Mc Z₁
  six : ∃ L : Subgroup G, L ∈ cComp (g1_1516 Z₁) ∧
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧ ¬ L ≤ mZ1516 Mc Z₁
  seven : ∀ L : Subgroup G, L ∈ cComp (g1_1516 Z₁) →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → ¬ L ≤ mZ1516 Mc Z₁ →
    oTwoUpper (M ⊓ Subgroup.centralizer (Z₁ : Set G)) ⊔ V₂ ≤ Subgroup.normalizer (L : Set G) ∧
      ⁅L, V₂⁆ ≠ ⊥

omit [Finite G] in
theorem Lemma15119Concl.toUsed {T Mc M Z₁ V₂ : Subgroup G} (h : Lemma15119Concl T Mc M Z₁ V₂) :
    Lemma15119Used T Mc M Z₁ V₂ :=
  ⟨h.one, h.two, h.three, h.four, h.six, h.seven⟩

theorem lemma_15_1_19_used (h37 : A37ForSQTK) (h38 : A38ForSQTK) {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h18 : Lemma15118Concl T Mc M Z₁)
    (hx18 : Lemma15118Extra T Mc M Z₁) : Lemma15119Used T Mc M Z₁ V₂ := by
  have h1 : oddCoreIn (g1_1516 Z₁) = ⊥ := lemma_15_1_19_one hC.qtfe hC.mf hC.setting h18
  have h2 := lemma_15_1_19_two1515c hC h18 hx18
  have h3 : oTwoFIn (g1_1516 Z₁) ≤ mZ1516 Mc Z₁ :=
    oTwoFIn_le_of_two (mZ1516_le_g1 Mc Z₁) h1 h2
  have h4 := lemma_15_1_19_four h18.five.2.1
  exact ⟨h1, h2, h3, h4, lemma_15_1_19_six_of_three_four hC.qtfe h18 h3 h4,
    lemma_15_1_19_seven h37 h38 hC.qtfe hC.mf hC.setting⟩

@[expose] def Lemma15120InputU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15118Extra T Mc M Z₁ →
    (CharTwo L → ⁅L, thompsonJ (s1516 T Z₁)⁆ = L ∧
      (Case15120TwoA T Mc Z₁ L ∨ Case15120TwoB T Mc Z₁ L ∨ Case15120TwoC Mc Z₁ L)) ∧
    (IsComponentOf L (g1_1516 Z₁) →
      Case15120ThreeA Mc Z₁ L ∨ Case15120ThreeB Mc Z₁ L ∨ Case15120ThreeC T Mc Z₁ L ∨
        Case15120ThreeD T Mc Z₁ L ∨ Case15120ThreeE T Mc Z₁ L)

@[expose] def Lemma15121InputU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → Lemma15118Extra T Mc M Z₁ → Lemma15121Concl Mc Z₁ L

@[expose] def Lemma15122InputU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15120Concl T Mc M Z₁ L →
    Lemma15121Concl Mc Z₁ L → Lemma15118Extra T Mc M Z₁ → Lemma15122Concl T Mc M Z₁ L

@[expose] def Lemma15124InputU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Ce15Small T Mc M → (Ce15Four T Mc M ∨ Ce15Six T Mc M 3) ∧ ¬ IsLnBlock L 3

@[expose] def Lemma15125InputRestU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L →
    L = oPrimeResidualOf 3 (g1_1516 Z₁) ∧ ¬ V₁ ≤ Subgroup.centralizer (L : Set G) ∧
      ¬ IsAltBlockType L 7

@[expose] def Lemma15127InputU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L → Lemma15125Concl T Z₁ V₁ L → Lemma15126Concl L →
    Lemma15127Concl Z₂ L

@[expose] def Lemma15128InputU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L → Lemma15125Concl T Z₁ V₁ L → Lemma15126Concl L →
    Lemma15127Concl Z₂ L → Lemma15128Concl T Mc Z₁ Z₂ L

@[expose] def Lemma15129InputU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15122Concl T Mc M Z₁ L →
    Lemma15124Concl T Mc M Z₁ V₁ V₂ L → Lemma15125Concl T Z₁ V₁ L → Lemma15126Concl L →
    Lemma15127Concl Z₂ L → Lemma15128Concl T Mc Z₁ Z₂ L → Lemma15129Concl Z₂ L

theorem Lemma15124InputU.toInput (h : Lemma15124InputU) : Lemma15124Input :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 hs =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19.toUsed hL h22 hs

theorem Lemma15125InputRestU.toInput (h : Lemma15125InputRestU) : Lemma15125InputRest :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19.toUsed hL h22 h24

theorem Lemma15127InputU.toInput (h : Lemma15127InputU) : Lemma15127Input :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26 =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19.toUsed hL h22 h24 h25 h26

theorem Lemma15128InputU.toInput (h : Lemma15128InputU) : Lemma15128Input :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26 h27 =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19.toUsed hL h22 h24 h25 h26 h27

theorem Lemma15129InputU.toInput (h : Lemma15129InputU) : Lemma15129Input :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26 h27 h28 =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19.toUsed hL h22 h24 h25 h26 h27 h28

theorem lemma15119Concl_of_used_input251515c (h25 : Lemma15119Input25)
    {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂)
    (h17 : Lemma15117Concl T M Z₁) (h18 : Lemma15118Concl T Mc M Z₁)
    (hU : Lemma15119Used T Mc M Z₁ V₂) : Lemma15119Concl T Mc M Z₁ V₂ :=
  ⟨hU.one, hU.two, hU.three, hU.four,
    (h25 G T Mc M Z₁ Z₂ V₁ V₂ hC h17 h18 hU.one hU.four).five, hU.six, hU.seven⟩

theorem Lemma15120InputU.of_input (h25 : Lemma15119Input25) (h : Lemma15120Input) :
    Lemma15120InputU :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 hU hL _ => by
    obtain ⟨h2, h3⟩ := h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18
      (lemma15119Concl_of_used_input251515c h25 hC h17 h18 hU)
      (hL.isL1520 h18.four (hC.setting.pCore_g1_ne_bot hC.qtfe hC.mf))
    exact ⟨h2, fun hc => (h3 hc).2⟩

theorem Lemma15121InputU.of_input (h25 : Lemma15119Input25) (h : Lemma15121Input) :
    Lemma15121InputU :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 hU _ =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 (lemma15119Concl_of_used_input251515c h25 hC h17 h18 hU)

theorem Lemma15122InputU.of_input (h25 : Lemma15119Input25) (h : Lemma15122Input) :
    Lemma15122InputU :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 hU hL h20 h21 _ =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 (lemma15119Concl_of_used_input251515c h25 hC h17 h18 hU)
      hL h20 h21

theorem Lemma15124InputU.of_input (h25 : Lemma15119Input25) (h : Lemma15124Input) :
    Lemma15124InputU :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 hU hL h22 hs =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 (lemma15119Concl_of_used_input251515c h25 hC h17 h18 hU)
      hL h22 hs

theorem Lemma15125InputRestU.of_input (h25 : Lemma15119Input25) (h : Lemma15125InputRest) :
    Lemma15125InputRestU :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 hU hL h22 h24 =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 (lemma15119Concl_of_used_input251515c h25 hC h17 h18 hU)
      hL h22 h24

theorem Lemma15127InputU.of_input (h25 : Lemma15119Input25) (h : Lemma15127Input) :
    Lemma15127InputU :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 hU hL h22 h24 h25' h26 =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 (lemma15119Concl_of_used_input251515c h25 hC h17 h18 hU)
      hL h22 h24 h25' h26

theorem Lemma15128InputU.of_input (h25 : Lemma15119Input25) (h : Lemma15128Input) :
    Lemma15128InputU :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 hU hL h22 h24 h25' h26 h27 =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 (lemma15119Concl_of_used_input251515c h25 hC h17 h18 hU)
      hL h22 h24 h25' h26 h27

theorem Lemma15129InputU.of_input (h25 : Lemma15119Input25) (h : Lemma15129Input) :
    Lemma15129InputU :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 hU hL h22 h24 h25' h26 h27 h28 =>
    h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 (lemma15119Concl_of_used_input251515c h25 hC h17 h18 hU)
      hL h22 h24 h25' h26 h27 h28

theorem lemma15123Standalone_of_inputs1515c (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hC65 : Construction1516SixFive) (h15 : StageLemma1515CE)
    (h19s : StageLemma1519) (h14 : StageLemma15114) (hI19 : Lemma15119Input25)
    (hI20 : Lemma15120Input) (hI21 : Lemma15121Input) (hI22 : Lemma15122Input)
    (hI23 : Lemma15123Input) : Lemma15123Standalone := by
  have h1416 : StageLemma1416 := stageLemma1416_of_a3 h37 h38 h39
  intro G _ _ T Mc M hq hM hCE h5
  obtain ⟨Z₁, Z₂, V₁, V₂, hSX⟩ := hC65 G T Mc M hq hM hCE h5
  have hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂ := hSX.toSetting1516
  have hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ := ⟨hq, hM, hCE, hS⟩
  have h15' := h15 G T Mc M hq hM hCE
  have h14' := h14 G T Mc M hq hM hCE
  have h19' := h19s G T Mc M hq hM hCE
  have h17 := lemma_15_1_17 hq hM hS h19'
  have h18c := lemma_15_1_18 as116Statement hC hSX.toExtra h15' h14' h19' h17
  have h19c := lemma_15_1_19_of_input_rest' h37 h38
    (lemma15119InputRest'_of_input235 (lemma15119Input235_of_input25 hI19)) hC h17 h18c
  obtain ⟨L, hLc, hLq, hLn⟩ := h19c.six
  have hL : IsL1519 Mc Z₁ L := ⟨hLc, hLq, hLn⟩
  have hL20 : IsL1520 T Mc Z₁ L := hL.isL1520 h18c.four (hS.pCore_g1_ne_bot hq hM)
  have h20 := lemma_15_1_20 hI20 hC (h1416 G T Mc hq).1 h15' h17 h18c h19c hL20
  have h21 := lemma_15_1_21 hI21 hC h17 h18c h19c (L := L)
  have h22 := lemma_15_1_22 hI22 hC h17 h18c h19c hL h20 h21
  have h53 := hI23 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 5 (Or.inr rfl) h5
  exact absurd h53 (by norm_num)

theorem theorem1515_of_inputs3_ce3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h15 : StageLemma1515CE) (h157 : StageLemma1517) (h19s : StageLemma1519)
    (h110 : StageLemma15110) (h113 : StageLemma15113) (h14 : StageLemma15114)
    (hD : M11TypesDisjoint1522) (h23 : Lemma15123Standalone)
    (hI20 : Lemma15120InputU) (hI21 : Lemma15121InputU) (hI22 : Lemma15122InputU)
    (hI24 : Lemma15124InputU) (hI25 : Lemma15125InputRestU) (hI27 : Lemma15127InputU)
    (hI28 : Lemma15128InputU) (hI29 : Lemma15129InputU) : StageTheorem1515 := by
  have h1416 : StageLemma1416 := stageLemma1416_of_a3 h37 h38 h39
  intro G _ _ T Mc M hq hM hCE hce
  have hsmall : Ce15Small T Mc M :=
    ce15Small_of_not_six_five hce (h23 G T Mc M hq hM hCE)
  obtain ⟨Z₁, Z₂, V₁, V₂, hSX⟩ := exists_setting_of_ce15Small h15 h157 h19s h110 h113 hq hM hCE hsmall
  have hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂ := hSX.toSetting1516
  have hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ := ⟨hq, hM, hCE, hS⟩
  have h15' := h15 G T Mc M hq hM hCE
  have h14' := h14 G T Mc M hq hM hCE
  have h19' := h19s G T Mc M hq hM hCE
  have h17 := lemma_15_1_17 hq hM hS h19'
  have h18c := lemma_15_1_18 as116Statement hC hSX.toExtra h15' h14' h19' h17
  have hx18 := lemma_15_1_18_extra hC hSX.toExtra h15' h14' h19' h17
  have h19c := lemma_15_1_19_used h37 h38 hC h18c hx18
  obtain ⟨L, hLc, hLq, hLn⟩ := h19c.six
  have hL : IsL1519 Mc Z₁ L := ⟨hLc, hLq, hLn⟩
  have hL20 : IsL1520 T Mc Z₁ L := hL.isL1520 h18c.four (hS.pCore_g1_ne_bot hq hM)
  have h20 : Lemma15120Concl T Mc M Z₁ L := by
    obtain ⟨h2, h3⟩ := hI20 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL hx18
    exact ⟨lemma_15_1_20_sylow h18c.four hL20,
      lemma_15_1_20_one (h1416 G T Mc hq).1 hM h15' hL20, h2,
      fun hc => ⟨isPGroup_two_center_of_isComponentOf1515c hc h19c.one, h3 hc⟩⟩
  have h21 : Lemma15121Concl Mc Z₁ L := hI21 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hx18
  have h22 : Lemma15122Concl T Mc M Z₁ L :=
    hI22 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h20 h21 hx18
  have h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L := by
    obtain ⟨h1, h2⟩ := hI24 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 hsmall
    have h7 := not_seven_of_four_or_six h1
    exact ⟨h1, (hS.decomp_other h7).2.1, h2, lemma_15_1_24_three hS h15' hsmall,
      (hS.y_facts hsmall).1.2.2.1, lemma_15_1_24_four hq hM hS hsmall h1⟩
  have h25 : Lemma15125Concl T Z₁ V₁ L := by
    obtain ⟨h1, h3, h5⟩ := hI25 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 h24
    exact ⟨h1, lemma_15_1_25_two hD hC h15' h19' h19c.one h17 h22 h24 h1, h3,
      lemma_15_1_25_four hS h24.one, h5, lemma_15_1_25_six hS h24.one⟩
  have h26 := lemma_15_1_26 hL h22 h24 h25
  have h27 : Lemma15127Concl Z₂ L := hI27 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 h24 h25 h26
  have h28 : Lemma15128Concl T Mc Z₁ Z₂ L :=
    hI28 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 h24 h25 h26 h27
  have h29 : Lemma15129Concl Z₂ L :=
    hI29 G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18c h19c hL h22 h24 h25 h26 h27 h28
  exact h29 h28.1

theorem theorem1515_of_inputs_ce3
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h23 : Lemma15123Standalone)
    (h316 : Theorem316Statement) (h317 : Theorem317Statement) (h319 : Lemma319Statement)
    (h1414 : StageLemma1414) (h1416 : StageLemma1416) (h1417 : StageLemma1417)
    (hD : Description1512CE) (hN : Nilpotency1512CE) (hStep : Step1514Gen)
    (h17 : StageLemma1517) (h158 : StageLemma1518) (h1511one : StageLemma15111One)
    (h1512four : StageLemma15112Four)
    (hI20 : Lemma15120InputU) (hI21 : Lemma15121InputU) (hI22 : Lemma15122InputU)
    (hI24 : Lemma15124InputU) (hI25 : Lemma15125InputRestU) (hI27 : Lemma15127InputU)
    (hI28 : Lemma15128InputU) (hI29 : Lemma15129InputU) : StageTheorem1515 := by
  obtain ⟨-, h15, -, h19, -, h113, h14⟩ :=
    stage151_of_inputs_ce h316 h317 h319 h1414 h1416 h1417 hD hN hStep h17 h158 h1511one
      h1512four
  have h110 : StageLemma15110 := stageLemma15110_of_ce h1416 h15
  exact theorem1515_of_inputs3_ce3 h37 h38 h39 h15 h17 h19 h110 h113 h14
    (m11TypesDisjoint1522_of_orders psuThreeThreeOrder1522 threeD4TwoOrder1522) h23 hI20 hI21 hI22
    hI24 hI25 hI27 hI28 hI29

end CFSG.Quasithin
