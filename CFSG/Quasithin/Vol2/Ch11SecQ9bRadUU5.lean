module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadUU4
public import CFSG.Quasithin.Vol2.Ch11SecQ9bC1
public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadU
public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadUP4
public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadUU3
public import CFSG.Quasithin.Vol2.Ch11SecQ9bXi
public import CFSG.Quasithin.Vol2.KGNatSL3LineFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K U : Subgroup G}

namespace C11P9B

theorem false_of_case_c_U (hF : Facts12) (hFb : Facts12b) (hC : CartanFacts)
    (hF11 : Facts11) (hN : NatFacts) (hL3 : FactLineSL3) (hLp : FactLineSp4)
    (hLg : FactLineG2) (hPG : SecS.FactParabGen) (h318 : A318Facts) (h36 : A36ForSQTK)
    (h38 : A38ForSQTK) (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h133 : Tmp1_3_3)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1111 : Stmt11_1_1)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁) (hV₂ : IsVi T L I 2 2 V₂)
    (hX : IsCartanX T L X) (hUV : U ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂)
    (hTU : T ≤ Subgroup.normalizer (U : Set G))
    (hLU : L ⊓ Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hK : K ∈ cComp (Subgroup.normalizer (U : Set G)))
    (hNK : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hlt : LOf L V₂ < K) (hc : Concl1111 (↥K ⧸ CFSG.pCore 2 ↥K) 2)
    (hnq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hFc' : ∀ y : ↥K, (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K) → Odd (orderOf y) →
      (y : G) ∈ Subgroup.centralizer (U : Set G)) : False := by
  obtain ⟨p, hp, hp2, hpF⟩ := exists_odd_prime_dvd_fitting hF hFb le_rfl hc hnq
  have : Fact p.Prime := ⟨hp⟩
  have hUV' : U ≤ fsuV T I := (le_V2_of_sup_eq hUV).trans (IsVi.le_fsuV hV₂)
  have hU1 := ne_bot_of_sup_eq h hV₂ hUV
  have hTsyl : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (U : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTU
  have hloc' : quasithinIsLocal T K :=
    isLocal_of_mem_cComp_of_sylow hTsyl (pCoreOf_normalizer_ne_bot_of_le h hUV' hU1) hK
  have hXi : IsXi T (xiP K p) :=
    h133 G T K p h.fsu.simple h.fsu.nonabelian h.fsu.qtke h.fsu.sylow hloc' hnq hp hp2 hpF
  have hKY : K ≤ Subgroup.normalizer (xiP K p : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_xiP p)
  have hV₀ := point_ne_bot hN h1102 h hV₁ hV₂ hUV
  have hTV₀ := T_le_normalizer_point hV₁ hTU
  obtain ⟨K₀, hK₀, hNK₀, hL₁K₀, hdesc⟩ := desc_point hFb hC hF hF11 hN h318 h36 h38 h331 h1102
    h1111 h hV₁ hV₂ hX inf_le_left hV₀ hTV₀ (xOne_le_normalizer_point hN h1102 h hV₁ hV₂ hX hLU)
    (xOne_inf_centralizer_point hC hF hN h1102 h hV₁ hV₂ hX hUV)
    (inf_normalizer_point_le hN h1102 h hV₁ hV₂ hUV)
  have hH₀ := pCoreOf_normalizer_ne_bot_of_le h (inf_le_left.trans (IsVi.le_fsuV hV₁)) hV₀
  have hYH : xiP K p ⊔ T ≤ Subgroup.normalizer ((V₁ ⊓ U : Subgroup G) : Set G) :=
    sup_le ((xiP_le_centralizer hFc').trans ((Subgroup.centralizer_le inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _))) hTV₀
  have := h.fsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  have hY5 := OE6.five_le_of_dvd_card_xiP h36c hloc (pCoreOf_normalizer_ne_bot_of_le h hUV' hU1)
    hK hNK hnq hp hpF
  have hL₁Y := lOf_le_normalizer_xi_gen h36c h hH₀ hK₀ hNK₀ hL₁K₀ hdesc hXi hYH hY5
  have hTY : T ≤ Subgroup.normalizer (xiP K p : Set G) := hXi.2.1
  have hOLT : pCoreOf 2 L ≤ T :=
    (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_inf_L h)).trans inf_le_left
  have hLY : L ⊔ T ≤ Subgroup.normalizer (xiP K p : Set G) :=
    sup_le ((le_sup_lOf₁₂ hPG hF11 hN hL3 hLp hLg h1102 h hV₁ hV₂).trans
      (sup_le (sup_le hL₁Y (hlt.le.trans hKY)) (hOLT.trans hTY))) hTY
  have hP1 := pCoreOf_ne_bot_of_isXi (charTwo_of_cComp_W h hUV' hU1 hTU hK hNK) hXi
    (xiP_le p) hKY
  have hPN := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (xiP K p)
  have hM := normalizer_le_of_isPGroup h331 h
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (xiP K p)) hP1 (hLY.trans hPN)
  exact not_le_normalizer_U hN h1102 h hV₂ hUV hLU hK hlt (hKY.trans (hPN.trans hM))

end C11P9B

theorem C11P9B.stmt11_1_2RadU_of (hF : Facts12) (hFb : Facts12b) (hFc : Facts12c)
    (hC : CartanFacts) (hF11 : Facts11) (hN : NatFacts) (hLp : FactLineSp4) (hLg : FactLineG2)
    (hPG : SecS.FactParabGen) (h318 : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h133 : Tmp1_3_3)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1111 : Stmt11_1_1) :
    C11P9B.Stmt11_1_2RadU := by
  intro G _ _ T L I n V₂ U h hV₂ hUV hTU hLU
  obtain ⟨K, hK, hLK, hNK, hcases⟩ :=
    C11P9B.cComp_U hF11 hN h1102 h36 h37 h38 h39 h312 h hV₂ hUV hTU hLU
  suffices hL₂K : LOf L V₂ = K by
    subst hL₂K
    exact ⟨hK, hNK⟩
  by_contra hne
  have hlt : LOf L V₂ < K := lt_of_le_of_ne hLK hne
  have hc : Concl1111 (↥K ⧸ CFSG.pCore 2 ↥K) n := hcases.resolve_left hne
  obtain ⟨V₁, hV₁, -⟩ := isVi_existsUnique hN h1102 h (i := 1) le_rfl (by norm_num)
  obtain ⟨X, hX⟩ := exists_isCartanX h
  rcases C11P9B.modules3n_U hFc hN KGNat.factLineSL3_holds hLp hLg h1102 h1103 h hV₂ hUV hTU hK
      hNK hLK hc with ⟨rfl, hA7, hZ⟩ | ⟨rfl, hnq, hFit⟩
  · exact C11P9B.false_of_case_b_U hFb hFc hC hN h318 h36 h38 h1102 h hV₁ hV₂ hX hUV hLU hK hNK
      hLK hA7 hZ
  · exact C11P9B.false_of_case_c_U hF hFb hC hF11 hN KGNat.factLineSL3_holds hLp hLg hPG h318
      h36 h38 h36c h133 h331 h1102 h1111 h hV₁ hV₂ hX hUV hTU hLU hK hNK hlt hc hnq hFit

end CFSG.Quasithin.Vol2.Ch11.SecA
