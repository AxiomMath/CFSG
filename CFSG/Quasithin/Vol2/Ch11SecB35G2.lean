module

public import CFSG.Quasithin.Vol2.Ch11SecB35G1
public import CFSG.Quasithin.Vol2.Ch11SecB21OddS
public import CFSG.Quasithin.Vol2.Ch11SecB35F
public import CFSG.Quasithin.Vol2.Ch11SecB36Amal
public import CFSG.Quasithin.Vol2.Ch11SecB36Claim
public import CFSG.Quasithin.Vol2.Ch11SecB36Flag
public import CFSG.Quasithin.Vol2.Ch11SecB36Two
public import CFSG.Quasithin.Vol2.Ch11SecCB51

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped Pointwise

theorem field11_3_5_of (hNP : FactNPrimeNat) (hNP2 : FactNPrimeTwoNat) (hNF : NatFacts)
    (hDHB : DerivedHallBorel) (h4413 : H13.Stmt4_4_13Lie) (h442 : TmpL4_4_2)
    (hNS : FactNotSmall443) (h3228 : Ch10.TmpL6_3_2_2_eight) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (hFC : FactCentralizerTwo) (h51 : AsB51) (h56 : AsB56)
    (hKF : SecC.KindModuleFacts) (h322 : Ch10.TmpL6_3_2_2_two) (hFV : FactsVM)
    (hPT : FactPointTrans) (hG2o : FactG2DerivedOrder) (h63 : ASInputs.AS_E_6_3)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1104 : Stmt11_0_4)
    (h1122 : Stmt11_2_2) (h1123 : Stmt11_2_3) (h1133 : Stmt11_3_3) : Field11_3_5 := by
  intro G _ _ T L I n V₁ H K k F _ _ hyp hV₁ h31 hnot hKc hHK hlie hF hk hiso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set V := fsuV T I with hVdef
  have hH := h31.hstar
  have hmin := minParabolic_of_isHStar h331 hyp hH
  have hV := isElemAbelian_fsuV hyp
  have hnH : (n : ℕ∞) ≤ E1.nParam H := by
    obtain ⟨-, V₂, -, -, hV₂, -⟩ := exists_isVi hNF h1102 hyp
    have hs := sParam_le_nParam hyp h31 (h1133 G T L I n V₁ H hyp hV₁ h31 hnot) hV
    by_cases hG2 : KindG2 L (fsuV T I) n
    · have hm := (h1122 G T L I n (2 * n) V₁ V₂ hyp hV₁ hV₂ (Or.inl ⟨hG2, rfl⟩)).2.2.2.1 hV
      rw [hm] at hs
      exact le_trans (by exact_mod_cast (by omega : n ≤ 2 * n)) hs
    · have hm := (h1122 G T L I n n V₁ V₂ hyp hV₁ hV₂ (Or.inr ⟨hG2, rfl⟩)).2.2.2.1 hV
      rw [hm] at hs
      exact hs
  have hn1 : 1 < E1.nParam H := lt_of_lt_of_le (by exact_mod_cast hyp.one_lt) hnH
  obtain ⟨B, hB, hBab, hTB⟩ := hDHB G T M H hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.sylow ⟨isMaxTwoLocal_M h331 hyp, hyp.normal⟩ (normalizer_T_le h331 hyp) hH hn1
  have hBV : B ⊓ Subgroup.centralizer (V : Set G) = ⊥ :=
    inf_centralizer_hall_eq_botS h4413 h442 hNS h331 h3228 hyp hH hKc hHK hlie hB hBab hTB
  have hTX : T ≤ H ⊓ M := le_inf hH.1.1 hyp.normal
  have hTS : QuasithinUnique.IsSylowTwoOf T (H ⊓ M) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTX
  have hBT : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) :=
    mul_comm_sylow_of_normalizes (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M))
      (B6.pCoreOf_two_le_of_isSylowTwoOf hTS) hTX hB.1 hTB inf_le_right
  obtain ⟨Y, hYB, hYc, hYcard⟩ := exists_cyclic_le_hall hmin hKc hHK hlie hF hk hiso hB
  have hLJ := eq_commutator_thompsonJ_of_moves hC58 h317 h3228 hFC h331 h1102 hyp hH h31.moves
  have hMVM : M ≤ Subgroup.normalizer (VM T L I : Set G) := le_normalizer_conjClosure V M
  rcases SecC.fsuV_eq_VM_or h51 h56 h1102 hKF h322 hyp hLJ with hVVM | ⟨hk3, -, hVM2⟩
  ·
    have hBN : B ≤ Subgroup.normalizer (V : Set G) := by
      have h1 := hB.1.trans (inf_le_right.trans hMVM)
      rwa [← hVVM] at h1
    have hTV := T_le_normalizer_fsuV T I
    have h1 := le_nPrime_autI hV hBN hTV hBV
      (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTV) hBab hB.2.1 hBT hYB hYc hYcard
    have h2 := hNP G L V n hV hyp.one_lt (L_le_normalizer_fsuV hyp)
      (commutator_fsuV_eq_self hyp) (natModuleOf_fsuV h1102 hyp) ⊤ le_top
      (inf_le_right.trans (normalizer_fsuV_le h331 hyp))
    exact le_trans (by exact_mod_cast h1.trans h2) hnH
  ·
    obtain ⟨-, V₂, -, -, hV₂, -⟩ := exists_isVi hNF h1102 hyp
    have hfl := flag36_of hNF hG2o h331 h1102 h1103 h1104 hyp hV₁ hV₂ hk3 hVM2 hLJ
    have hE61 := hypE61_VM h331 h1102 h1103 hyp
    have hn := hfl.two_le
    have hmP : E3.mParam (autI hfl.elemW (Subgroup.normalizer (L : Set G))) = 2 * n := by
      rw [← autI_top_eq_VM h331 h1103 hyp hfl.elemW]
      exact hFV.param G L (fsuV T I) (VM T L I) ⊤ T V₁ V₂ n hfl
    have h63' := h63 G T _ (VM T L I) hfl.elemW hE61 (by rw [hmP]; omega)
    have hs : E3.sParam hfl.elemW = 2 * n := by rw [h63'.2, hmP]
    have hCV₁ := h31.sl3 hk3
    have hN1 := (h1123 G T L I n V₁ hyp hV₁).2 hCV₁
    have hNV₁ : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
      fun x hx => normalizer_inf_le h1103 hyp hV₁ ⟨hN1 hx, hx⟩
    have hV3 := relIndex_fsuV_of_SL3 hG2o h1102 hyp hk3
    have hW0 := wClos_VM_not_le h331 h1102 h1103 hyp h31.hstar
      fun g hgT hgc hgN => claim36 hFV hPT hyp hfl hs hV3 hNV₁ hgT hgc hgN
    have hsk := sParam_le_nParam_gen hyp h31 hfl.elemW hW0
    rw [hs] at hsk
    have hBU : B ⊓ Subgroup.centralizer (VM T L I : Set G) = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_left B (Subgroup.centralizer_le (le_conjClosure V M))).trans
        hBV.le)
    have hBN : B ≤ Subgroup.normalizer (VM T L I : Set G) := hB.1.trans (inf_le_right.trans hMVM)
    have hTU : T ≤ Subgroup.normalizer (VM T L I : Set G) := hyp.normal.trans hMVM
    have h1 := le_nPrime_autI hfl.elemW hBN hTU hBU
      (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTU) hBab hB.2.1 hBT hYB hYc hYcard
    have h2 := hNP2 G L (VM T L I) n hfl.elemW hyp.one_lt (Subgroup.le_normalizer.trans hMVM)
      ((vmTwoNatural_iff T L I n).mp hVM2) ⊤ le_top
      (inf_le_right.trans (normalizer_VM_le h331 h1103 hyp))
    exact le_trans (by exact_mod_cast h1.trans h2) hsk

end CFSG.Quasithin.Vol2.Ch11.SecB
