module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Canon
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Canon2Rk2
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Res
public import CFSG.Quasithin.Recognition.GoldschmidtF112ROmega4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

namespace Hyp5_2_4

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}

theorem cases_of_listC (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) (hF11 : StmtF11_5_2) (hbor : Stmt5_2_6_borel) (h524 : Stmt5_2_4)
    (hor : Stmt5_2_6_orient) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hnotL : ¬ centerOf (sec52S M H) ≤ Subgroup.centralizer (L : Set G))
    (hSL : sec52S M H ≤ L) (hSL₂ : sec52S M H ≤ L₂) {L1' L2' : Subgroup G}
    (hor12 : (L1' = L ∧ L2' = L₂) ∨ (L1' = L₂ ∧ L2' = L))
    (hlist : F112ListALegacyBare L1' L2' (sec52S M H)) :
    Cases5_2_6 (sec52Alpha M L H B D L₂) L L₂ n := by
  have hn := hyp.isL2Quot_L
  have hn1 : 1 ≤ n := by have := hyp.toHyp5_0_1.two_le; omega
  obtain ⟨h111', hq', hSn', hns1, hns2⟩ := hyp.f112_hyps hF11 hbor h524 hor12
  have hα := fun {P : ∀ (Y : Type) [Group Y], Prop} => hyp.isAmalgamOfGroup_of_orient h331 hR hbor
    (P := P) hor12
  have hαU := fun {f : ℕ} => hyp.isU4ExtTwo_of_orient h331 hR hbor (f := f) hor12
  have hLS : L ⊔ sec52S M H = L := sup_eq_left.mpr hSL
  have hL₂S : L₂ ⊔ sec52S M H = L₂ := sup_eq_left.mpr hSL₂
  have horient := hor G L1' L2' (sec52S M H) h111' hq' hSn' hns1 hns2
  unfold Cases5_2_6
  rcases hor12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    subst L1' L2'
    unfold F112ListALegacyBare at hlist
    rcases hlist with ⟨f, -, hA, hb1, ht1, hb2, ht2⟩ | ⟨f, hf, hA, hb1, ht1, hb2, ht2⟩ | h3 | h4 |
      ⟨a, -, -, ⟨e⟩, -⟩ | h6 | ⟨-, ⟨F, _, _, hF, ⟨e⟩⟩, -⟩
    · have hfn := hyp.eq_of_isLin2Type_L ht1
      subst hfn
      exact Or.inl ⟨hα hA, hb1, ht1, hb2, ht2⟩
    · have hfn := hyp.eq_of_isLin2Type_L ht1
      subst hfn
      refine Or.inr (Or.inl ⟨hα (IsAmalgamOfGroup.mono hA fun Y _ hY => ?_), hb1, ht1, hb2, ht2⟩)
      rcases hY with ⟨h1, -⟩ | ⟨-, hY⟩
      · omega
      · exact hY
    · exact absurd (horient (Or.inl h3)) hnotL
    · exact absurd (horient (Or.inr (Or.inl h4))) hnotL
    · exact (not_mulEquiv_sz_of_isL2Quot hn1 hn e).elim
    · exact absurd (horient (Or.inr (Or.inr h6))) hnotL
    · exact (not_mulEquiv_su34_of_isL2Quot hn1 hn hF e).elim
  ·
    subst L1' L2'
    unfold F112ListALegacyBare at hlist
    rcases hlist with ⟨f, -, hA, hb1, ht1, hb2, ht2⟩ | ⟨f, hf, hA, hb1, ht1, hb2, ht2⟩ |
      ⟨f, hf, hA, hq1, hq2, hsp, hc⟩ | ⟨f, hf, hA, hq1, hsp, hq2, hc⟩ |
      ⟨a, ha, hA, he, hc1, hq2, hc2⟩ | ⟨f, hf, hA, hq1, hsp, hb2, hq2, hO⟩ |
      ⟨hA, hSU, hsp, hq2, hc⟩
    · have hfn := hyp.eq_of_isLin2Type_L ht2
      subst hfn
      exact Or.inl ⟨hα hA, hb2, ht2, hb1, ht1⟩
    · have hfn := hyp.eq_of_isLin2Type_L ht2
      subst hfn
      refine Or.inr (Or.inl ⟨hα (IsAmalgamOfGroup.mono hA fun Y _ hY => ?_), hb2, ht2, hb1, ht1⟩)
      rcases hY with ⟨h1, -⟩ | ⟨-, hY⟩
      · omega
      · exact hY
    · have hfn := hyp.eq_of_isL2Quot_L (by omega) hq2
      subst hfn
      refine Or.inr (Or.inr (Or.inl
        ⟨hα (IsAmalgamOfGroup.mono hA fun Y _ hY => ?_), hq2, hq1, ?_, ?_⟩))
      · rcases hY with ⟨h1, -⟩ | ⟨-, hY⟩
        · omega
        · exact hY
      · rwa [hL₂S] at hsp
      · rwa [hLS] at hc
    · have hfn := hyp.eq_of_isL2Quot_L (by omega) hq2
      subst hfn
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hα hA, hq2, hc, hq1, hsp⟩)))
    · have hfn := hyp.eq_of_isL2Quot_L (by omega) hq2
      subst hfn
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hα (IsAmalgamOfGroup.mono hA fun Y _ hY => ?_), hq2, hc2, ⟨a, rfl, he⟩, hc1⟩))))
      rcases hY with ⟨h1, -⟩ | ⟨-, -, hY⟩
      · omega
      · exact hY
    · have hfn := hyp.eq_of_isL2Quot_L (by omega) hq2
      have h2n : 2 < 2 * f := by omega
      subst hfn
      have hOm := F112R.isOmega4MinusBlock_of_type (by omega) hb2 hq2 hO
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, rfl, h2n, ?_, hOm, hq1,
        hsp⟩)))))
      rcases hA with hA | hA
      · exact Or.inl (hα hA)
      · exact Or.inr (hαU hA)
    · have hfn := hyp.eq_of_isL2Quot_L (by norm_num) hq2
      subst hfn
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hα hA, hq2, hc, hSU,
        hsp⟩)))))

end Hyp5_2_4

theorem stmt5_2_6_trC_of (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) (hF : RankOneListedFacts.{0}) (hF11 : StmtF11_5_2)
    (hbor : Stmt5_2_6_borel) (h524 : Stmt5_2_4) (h510 : Stmt5_1_10)
    (h38 : Vol2Native.A38ForSQTKCat) (hU3 : FactU3Cover) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h512 : Stmt5_1_2) (hsecC : Stmt5_2_6_secondC)
    (hU4C : Stmt5_2_6_U4extC) (hU4 : Stmt5_2_6_U4ext) (hrk2C : Stmt5_2_6_L2K_rank2C) :
    Stmt5_2_6_trC := by
  rintro G _ _ T M L V H B D L₂ n hyp ⟨L1', L2', hor12, -, hlistC, hsecond⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  have hor : Stmt5_2_6_orient := stmt5_2_6_orient_holds
  obtain ⟨h111', hq', hSn', hns1, hns2⟩ := hyp.f112_hyps hF11 hbor h524 hor12
  have hnotL : ¬ centerOf (sec52S M H) ≤ Subgroup.centralizer (L : Set G) := fun hc =>
    h.not_omega_le_centralizer h331 hC58 h317 h512 hyp.ch5Module hyp.hStar hN.2.1
      (hyp.toHyp5_1_8.omega_le_centerOf.trans hc)
  obtain ⟨hlist, hab⟩ := Hyp5_2_4.bridge hF h331 hR hF11 hbor h524 hsecC hU4C hyp hnotL hor12
    hlistC hsecond
  have horient : (F112E3 L1' L2' (sec52S M H) ∨ F112E4 L1' L2' (sec52S M H) ∨
      F112E6 L1' L2' (sec52S M H)) → L1' = L₂ ∧ L2' = L := by
    intro he
    have hc := hor G L1' L2' (sec52S M H) h111' hq' hSn' hns1 hns2 he
    rcases hor12 with ⟨h1, -⟩ | h12
    · rw [h1] at hc
      exact absurd hc hnotL
    · exact h12
  have hSN : sec52S M H ≤ Subgroup.normalizer (L₂ : Set G) :=
    (le_sup_right.trans le_sup_left).trans (h524 G T M L V H B D L₂ n hyp).2.2.2
  have hS2 : sec52S M H ≤ L₂ ∨ ∃ t : G, t ^ 2 = 1 ∧
      t ∈ Subgroup.normalizer (pCoreOf 2 L₂ : Set G) ∧
      pCoreOf 2 (L₂ ⊔ sec52S M H) ≤ pCoreOf 2 L₂ ⊔ Subgroup.zpowers t := by
    rcases hab with ⟨-, -, hS1, hS2⟩ | hext
    · left
      rcases hor12 with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2 ▸ hS2
      · exact h1 ▸ hS1
    · right
      obtain ⟨h1, h2⟩ := horient (Or.inr (Or.inr hext.e6))
      subst L1' L2'
      obtain ⟨f, hf, hA, hq1, hsp, hb2, hq2, hO⟩ := hext
      obtain ⟨-, -, t, ht, -, hOeq, -⟩ :=
        hU4 G T M L V H B D L₂ n f hyp hf (hyp.isU4ExtTwo_of_orient h331 hR hbor
          (Or.inr ⟨rfl, rfl⟩) hA) hq1 hsp hb2 hq2 hO
      refine ⟨t, ht ▸ pow_orderOf_eq_one t, ?_, hOeq.le⟩
      have htO : t ∈ pCoreOf 2 (L₂ ⊔ sec52S M H) := by
        rw [hOeq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
      exact normalizer_le_normalizer_pCoreOf 2 L₂
        (sup_le Subgroup.le_normalizer hSN ((pCoreOf_le 2 _) htO))
  have hL₂K : L₂ = oTwoUpper H := by
    obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
    rcases hcase with ⟨hbend, hL₂K₁⟩ | ⟨hnb, hK₁K, P, hP, hL₂P⟩
    · subst K₁
      exact hyp.eq_oTwoUpper_of_bender h38 hF hU3 h510 h524 hK₁ hKeq hbend hS2
    · subst K₁
      exact (hrk2C G T M L V H B D L₂ n hyp hnb ⟨P, hP, hL₂P⟩ L1' L2' hor12 hlistC
        hsecond).elim
  subst hL₂K
  set S := sec52S M H with hSdef
  set K := oTwoUpper H with hKdef
  have hG2 := perfectCore_G2_eq h331 hR hF hF11 hbor hyp
  have hTS := pCoreOf_sup_T_eq hyp.toHyp5_1_8
  rcases hab with ⟨-, -, hS1, hS2'⟩ | hext
  ·
    have hSL : S ≤ L := by
      rcases hor12 with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1 ▸ hS1
      · exact h2 ▸ hS2'
    have hSK : S ≤ K := by
      rcases hor12 with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2 ▸ hS2'
      · exact h1 ▸ hS1
    have hBodd : Odd (Nat.card ↥(B ⊓ K)) :=
      Odd.of_dvd_nat hN.1.2.1 (Subgroup.card_dvd_of_le inf_le_left)
    have hBL : B ⊓ K ≤ Subgroup.normalizer (L : Set G) :=
      (inf_le_left.trans (hN.1.1.trans inf_le_left)).trans h.normal
    have hG1eq : sec52G1 M L H B K = L ⊔ (B ⊓ K) := by
      show L ⊔ S ⊔ (B ⊓ K) = L ⊔ (B ⊓ K)
      rw [sup_eq_left.mpr hSL]
    have hG2eq : sec52G2 M H D K = K ⊔ D := by
      show D ⊔ S ⊔ K = K ⊔ D
      apply le_antisymm
      · exact sup_le (sup_le le_sup_right (hSK.trans le_sup_left)) le_sup_left
      · exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
    refine ⟨rfl, hG2.symm, ?_, ?_, hyp.cases_of_listC h331 hR hF11 hbor h524 hor hnotL hSL
      hSK hor12 hlist, hTS, Or.inl ⟨hSL, hSK, by rw [sup_eq_left.mpr hSL],
        by rw [sup_eq_left.mpr hSK]⟩⟩
    · rw [hG1eq]
      exact pCoreOf_sup_of_odd hBL hBodd
    · rw [hG2eq]
      exact pCoreOf_sup_of_odd hyp.D_le hN.2.1.2.1
  ·
    obtain ⟨h1, h2⟩ := horient (Or.inr (Or.inr hext.e6))
    subst L1' L2'
    obtain ⟨f, hf, hA, hq1, hsp, hb2, hq2, hO⟩ := hext
    have hAα := hyp.isU4ExtTwo_of_orient h331 hR hbor (Or.inr ⟨rfl, rfl⟩) hA
    obtain ⟨hO1, hO2, t, ht, htO, hOeq, hC⟩ :=
      hU4 G T M L V H B D K n f hyp hf hAα hq1 hsp hb2 hq2 hO
    have hfn : 2 * f = n := hyp.eq_of_isL2Quot_L (by omega) hq2
    have h2n : 2 < n := by omega
    have hOm := F112R.isOmega4MinusBlock_of_type (by omega) hb2 hq2 hO
    refine ⟨rfl, hG2.symm, hO1, hO2, ?_, hTS, Or.inr ⟨f, hfn.symm, h2n, hAα, t, ht, htO, hOeq,
      hC⟩⟩
    unfold Cases5_2_6
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hfn.symm, h2n, Or.inr hAα, hOm, hq1,
      hsp⟩)))))

theorem stmt5_2_6_trC_holds
    (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (hF : RankOneListedFacts.{0})
    (hF11 : StmtF11_5_2) (hbor : Stmt5_2_6_borel) (h524 : Stmt5_2_4) (h510 : Stmt5_1_10)
    (h38 : Vol2Native.A38ForSQTKCat) (hU3 : FactU3Cover) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h512 : Stmt5_1_2) : Stmt5_2_6_trC :=
  have hsecC : Stmt5_2_6_secondC := stmt5_2_6_second_holdsC
  have hU4C : Stmt5_2_6_U4extC := stmt5_2_6_U4extC_of h331 hR hF hF11 hbor
  have hU4 : Stmt5_2_6_U4ext := stmt5_2_6_U4ext_of h331 hR hF hF11 hbor
  have hres : Stmt5_2_6_L2K_rank2_res := stmt5_2_6_L2K_rank2_res_of h331 hF hF11 hbor h524
  stmt5_2_6_trC_of h331 hR hF hF11 hbor h524 h510 h38 hU3 hC58 h317 h512 hsecC hU4C hU4
    (stmt5_2_6_L2K_rank2C_of h331 hF hF11 hbor h524 h510 h38 hU3 hC58 h317 h512 hU4 hsecC hU4C
      hres)

end CFSG.Quasithin.H13
