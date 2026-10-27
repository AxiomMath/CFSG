module

public import CFSG.Quasithin.Vol2.Ch9Sec2Swap
public import CFSG.Quasithin.Vol2.Ch9Sec2KStar

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem minParabolic_of_isHStar (h331 : Stmt3_3_1) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H) :
    MinParabolic H T (H ⊓ fsuM T L) ∧ SQTKGroup ↥H ∧ ¬ Group.IsSolvable ↥H ∧
      IsSylowTwoOf T (H ⊓ fsuM T L) := by
  have hInM : InM T (fsuM T L) := ⟨S.uniq.1.1, le_sup_right.trans S.uniq.1.2⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤ fsuM T L :=
    ((h331 G T S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke S.hyp.fsu.sylow).2 L
      S.hyp.fsu.maximal S.hyp.fsu.quasisimple).2.2.2.1
  have hTH : T ≤ H := hH.1.1
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.hyp.fsu.sylow
  have hU : IsUniqueMaxOver H T (H ⊓ fsuM T L) := by
    have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ hInM.2)
    rwa [hP] at this
  exact ⟨⟨isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH, hH.not_le_normalizer hNT, hU⟩,
    sqtkGroup_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian hH.1.2,
    fun hsol => absurd hn1 (not_lt.mpr (E1.solvable_nParam_le_one hsol)),
    isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow (le_inf hTH hInM.2)⟩

theorem exists_hall (hE22 : E2.E22StatementC) (h331 : Stmt3_3_1) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H) :
    ∃ B : Subgroup G, Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) := by
  have hInM : InM T (fsuM T L) := ⟨S.uniq.1.1, le_sup_right.trans S.uniq.1.2⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤ fsuM T L :=
    ((h331 G T S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke S.hyp.fsu.sylow).2 L
      S.hyp.fsu.maximal S.hyp.fsu.quasisimple).2.2.2.1
  obtain ⟨B, hB, -, -⟩ := Vol2.Ch11.SecB.derivedHallBorel_ofC hE22
    Vol2.Ch11.SecB.factBorelComm_holds G T (fsuM T L) H S.hyp.fsu.simple S.hyp.fsu.nonabelian
    S.hyp.fsu.qtke S.hyp.fsu.sylow hInM hNT hH hn1
  exact ⟨B, hB⟩

theorem le_two_of_isHStar
    (hE22 : E2.E22StatementC) (h4414 : Stmt4_4_14) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h122 : Vol2Native.Lemma122A) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four) (h63 : ASInputs.AS_E_6_3)
    (hH11 : Ch9InH11Plus) (h1 : zQ T I = fsuV T I) (h331 : Stmt3_3_1)
    (hF1 : FactBorelOddLarge) (hF2 : FactBenderCartanFrob) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H) : n ≤ 2 := by
  obtain ⟨K, _, _, _, e, ψ, hc⟩ := S.exists_isCoord
  obtain ⟨hmin, hSQ, hns, hTXs⟩ := S.minParabolic_of_isHStar h331 hH hn1
  obtain ⟨B, hB⟩ := S.exists_hall hE22 h331 hH hn1
  obtain ⟨hBL, hcyc, hBc, -, D, hD, hBD⟩ := S.hall_eq_cartan hE22 h4414 hC58 h317 h331 h122
    h37c h38c h37 h38 h39 h3228 hE610 h63 hH11 h1 hH hn1 hB
  have hnH := S.le_nParam_add_one h37 h38 h39 h3228 hE610 h63 hH11 h1 hH
  obtain ⟨Kc, -, hHK, hTK, hJ2, hBor, htype⟩ := KStar.exists_comp hE22 hF1 hmin hSQ hns
    inf_le_left hTXs.1 hTXs hn1 S.two_le hnH hB hBc
  suffices key : IsPSL 2 2 n ↥(E2.star (H ⊓ fsuM T L) H Kc) ∨
      IsSz n ↥(E2.star (H ⊓ fsuM T L) H Kc) → n ≤ 2 by
    rcases htype with h | h | ⟨hn, -⟩
    · exact key (Or.inl h)
    · exact key (Or.inr h)
    · omega
  intro htype'
  have : IsCyclic ↥B := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥B)
  have hbo : orderOf (g : G) = 2 ^ n - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hBc]
  obtain ⟨t, ht, htn, htB⟩ := S.exists_mem_normalizer_cartan hD hBD
  obtain ⟨j, hj⟩ := KStar.exists_conj_eq_pow hF2 inf_le_left hTXs.1 hTXs hHK hTK hJ2 hBor
    S.two_le htype' hB g.2 hbo hBc ht htB
  exact hc.le_two_of_conj h37 h38 h37c h38c h1 (hBL g.2)
    (S.le_centralizer_of_hall h37c h38c hC58 h317 h1 hH hB g.2) hbo ht htn hj

theorem eq_two
    (hE22 : E2.E22StatementC) (h4414 : Stmt4_4_14) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h122 : Vol2Native.Lemma122A) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four) (h63 : ASInputs.AS_E_6_3)
    (hH11 : Ch9InH11Plus) (h1 : zQ T I = fsuV T I) (h331 : Stmt3_3_1)
    (hF1 : FactBorelOddLarge) (hF2 : FactBenderCartanFrob) : n = 2 := by
  obtain ⟨H, hH⟩ := ((h331 G T S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke
    S.hyp.fsu.sylow).2 L S.hyp.fsu.maximal S.hyp.fsu.quasisimple).2.2.1
  by_contra hne
  have hn3 : 3 ≤ n := by have := S.two_le; omega
  have hnH := S.le_nParam_add_one h37 h38 h39 h3228 hE610 h63 hH11 h1 hH
  have hn1 : 1 < E1.nParam H := by
    by_contra h
    push Not at h
    have h2 : (n : ℕ∞) ≤ 2 := hnH.trans (by
      calc E1.nParam H + 1 ≤ 1 + 1 := add_le_add h le_rfl
        _ = 2 := one_add_one_eq_two)
    have h3 : n ≤ 2 := by exact_mod_cast h2
    omega
  have := S.le_two_of_isHStar hE22 h4414 hC58 h317 h122 h37c h38c h37 h38 h39 h3228 hE610 h63
    hH11 h1 h331 hF1 hF2 hH hn1
  omega

theorem nParam_le_two
    (hE22 : E2.E22StatementC) (h4414 : Stmt4_4_14) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h122 : Vol2Native.Lemma122A) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four) (h63 : ASInputs.AS_E_6_3)
    (hH11 : Ch9InH11Plus) (h1 : zQ T I = fsuV T I) (h331 : Stmt3_3_1)
    (hF1 : FactBorelOddLarge) (hF2 : FactBenderCartanFrob) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) : E1.nParam H ≤ 2 := by
  by_cases hn1 : 1 < E1.nParam H
  · have h := (S.exists_orderOf_eq hE22 h4414 hC58 h317 h331 h37c h38c h37 h38 h39 h3228 hE610
      h63 hH11 h1 hH hn1).1
    rw [S.eq_two hE22 h4414 hC58 h317 h122 h37c h38c h37 h38 h39 h3228 hE610 h63 hH11 h1 h331
      hF1 hF2] at h
    exact_mod_cast h
  · push Not at hn1
    exact hn1.trans (by norm_num)

end Setup

end CFSG.Quasithin.H13.Ch9
