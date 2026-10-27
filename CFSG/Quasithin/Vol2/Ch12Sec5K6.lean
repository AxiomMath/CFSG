module

public import CFSG.Quasithin.Vol2.Ch12Sec5Six
public import CFSG.Quasithin.Vol2.Ch12Sec5FinA
public import CFSG.Quasithin.Vol2.Ch12Sec5L9a
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3K1
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Irr
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12
public import CFSG.Quasithin.EmptyFaithful.S153EB6D
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125
open scoped IsMulCommutative
open CFSG.RankThree.GroupTheory

namespace S125K6

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_li {T L W : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) : T ≤ Subgroup.normalizer (li L W : Set G) :=
  fun _ ht => SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hTL ht, Subgroup.le_normalizer (hTW ht)⟩)

theorem commutator_li (L W : Subgroup G) : ⁅li L W, li L W⁆ = li L W := by
  have hP := (CFSG.perfect_residual_characterization
    (G := ↥(L ⊓ Subgroup.normalizer (W : Set G)))).2.2.1
  rw [Subgroup.isPerfect_iff] at hP
  rw [li, CFSG.inSubgroup, ← Subgroup.map_commutator, hP]

omit [Finite G] in
theorem li_le (L W : Subgroup G) : li L W ≤ L :=
  (Subgroup.map_subtype_le _).trans inf_le_left

omit [Finite G] in
theorem li_le_normalizer (L W : Subgroup G) : li L W ≤ Subgroup.normalizer (W : Set G) :=
  (Subgroup.map_subtype_le _).trans inf_le_right

variable {T L V : Subgroup G}

theorem T_le_normalizer_l6 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    T ≤ Subgroup.normalizer (li L F.V6 : Set G) :=
  le_normalizer_li hH.hyp.normalizes (S125L2G.T_le_V F (S125Ex.Facts125.of h1222 hH).T_le).2.2.2

theorem l6_quot_equiv (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    Nonempty (↥(li L F.V6) ⧸ CFSG.pCore 2 ↥(li L F.V6) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hTL₆ := T_le_normalizer_l6 h1222 F hH
  have hXV : li L F.V6 ≤ Subgroup.normalizer (V : Set G) := (li_le L _).trans hf.normalizes
  have hYV : ri T L F.V6 ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le hXV hf.T_le)
  have hC : IsPGroup 2 ↥(li L F.V6 ⊓ Subgroup.centralizer (V : Set G)) :=
    (S125Tr2.isPGroup_centralizer hH hf).to_le
      (inf_le_inf_right _ ((li_le L _).trans le_sup_left))
  have hOY : pCoreOf 2 (li L F.V6) ≤ ri T L F.V6 :=
    E1.ThinA5.pCoreOf_le_pCoreOf le_sup_left (sup_le Subgroup.le_normalizer hTL₆)
  exact S125Fin.quot_pCore_equiv_of_quotSL hXV hYV hC
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hOY
    (lemma12_5_2_of h1222 G T L V F hH).2.2.2.2.2.1

theorem l6_mem_lFamily (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    li L F.V6 ∈ lFamily T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := l6_quot_equiv h1222 F hH
  have hTL₆ := T_le_normalizer_l6 h1222 F hH
  rw [lFamily, Set.mem_ofPred_eq]
  refine mem_cComp_of_quasisimple_quotient (fun N _ hN => ?_)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl_zmod_two (by omega)).1)
    (A3.subnormal_of_normal le_sup_left ?_)
  · have : Group.IsPerfect ↥(li L F.V6) := Subgroup.isPerfect_iff.mpr (commutator_li L _)
    by_contra hne
    have : Nontrivial (↥(li L F.V6) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    have : Group.IsNilpotent (↥(li L F.V6) ⧸ N) := hN.isNilpotent
    exact Group.IsPerfect.not_isNilpotent (↥(li L F.V6) ⧸ N) ‹_›
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer hTL₆

omit [Finite G] in
theorem card_V6 (F : Frame125 T L V) : Nat.card ↥F.V6 = 2 ^ 6 := by
  rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← S125L9a.card_V6_sub F]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv.symm

theorem false_of_list
    (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) {K : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (F.V6 : Set G)) (hLK : li L F.V6 ≤ K)
    (hl : IsList1293Two (↥K ⧸ CFSG.pCore 2 ↥K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  obtain ⟨-, -, -, -, ⟨hcomm, hext⟩, -⟩ := (lemma12_5_2_of h1222 G T L V F hH).2.2.2
  have := hcomm
  have hV6V : F.V6 ≤ V := Subgroup.map_subtype_le _
  have hcard := card_V6 F
  have hV6ne : F.V6 ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hirrL : IsIrreducibleUnder (li L F.V6) F.V6 :=
    ⟨hV6ne, fun W hW hLW => Ch4.T4213N.eq_bot_or_eq_of_slExteriorTwo hext hW hLW⟩
  have hirrK : IsIrreducibleUnder K F.V6 := ⟨hV6ne, fun W hW hKW => hirrL.2 W hW (hLK.trans hKW)⟩
  have hL₆N : li L F.V6 ≤ Subgroup.normalizer (F.V6 : Set G) := hLK.trans hKN
  have hirrLa := S125Ex.irr_autOn hL₆N hirrL
  have hirrKa := S125Ex.irr_autOn hKN hirrK
  have h2 : ∀ v : ↥F.V6, v ^ 2 = 1 := fun v => Subtype.ext (hf.sq v (hV6V v.2))
  have hO2a : pCoreOf 2 (autOn K F.V6) = ⊥ :=
    S153EB6.pCoreOf_two_eq_bot_of_irr h2 (A4.autOn_mono hLK) hirrLa
  have hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (F.V6 : Set G) :=
    Lem12.pCoreOf_le_centralizer_of_autOn hKN hO2a
  have hnc : ¬ K ≤ Subgroup.centralizer (F.V6 : Set G) := by
    intro hKC
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ F.V6, v ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hV6ne (eq_bot_iff.mpr fun v hv => (Subgroup.mem_bot).mpr (hcon v hv))
    have hW : Subgroup.zpowers v ≤ F.V6 := Subgroup.zpowers_le.mpr hv
    rcases hirrL.2 _ hW ((hLK.trans hKC).trans ((Subgroup.centralizer_le hW).trans
        (Subgroup.centralizer_le_normalizer _))) with h | h
    · exact hv1 (by rw [← Subgroup.mem_bot, ← h]; exact Subgroup.mem_zpowers v)
    · have h1 : Nat.card ↥(Subgroup.zpowers v) = 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (hf.sq v (hV6V hv)) hv1
      rw [h, hcard] at h1
      norm_num at h1
  have hA : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) →
      Nonempty (↥(autOn K F.V6) ≃* (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    fun hs => nonempty_autOn_mulEquiv_quotient hKN hO2 hs hnc
  have h11 : ¬ 11 ∣ Nat.card ↥(autOn K F.V6) := by
    intro hd
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 11 hd
    exact S125Six.false_of_orderOf_eleven hcard (a := (a : MulAut ↥F.V6))
      (by rw [Subgroup.orderOf_coe, ha])
  rcases hl with hS | hM | hJ
  · obtain ⟨eS⟩ := hS
    have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
      have := (isSimpleGroup_sl_zmod_two (m := 5) (by norm_num)).1
      exact eS.isSimpleGroup
    obtain ⟨eA⟩ := hA hs
    exact S125Six.false_of_mulEquiv_sl5 h2 hcard (eA.trans eS) hirrKa
  · obtain ⟨eM⟩ := hM
    have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
      have := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
      exact @MulEquiv.isSimpleGroup _ _ _ _ this eM
    obtain ⟨eA⟩ := hA hs
    apply h11
    rw [Nat.card_congr (eA.trans eM).toEquiv, CFSG.Sporadic.Mathieu.card_M24]
    norm_num
  · obtain ⟨eJ⟩ := hJ
    have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
      have := CFSG.Sporadic.J4.isSimpleGroup_J4
      exact @MulEquiv.isSimpleGroup _ _ _ _ this eJ
    obtain ⟨eA⟩ := hA hs
    apply h11
    rw [Nat.card_congr (eA.trans eJ).toEquiv, CFSG.Sporadic.J4.card_J4]
    norm_num

theorem l6_cComp
    (h1222 : Stmt12_2_2) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    quasithinIsCComponent (li L F.V6) (Subgroup.normalizer (F.V6 : Set G)) ∧
      Subgroup.normalizer (F.V6 : Set G) ≤ Subgroup.normalizer (li L F.V6 : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  have hTV₆ : T ≤ Subgroup.normalizer (F.V6 : Set G) := (S125L2G.T_le_V F hf.T_le).2.2.2
  have hTL₆ := T_le_normalizer_l6 h1222 F hH
  have hL₆G₆ : li L F.V6 ≤ Subgroup.normalizer (F.V6 : Set G) := li_le_normalizer L _
  have hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (F.V6 : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTV₆
  have hV₆V : F.V6 ≤ V := Subgroup.map_subtype_le _
  have hV₆2 : IsPGroup 2 ↥F.V6 := by
    refine IsPGroup.of_card (n := 6) ?_
    exact card_V6 F
  have hO : pCoreOf 2 (Subgroup.normalizer (F.V6 : Set G)) ≠ ⊥ := by
    intro hb
    have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 F.V6 hV₆2
    rw [hb, le_bot_iff] at h1
    have h2 := card_V6 F
    rw [h1, Subgroup.card_bot] at h2
    norm_num at h2
  have hB := l6_mem_lFamily h1222 F hH
  obtain ⟨K, hK, hLK⟩ := lemma_1_2_4_exists hyp.qtke hyp.simple hyp.nonabelian h37 h39 hO hS
    hL₆G₆ hB
  have hKc : K ∈ cComp (Subgroup.normalizer (F.V6 : Set G)) := hK
  have hKG₆ : K ≤ Subgroup.normalizer (F.V6 : Set G) := le_of_mem_cComp hKc
  have hKn : Subgroup.normalizer (F.V6 : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    have hn := lemma_1_2_4_normal hyp.qtke hyp.simple hyp.nonabelian h37 h38 hO hS hB hLK hK
      hTL₆
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (A3.subnormal_le hK.2.2.1)).1 hn
  suffices hKL : li L F.V6 = K by
    rw [hKL]
    exact ⟨hK, hKn⟩
  obtain ⟨e₆⟩ := l6_quot_equiv h1222 F hH
  obtain ⟨eB⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hL₆G₆
  have hD := data1293_of (B := modO2Image (Subgroup.normalizer (F.V6 : Set G)) (li L F.V6))
    (k := 4) (Or.inr rfl) (eB.symm.trans e₆)
  have hBK : modO2Image (Subgroup.normalizer (F.V6 : Set G)) (li L F.V6) ≤
      modO2Image (Subgroup.normalizer (F.V6 : Set G)) K :=
    Subgroup.map_mono (fun x hx => hLK hx)
  obtain ⟨eK⟩ := modO2_mulEquiv hKc
  rcases lemma_1_2_4_list hyp.qtke hyp.simple hyp.nonabelian h312 hO hS hL₆G₆ hB hKc hLK with
    heq | hcase | hnq
  ·
    refine L1293.eq_of_modO2Image_eq hLK hKG₆ (perfect_of_mem_cComp hKc) ?_ heq
    have hP : pCoreOf 2 (Subgroup.normalizer (F.V6 : Set G)) ≤ T :=
      pCoreOf_two_le_of_isSylowTwoOf hS
    exact L1295.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer (hP.trans hTL₆)))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _) le_sup_right le_rfl
  ·
    exfalso
    have hDyn : ¬ DynkinPair1293 (modO2Image (Subgroup.normalizer (F.V6 : Set G)) (li L F.V6))
        (modO2Image (Subgroup.normalizer (F.V6 : Set G)) K) := by
      have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 :=
        card_sl_four_zmod_two
      have hdvd := hD.dvd_card
      rw [hc] at hdvd
      rintro (⟨hb, -⟩ | ⟨hb, -⟩)
      · have h2 := Vol2.Ch11.SecA.two_mul_card_of_isPSL_two (by norm_num) (by norm_num) hb
        have h3 : Nat.card ↥(modO2Image (Subgroup.normalizer (F.V6 : Set G)) (li L F.V6)) =
            168 := by omega
        rw [h3] at hdvd
        norm_num at hdvd
      · have h2 := Vol2.Ch11.SecA.card_of_isSL2 (by norm_num) hb
        rw [h2] at hdvd
        norm_num at hdvd
    rcases hD.list_of_case hDyn hcase with h | ⟨h43, -⟩
    · exact false_of_list h1222 F hH hKG₆ hLK (h.of_mulEquiv eK.symm)
    · exact absurd h43 (by norm_num)
  ·
    exfalso
    have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hO
    obtain ⟨h43, -⟩ := hD.list_of_nonquasi hBK (h36 _ hQ _ (modO2Image_mem_cComp hKc)) hnq
    exact absurd h43 (by norm_num)

end S125K6

end CFSG.Quasithin.H13
