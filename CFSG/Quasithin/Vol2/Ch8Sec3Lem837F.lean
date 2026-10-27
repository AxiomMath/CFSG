module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837E
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.EmptyFaithfulMultiple.Facts15420Proof
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837B
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

namespace Ch837

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_sup_of_le_sup {Gz Kz N M : Subgroup G} (hKz : Kz ≤ Gz)
    (hle : Gz ≤ Kz ⊔ (Gz ⊓ N)) (hNM : Gz ⊓ N ≤ M) : Gz = Kz ⊔ (M ⊓ Gz) :=
  le_antisymm (hle.trans (sup_le_sup_left (le_inf hNM inf_le_left) _)) (sup_le hKz inf_le_right)

omit [Finite G] in
theorem statedClassicalModel_psl25_of_psl24 {Q : Type} [Group Q]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSL 2 2 2) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel Q .PSL 2 5 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e4⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField _ 2 2 2 h
  obtain ⟨e54⟩ := CFSG.Walter.nonempty_psl2_five_mulEquiv_psl2_four
  exact CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv Q 5 1 (by norm_num)
    (e4.trans e54.symm)

end Ch837

open Ch837 in
theorem stmt8_3_7_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h3228 : Stmt3_2_2_eight) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h332 : Stmt3_3_2MTwo) (h326 : Stmt3_2_6C) (h3108 : Stmt3_2_10_eight)
    (h134 : EmptyFaithfulMultiple.Prop134E9He) (h734 : Stmt7_3_4) (h836 : Stmt8_3_6)
    (hOut : KG838Out) (hKG : KGRankOneOvergroups) (hL2N : Claim837L2N)
    (hYns : Claim837YNonsolv) : Stmt8_3_7 := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hyp.fsu.simple
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hXKz : ch83X T L z ≤ ch83Kz T L z := le_conjClosure _ _
  have hKzGz : ch83Kz T L z ≤ Subgroup.centralizer ({z} : Set G) := conjClosure_le fun h hh x hx =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hGzKz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (ch83Kz T L z : Set G) := le_normalizer_conjClosure _ _
  have hTX := le_normalizer_ch83X (L := L) hTz
  have hres : twoResidual (ch83X T L z) = ch83X T L z :=
    twoResidual_twoResidual (fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G))
  have hTGz : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)) :=
    isSylowTwoOf_of_le hyp.fsu.sylow hTz
  obtain ⟨φ, hO2, hXi, hrel, P, hP, hPc, hcyc⟩ := xi_data h37 h38 h326 hyp hV hrow hN hz2 hzV
  have hPne : P ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hPc
    omega
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    zpowers_le_pCoreOf hz2 (Subgroup.mem_centralizer_singleton_iff.mpr rfl) le_rfl
  have hPGz : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := fun h => by
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hsq : CFSG.SectionRank.IsSQTKCat ↥(Subgroup.centralizer ({z} : Set G)) := hK _ hPGz
  have hSQ : IsSQTKIn (Subgroup.centralizer ({z} : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hPGz
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38)
  have hNXM := inf_normalizer_ch83X_le h37 h38 h39 h326 h3108 h836 hYns hyp h731 hrow hV hN
    hz2 hzV
  have hGzM := not_centralizer_le_fsuM h37 h38 h39 h3228 hC58 h317 h332 hyp hz2 hzV
  have hOKz : pCoreOf 2 (ch83Kz T L z) ≤ Subgroup.normalizer (ch83X T L z : Set G) := by
    refine le_trans ?_ hTX
    refine le_trans ?_ (B6.pCoreOf_two_le_of_isSylowTwoOf hTGz)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKzGz)
      (hGzKz.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hfirst : (∀ g ∈ Subgroup.centralizer ({z} : Set G), ∃ m : ℕ, g ^ 2 ^ m ∈
      ch83Kz T L z ⊔ centralizerSection (Subgroup.centralizer ({z} : Set G)) (ch83Kz T L z)
        (pCoreOf 2 (ch83Kz T L z))) →
      Subgroup.centralizer ({z} : Set G) =
        ch83Kz T L z ⊔ (fsuM T L ⊓ Subgroup.centralizer ({z} : Set G)) := fun hpow =>
    eq_sup_of_le_sup hKzGz (le_sup_inf_normalizer hKzGz hGzKz hXKz hres hOKz hTGz hTX hpow) hNXM
  rcases h134 G _ T _ P hsq hPGz hTGz hXGz hXi hrel hP.le hP.isPGroup hPc with
    hNX | ⟨K, hKc, hq, hXK, hcases⟩
  ·
    exact absurd ((le_inf le_rfl hNX).trans hNXM) hGzM
  obtain ⟨horb, hcase⟩ := hA3 _ T K hSQ hTGz hKc
  have hinv : T ≤ Subgroup.normalizer (K : Set G) →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
        ch83X T L z ≤ K := by
    intro hTK
    refine ⟨fun g hg => ?_, hXK.trans (conjClosure_le fun g hg l hl =>
      (Subgroup.mem_normalizer_iff.mp (hTK hg) l).mp hl)⟩
    have hmem : conjByElt g K ∈ conjSubgroupsBy (Subgroup.centralizer ({z} : Set G)) K :=
      ⟨g, hg, rfl⟩
    rw [horb] at hmem
    obtain ⟨t, ht, hgt⟩ := hmem
    have h1 : conjByElt t K = K := A38.map_conj_eq_iff.mpr (hTK ht)
    have h2 : conjByElt g K = K := by rw [hgt]; exact h1
    exact A38.map_conj_eq_iff.mp h2
  rcases hcases with ⟨⟨t, htSN, htK, hPeq, -⟩, htype⟩ | ⟨hTK, htype⟩ | ⟨-, -, hcyc'⟩ |
      ⟨hTK, htype⟩ | ⟨hGK, he⟩
  ·
    rcases hcase with hnorm | ⟨t', ht'T, ht'N, hpair, -, -, -⟩
    · exact absurd (hnorm t htSN.1) htK
    have hY := Der6D.conjClosure_eq_sup_of_orbit (hTGz.1 ht'T) (horb.trans hpair)
    have hTKcl := Der6D.conjClosure_eq_sup_of_orbit ht'T hpair
    have hPK : P ⊓ K ≠ ⊥ := by
      intro h
      apply hPne
      rw [hPeq, h]
      simp [conjByElt]
    have hcenter : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
      rcases htype with ⟨n, -, hn'⟩ | ⟨q, -, -, hq'⟩
      · exact EmptyFaithfulMultiple.facts15420_centerPSL _ 2 2 n hn'
      · exact EmptyFaithfulMultiple.facts15420_centerPSL _ 2 q 1 hq'
    have hKzeq : ch83Kz T L z = K ⊔ conjByElt t' K :=
      Der6D.conjClosure_eq_sup_of_pair hKc hTGz.1 ht'T hY hXK hq hcenter hP.le hP.isPGroup hPK
    have hK'c : conjByElt t' K ∈ cComp (Subgroup.centralizer ({z} : Set G)) := by
      rw [conjByElt_eq_conjugate]
      exact conjSub_mem_cComp_of_mem hKc (by rw [inv_inv]; exact hTGz.1 ht'T)
    have hne : K ≠ conjByElt t' K := fun h => ht'N (A38.map_conj_eq_iff.mp h.symm)
    have hcommKK' := (Vol2Native.lemma_1_2_1_two hK h37 hPGz hKc hK'c hne).1
    have hperm : ∀ g ∈ Subgroup.centralizer ({z} : Set G),
        (conjByElt g K = K ∨ conjByElt g K = conjByElt t' K) ∧
          (conjByElt g (conjByElt t' K) = K ∨
            conjByElt g (conjByElt t' K) = conjByElt t' K) := by
      intro g hg
      have hmem : ∀ y ∈ Subgroup.centralizer ({z} : Set G),
          conjByElt y K = K ∨ conjByElt y K = conjByElt t' K := by
        intro y hy
        have h1 : conjByElt y K ∈ conjSubgroupsBy (Subgroup.centralizer ({z} : Set G)) K :=
          ⟨y, hy, rfl⟩
        rw [horb.trans hpair] at h1
        exact h1
      have e : conjByElt g (conjByElt t' K) = conjByElt (g * t') K := by
        unfold conjByElt
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      exact ⟨hmem g hg, e ▸ hmem _ (Subgroup.mul_mem _ hg (hTGz.1 ht'T))⟩
    have hcase_i : ∀ p : ℕ, p.Prime →
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 p 1 →
        Subgroup.centralizer ({z} : Set G) =
            ch83Kz T L z ⊔ (fsuM T L ⊓ Subgroup.centralizer ({z} : Set G)) ∧
          ((∃ (K : Subgroup G) (s : G), s ∈ T ∧ s ∉ Subgroup.normalizer (K : Set G) ∧
              quasithinIsCComponent K (Subgroup.centralizer ({z} : Set G)) ∧
              ch83Kz T L z = K ⊔ CFSG.conjugate K s ∧
              ∃ p : ℕ, p.Prime ∧
                CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 p 1) ∨
            CFSG.Assembly.LowTwoRank.StatedClassicalModel
              (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z)) .PSL 4 2 1 ∨
            CFSG.Assembly.LowTwoRank.StatedClassicalModel
              (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z)) .PSL 5 2 1 ∨
            Nonempty (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z) ≃*
              CFSG.Blueprint.NativeSporadic.Carrier .He)) := by
      intro p hp hmod
      obtain ⟨eK⟩ := nonempty_quot_conjugate_equiv K t'⁻¹
      have hmod' : CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥(conjByElt t' K) ⧸ CFSG.pCore 2 ↥(conjByElt t' K)) .PSL 2 p 1 := by
        rw [conjByElt_eq_conjugate]
        exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv eK.symm hmod
      have hpow := pow_mem_of_pair (le_of_mem_cComp hKc) (le_of_mem_cComp hK'c)
        (hKzeq ▸ hGzKz) hcommKK' (hOut.1 _ p hmod) (hOut.1 _ p hmod')
        (fun g hg => sq_mem_normalizer_of_pair hne hperm hg)
      refine ⟨hfirst (hKzeq ▸ hpow), Or.inl ⟨K, t'⁻¹, T.inv_mem ht'T, fun h => ht'N ?_, hKc,
        hKzeq.trans (by rw [conjByElt_eq_conjugate]), p, hp, hmod⟩⟩
      simpa using Subgroup.inv_mem _ h
    rcases htype with ⟨n, hn2, hn'⟩ | ⟨q, hq', -, hmod⟩
    ·
      have hn1 : 1 ≤ n := hn'.1.2.1
      rcases (by obtain ⟨k, rfl⟩ := hn2; omega : n = 2 ∨ 4 ≤ n) with rfl | hn4
      · exact hcase_i 5 Nat.prime_five (statedClassicalModel_psl25_of_psl24 hn')
      · exact (false_of_l2_four h37 h38 h326 h734 h836 hKG hL2N hyp h731 hrow hV hN hz2 hzV φ
          hrel ht'T ht'N hKc hKzeq hTKcl hn2 hn4 hn').elim
    · exact hcase_i q hq' hmod
  ·
    obtain ⟨hGzK, hXK'⟩ := hinv hTK
    exact (false_of_l33_m11 hyp.fsu.sylow hTz le_sup_right hGzK (by rw [hO2]; exact hXK') φ
      (by rcases htype with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h))).elim
  ·
    exact absurd hcyc' hcyc
  ·
    obtain ⟨hGzK, hXK'⟩ := hinv hTK
    rcases htype with hM | h42 | h52
    · exact (false_of_l33_m11 hyp.fsu.sylow hTz le_sup_right hGzK (by rw [hO2]; exact hXK') φ
        (Or.inr (Or.inr hM))).elim
    · have hcenter := EmptyFaithfulMultiple.facts15420_centerPSL _ 4 2 1 h42
      have hKzK : ch83Kz T L z = K :=
        Der6D.conjClosure_eq_of_invariant hKc hGzK hXK' hq hcenter hP.le hP.isPGroup hPne
      have hpow := pow_mem_of_outIsTwoGroup (le_of_mem_cComp hKc) hGzK (hOut.2.1 _ h42)
      rw [← hKzK] at hpow h42
      exact ⟨hfirst hpow, Or.inr (Or.inl h42)⟩
    · have hcenter := EmptyFaithfulMultiple.facts15420_centerPSL _ 5 2 1 h52
      have hKzK : ch83Kz T L z = K :=
        Der6D.conjClosure_eq_of_invariant hKc hGzK hXK' hq hcenter hP.le hP.isPGroup hPne
      have hpow := pow_mem_of_outIsTwoGroup (le_of_mem_cComp hKc) hGzK (hOut.2.2.1 _ h52)
      rw [← hKzK] at hpow h52
      exact ⟨hfirst hpow, Or.inr (Or.inr (Or.inl h52))⟩
  ·
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTz.trans hGK
    have hXK' : ch83X T L z ≤ K := hXK.trans (conjClosure_le fun g hg l hl =>
      (Subgroup.mem_normalizer_iff.mp (hTK hg) l).mp hl)
    obtain ⟨eHe⟩ := he
    have hcenter := Ch838.center_eq_bot_of_he eHe
    have hKzK : ch83Kz T L z = K :=
      Der6D.conjClosure_eq_of_invariant hKc hGK hXK' hq hcenter hP.le hP.isPGroup hPne
    have hpow := pow_mem_of_outIsTwoGroup (le_of_mem_cComp hKc) hGK (hOut.2.2.2 _ ⟨eHe⟩)
    have he' : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) :=
      ⟨eHe⟩
    rw [← hKzK] at hpow he'
    exact ⟨hfirst hpow, Or.inr (Or.inr (Or.inr he'))⟩

end CFSG.Quasithin.H13
