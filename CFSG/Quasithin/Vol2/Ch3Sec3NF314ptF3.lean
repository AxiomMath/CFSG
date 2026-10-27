module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptF3a
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptF3b
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptF2
public import CFSG.Quasithin.MS93.S45C1

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

theorem f3_modO2_mono {G : Type} [Group G] {H L L' : Subgroup G} (h : L ≤ L') :
    CFSG.Quasithin.modO2Image H L ≤ CFSG.Quasithin.modO2Image H L' := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx)), rfl⟩

theorem f3_final {G : Type} [Group G] [Finite G] {G1 TL J L2 B : Subgroup G} {q : ℕ}
    (hA : LeafA312) (h312 : CFSG.QuasithinUnique.Vol2Native.A312ForSQTKCat)
    (hLS : LocalSQTK G) (hq : q.Prime) (hq24 : q % 24 = 11 ∨ q % 24 = 13)
    (hpc : pCoreOf 2 G1 ≠ ⊥) (hS : CFSG.QuasithinUnique.IsSylowTwoOf TL G1)
    (hL2G1 : L2 ≤ G1) (hloc2 : CFSG.Open.quasithinIsLocal TL L2)
    (hPSL2 : IsPSL 3 2 1 (↥L2 ⧸ CFSG.pCore 2 ↥L2))
    (hBG1 : B ≤ G1) (hlocB : CFSG.Open.quasithinIsLocal TL B)
    (hPSLB : IsPSL 2 q 1 (↥B ⧸ CFSG.pCore 2 ↥B))
    (hJc : J ∈ cComp G1) (hL2J : L2 ≤ J) (hBJ : B ≤ J) : False := by
  have hd1 := CFSG.QuasithinUnique.Vol2Native.lemma_1_2_4_list hLS h312 hpc hS hL2G1
    (CFSG.Quasithin.mem_lFamily_of_isLocal hloc2) hJc hL2J
  have hd2 := CFSG.QuasithinUnique.Vol2Native.lemma_1_2_4_list hLS h312 hpc hS hBG1
    (CFSG.Quasithin.mem_lFamily_of_isLocal hlocB) hJc hBJ
  exact hA (↥G1 ⧸ CFSG.pCore 2 ↥G1) (CFSG.Quasithin.modO2Image G1 L2)
    (CFSG.Quasithin.modO2Image G1 B) (CFSG.Quasithin.modO2Image G1 J) q hq hq24
    (f3_isPSL_modO2 hL2G1 hPSL2) (f3_isPSL_modO2 hBG1 hPSLB)
    (f3_modO2_mono hL2J) (f3_modO2_mono hBJ) hd1 hd2

theorem leafF3_holds (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h312 : CFSG.QuasithinUnique.Vol2Native.A312ForSQTKCat) (hA : LeafA312) : LeafF3 := by
  intro G _ _ T M L D H K TL L2 e F hloc _hTLN hPSL hY2 hnot
  have c : NFConfig G T M L D H K := F.nf
  haveI : IsSimpleGroup G := c.hyp.simple
  have hLS : LocalSQTK G := (qtkeCore_of_cat c.hyp.nonabelian c.hyp.qtke).1
  obtain ⟨q, hq, hq24, hmodel⟩ := c.model
  have hpc : pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) ≠ ⊥ :=
    (f2_twoLocal_centralizer F.e_sq F.e_ne).2
  have hL2G1 : L2 ≤ Subgroup.centralizer ({e} : Set G) := F.L2_e
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf TL (Subgroup.centralizer ({e} : Set G)) :=
    f3_sylow_TL c.hyp.sylow F.TL_le F.T_e F.TL_idx F.e_T F.e_ne F.e_sq hnot
  have hidx : TL.relIndex TL ≤ 2 := by
    rw [Subgroup.relIndex_self]; norm_num
  obtain ⟨t', ht'T, -, hK'H, hKK', hK₀eq, -⟩ :=
    CFSG.Quasithin.H13.NFConfig.exists_pair c h37 h38
  have hKsub : K ≤ conjClosure K T := by rw [hK₀eq]; exact le_sup_left
  have hK'sub : K.map (MulAut.conj t').toMonoidHom ≤ conjClosure K T := by
    rw [hK₀eq]; exact le_sup_right
  have hKG1 : K ≤ Subgroup.centralizer ({e} : Set G) := hKsub.trans F.K0_e
  have hK'G1 : K.map (MulAut.conj t').toMonoidHom ≤ Subgroup.centralizer ({e} : Set G) :=
    hK'sub.trans F.K0_e
  have hlocK : CFSG.Open.quasithinIsLocal TL K :=
    f2_isLocal_TL c.hyp.sylow F.TL_le F.T_e F.e_T F.e_ne F.e_sq F.K0_e
      (le_normalizer_conjClosure K T) hKsub (cComp_of_isLocal c.K_isLocal)
  have hloc'T : CFSG.Open.quasithinIsLocal T (K.map (MulAut.conj t').toMonoidHom) :=
    isLocal_of_mem_cComp_of_sylow c.isSylowTwoOf_H₀ c.O hK'H
  have hlocK' : CFSG.Open.quasithinIsLocal TL (K.map (MulAut.conj t').toMonoidHom) :=
    f2_isLocal_TL c.hyp.sylow F.TL_le F.T_e F.e_T F.e_ne F.e_sq F.K0_e
      (le_normalizer_conjClosure K T) hK'sub (cComp_of_isLocal hloc'T)
  obtain ⟨J_K, ⟨hJKc, hKJK⟩, -⟩ :=
    CFSG.QuasithinUnique.Vol2Native.lemma_1_2_5 hLS h37 h39 hpc hS le_rfl hidx hlocK hKG1
  obtain ⟨J_K', ⟨hJK'c, hK'JK'⟩, -⟩ :=
    CFSG.QuasithinUnique.Vol2Native.lemma_1_2_5 hLS h37 h39 hpc hS le_rfl hidx hlocK' hK'G1
  obtain ⟨J_L, ⟨hJLc, hL2JL⟩, -⟩ :=
    CFSG.QuasithinUnique.Vol2Native.lemma_1_2_5 hLS h37 h39 hpc hS le_rfl hidx hloc hL2G1
  have hdich : J_L = J_K ∨ J_L = J_K' := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hne1, hne2⟩ := hcon
    have hp1 := CFSG.QuasithinUnique.Vol2Native.lemma_1_2_1_two hLS h37 hpc hJKc hJLc
      (Ne.symm hne1)
    have hp2 := CFSG.QuasithinUnique.Vol2Native.lemma_1_2_1_two hLS h37 hpc hJK'c hJLc
      (Ne.symm hne2)
    have hKL2 : ⁅K, L2⁆ ≤ pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) :=
      (Subgroup.commutator_mono hKJK hL2JL).trans (hp1.1.trans hp1.2)
    have hK'L2 : ⁅K.map (MulAut.conj t').toMonoidHom, L2⁆ ≤
        pCoreOf 2 (Subgroup.centralizer ({e} : Set G)) :=
      (Subgroup.commutator_mono hK'JK' hL2JL).trans (hp2.1.trans hp2.2)
    apply hY2
    rw [hK₀eq]
    exact CFSG.Quasithin.MS93.S45.commutator_sup_left_le
      (fun x hx => (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hKG1 hx)))
      (fun x hx => (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hK'G1 hx)))
      hKL2 hK'L2
  rcases hdich with hJ | hJ
  · rw [hJ] at hL2JL
    exact f3_final hA h312 hLS hq hq24 hpc hS hL2G1 hloc hPSL hKG1 hlocK hmodel hJKc hL2JL hKJK
  · rw [hJ] at hL2JL
    exact f3_final hA h312 hLS hq hq24 hpc hS hL2G1 hloc hPSL hK'G1 hlocK'
      (f3_isPSL_conj K t' hmodel) hJK'c hL2JL hK'JK'

end CFSG.Quasithin.H13.NF314pt
