module

public import CFSG.Quasithin.H13.A5S136ab6
public import CFSG.Quasithin.H13.A5S136ab7
public import CFSG.Quasithin.H13.A5S136abR
public import CFSG.Quasithin.Vol2.F134Orders

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Assembly.LowTwoRank
open CFSG.Blueprint CFSG.SectionRank

namespace ConfAB

theorem lieZCentList_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : LieZCentList Y) : LieZCentList X := by
  obtain ⟨f, h⟩ := h
  refine ⟨f, ?_⟩
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl ⟨h.1, statedClassicalModel_of_mulEquiv e h.2⟩
  · exact Or.inr (Or.inl ⟨h.1, statedClassicalModel_of_mulEquiv e h.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h.1, statedClassicalModel_of_mulEquiv e h.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, chevalleyExceptionalModel_of_mulEquiv e h.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,
      chevalleyExceptionalModel_of_mulEquiv e h.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1,
      reeTitsModel_of_mulEquiv e h.2.2⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, h.2.1,
      suzukiModel_of_mulEquiv e h.2.2⟩)))))

theorem center_eq_bot_of_simple {X : Type*} [Group X] (hq : CFSG.IsQuasisimple X)
    (hs : IsSimpleGroup X) : Subgroup.center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, h]
    exact Subgroup.mem_top _

theorem three_dvd_or_isSz_of_a38Types {X : Type} [Group X]
    (h : A38Types X) : 3 ∣ Nat.card X ∨ ∃ n, IsSz n X := by
  rcases h with ⟨n, hn⟩ | hSz | ⟨⟨e⟩⟩ | ⟨p, -, -, hp⟩
  · exact Or.inl (F134.three_dvd_card_of_statedPSL_two hn)
  · exact Or.inr hSz
  · left
    rw [Nat.card_congr e.toEquiv,
      show Nat.card (NativeSporadic.Carrier .J1) = _ from CFSG.Sporadic.J1.card_J1]
    norm_num
  · exact Or.inl (F134.three_dvd_card_of_statedPSL_two hp)

theorem one_lt_pRank_of_psp {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : StatedClassicalModel X .PSp 2 2 f) : 1 < CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  have h2 := Vol2Native.EvenWit.two_le_pRank_three_psp (K := K) (n := 2) le_rfl
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  omega

end ConfAB

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem Lv_inner_of_rank (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hEven : Ch1.EvenLieAutInner) (hF3 : FactLieZCentPGL3) (hF6 : FactL3SylowCenterCyclic)
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hr : 1 < CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)))
    (hSQ : Ch1.SQTKCharTwoLie (↥K ⧸ CFSG.pCore 2 ↥K)) (hinner : Ch1.InducesInner S.z K) :
    ∀ y ∈ S.Lv, ∀ hyN : y ∈ Subgroup.normalizer (K : Set G),
      ∃ k : ↥K ⧸ CFSG.pCore 2 ↥K, ConfAB.indHom K (MulEquiv.refl _) ⟨y, hyN⟩ = MulAut.conj k := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have h3 := ConfAB.three_dvd_card_of_pRank hr
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hK.1] at h2
  by_cases hc2 : A318Case2 (starImage 3 (K.subgroupOf Gv))
  · obtain ⟨X, Q, y₀, hy₀Lv, hconf⟩ := S.exists_conf1366_Lv h1222 h517 h37 h38 hK hinner
    have hy₀N : y₀ ∈ Subgroup.normalizer (K : Set G) := hconf.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact S.inner_of_mem_Lv_of_odd (S.Lv_le_normalizer_of_mem_cComp h1222 h517 h37 h38 hKc) _
      (S.inner_all_of_case2 h1222 h517 hF3 hF6 hEven h38 hK hq hZ h3 hr hSQ hy₀Lv hconf hc2
        hy₀N)
  · intro y hy hyN
    rcases S.inner_or_case2 hF318 h36 h38 hK hq hZ h3 hr hy hyN with h | h
    · exact h
    · exact absurd h hc2

theorem false_of_lie_simple
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hEven : Ch1.EvenLieAutInner) (hF1 : FactLieZCent) (hF2 : FactLieOutAbelian)
    (hF3 : FactLieZCentPGL3) (hF6 : FactL3SylowCenterCyclic) (h122 : Vol2Native.Lemma122A)
    (hSz : Elim1366SzPair) (hab : CFSG.Open.IsElemAbelian 2 (conjClosure V S.G1))
    {K : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hSQ : Ch1.SQTKCharTwoLie (↥K ⧸ CFSG.pCore 2 ↥K))
    (hL : LieZCentList (↥K ⧸ CFSG.pCore 2 ↥K))
    (hsimp : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥K) ∨ 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K))
    (hinner : Ch1.InducesInner S.z K) : False := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hmain := fun h3 => S.false_of_lieZCent h1222 h517 hF318 h36 h37 h38 hEven hF1 hF2 hF3 hF6
    h122 hK hq hZ hSQ hL h3 hinner
  by_cases hn : (K.subgroupOf Gv).Normal
  · exact hmain (Or.inl hn)
  by_cases h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)
  · exact hmain (Or.inr h3)
  have : IsSimpleGroup G := S.h13.simple
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hK.1] at h2
  have hcore := qtkeCore_of_cat S.h13.nonabelian S.h13.qtke
  rcases Vol2Native.lemma_1_2_1_three hcore.1 h37 h38 S.pCoreOf_Gv_ne_bot' hKc with hn' | ⟨-, ht⟩
  · exact hn hn'
  rcases ConfAB.three_dvd_or_isSz_of_a38Types ht with h3' | ⟨n, hSzn⟩
  · exact h3 h3'
  rcases hsimp with ⟨⟨ψ₀⟩⟩ | h3'
  · exact hSz G T L V S hab K hK hn ⟨n, suzukiModel_of_mulEquiv ψ₀.symm hSzn⟩ hinner
  · exact h3 h3'

end Setting

theorem elim1366AB_of
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7)
    (h1336 : Input1336) (hF318 : A318Facts) (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hKF : KnownFacts15122Types)
    (hEven : Ch1.EvenLieAutInner) (hD4 : KG68.TrialityTwoSylowCenterCyclic)
    (hTits : KG68.TitsSylowCenterCyclic) (hF1 : FactLieZCent) (hF2 : FactLieOutAbelian)
    (hF3 : FactLieZCentPGL3) (hF6 : FactL3SylowCenterCyclic) (h122 : Vol2Native.Lemma122A)
    (hSp4 : Elim1366Sp4) (hSz : Elim1366SzPair) : Elim1366AB := by
  intro G _ _ T L V S hab K hK hcase
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hKG : K ≤ Gv := hK.1
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hKG)).1 hK.2.1
  have hlie := fun hinner => S.false_of_lie_simple h1222 h517 hF318 h36 h37 h38 hEven hF1 hF2
    hF3 hF6 h122 hSz hab hK (K := K) (hinner := hinner)
  rcases hcase with ⟨hsimp, hLie, hinner⟩ | ⟨hZne, hZO, hL34, hinner⟩
  ·
    have hO2 := ConfAB.pCore_two_eq_bot_of_simple hqs hsimp
    let ψ₀ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
    have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ₀.symm hqs
    have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
      have : IsSimpleGroup ↥K := hsimp
      have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := ψ₀.isSimpleGroup
      exact ConfAB.center_eq_bot_of_simple hq hs
    have htwo : CaseABTwoList ↥K → False := fun h2 => by
      obtain ⟨X, Q, y, hconf⟩ := S.exists_conf1366 h1222 h517 h37 h38 hK hinner
      exact not_conf1366_of_two hEven hD4 hTits hqs hsimp h2 hconf
    rcases hLie with hSQK | ⟨⟨e6⟩⟩ | hU33
    · have hSQ : Ch1.SQTKCharTwoLie (↥K ⧸ CFSG.pCore 2 ↥K) :=
        Ch1.SQTKCharTwoLie.of_mulEquiv ψ₀ hSQK
      have hL : ∀ hLK : LieZCentList ↥K, False := fun hLK =>
        hlie hinner hq hZ hSQ (ConfAB.lieZCentList_of_mulEquiv ψ₀ hLK) (Or.inl ⟨ψ₀⟩)
      rcases hSQK with (⟨f, hb⟩ | hTits') | ⟨n, hn, hPSL⟩
      · rcases hb with ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ |
          ⟨hf1, hf3, h⟩ | ⟨hf1, hf3, h⟩
        · exact hL ⟨f, Or.inl ⟨hf, h⟩⟩
        · rcases Nat.lt_or_ge f 2 with hf1 | hf2
          · have hf' : f = 1 := by omega
            subst hf'
            exact htwo (Or.inl ⟨3, Or.inl rfl, h⟩)
          · exact hL ⟨f, Or.inr (Or.inl ⟨hf2, h⟩)⟩
        · exact hL ⟨f, Or.inr (Or.inr (Or.inl ⟨hf, h⟩))⟩
        ·
          have hP : StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSp 2 2 f :=
            statedClassicalModel_of_mulEquiv ψ₀ h
          have hr := ConfAB.one_lt_pRank_of_psp hP
          have hKc : K ∈ cComp Gv := by
            have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
            rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
          have hGvS : SQTKGroup ↥Gv := sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple
            S.h13.nonabelian S.pCoreOf_Gv_ne_bot'
          have hSQ' := SQTKHyp.of_sqtkGroup ↥Gv hGvS
          have hr1 : 1 < CFSG.Open.pRank 3 (K.subgroupOf Gv) := by
            rw [CFSG.Quasithin.Vol2.Ch11.SecA.pRank_subgroupOf_eq hKG Nat.prime_three
              (by norm_num)]
            exact hr
          have hn : (K.subgroupOf Gv).Normal :=
            A318.normal_of_pRank_gt_one hGvS ((a38ForSQTK_of_cat h38) _ hSQ')
              (subgroupOf_mem_cComp hKc) Nat.prime_three (by norm_num) hr1
          exact hSp4 G T L V S hab K hK hn hsimp ⟨f, hf, hP⟩ hinner
            (S.Lv_inner_of_rank h1222 h517 hF318 h36 h37 h38 hEven hF3 hF6 hK hq hZ hr hSQ
              hinner)
        · exact hL ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, h⟩)))⟩
        · rcases Nat.lt_or_ge f 2 with hf1 | hf2
          · have hf' : f = 1 := by omega
            subst hf'
            exact htwo (Or.inr (Or.inl h))
          · exact hL ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf2, h⟩))))⟩
        · exact hL ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf1, hf3, h⟩)))))⟩
        · exact hL ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hf1, hf3, h⟩)))))⟩
      · exact htwo (Or.inr (Or.inr (Or.inl hTits')))
      · rcases hn with rfl | rfl
        · exact htwo (Or.inl ⟨4, Or.inr (Or.inl rfl), hPSL⟩)
        · exact htwo (Or.inl ⟨5, Or.inr (Or.inr rfl), hPSL⟩)
    · exact S.false_of_alt6 h331 h1327 h1336 hF318 h36 h38 hKF hab hK e6
    · exact htwo (Or.inr (Or.inr (Or.inr hU33)))
  ·
    let eZ : (↥K ⧸ Subgroup.center ↥K) ≃* (↥K ⧸ CFSG.pCore 2 ↥K) :=
      QuotientGroup.quotientMulEquivOfEq hZO
    have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hqs.2.1
    have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := eZ.symm.isSimpleGroup
    have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eZ (isQuasisimple_of_simple hqs.2.2)
    have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := ConfAB.center_eq_bot_of_simple hq hs
    rcases hL34 with h | h
    · refine hlie hinner hq hZ (Or.inl (Or.inl ⟨2, Or.inr (Or.inl ⟨by norm_num, h⟩)⟩))
        ⟨2, Or.inr (Or.inl ⟨le_rfl, h⟩)⟩ (Or.inr (F134.three_dvd_card_of_statedPSL_three h))
    · refine hlie hinner hq hZ
        (Or.inl (Or.inl ⟨2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩))))⟩))
        ⟨2, Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩)))⟩
        (Or.inr (F134.three_dvd_card_of_g2_two h))

end CFSG.Quasithin.H13.A5
