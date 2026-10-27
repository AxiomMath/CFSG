module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Defs
public import CFSG.Quasithin.EmptyFaithful.S1421STC3Step

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem normal_isPGroup_le_center_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (N : Subgroup Q) [N.Normal] (hN : IsPGroup 2 N) :
    N ≤ Subgroup.center Q := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have := hperf
  have := hsimple
  have hmapN : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · intro x hx
    have hx' : QuotientGroup.mk' (Subgroup.center Q) x ∈
        N.map (QuotientGroup.mk' (Subgroup.center Q)) := Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff _).1 hx'
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsurj :
        Function.Surjective ((QuotientGroup.mk' (Subgroup.center Q)).comp N.subtype) := by
      intro y
      have hy : y ∈ N.map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [h]
        trivial
      obtain ⟨n, hn, hny⟩ := hy
      exact ⟨⟨n, hn⟩, hny⟩
    have h2 : IsPGroup 2 (Q ⧸ Subgroup.center Q) := hN.of_surjective _ hsurj
    exact Group.IsPerfect.not_isNilpotent (Q ⧸ Subgroup.center Q) h2.isNilpotent

theorem pCoreOf_le_centralizer_of_isQuasisimple {K L : Subgroup G} (hLK : L ≤ K)
    (hLn : (L.subgroupOf K).Normal) (hq : CFSG.IsQuasisimple ↥L) :
    pCoreOf 2 K ≤ Subgroup.centralizer (L : Set G) := by
  have hKL : K ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mp hLn
  have hOK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K
  have hO2 : IsPGroup 2 (pCoreOf 2 K) := pCoreOf_isPGroup 2 K
  have hcomm : ⁅pCoreOf 2 K, L⁆ ≤ pCoreOf 2 K ⊓ L :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLK.trans hKO))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp (hOK.trans hKL))
  have hnormal : ((pCoreOf 2 K).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hKO (hLK g.2)) n).mp hn
  have hcentral : (pCoreOf 2 K).subgroupOf L ≤ Subgroup.center ↥L :=
    normal_isPGroup_le_center_of_isQuasisimple hq _ hO2.comap_subtype
  have hOLc : pCoreOf 2 K ⊓ L ≤ Subgroup.centralizer (L : Set G) := by
    rintro x ⟨hxO, hxL⟩
    have hxN : (⟨x, hxL⟩ : ↥L) ∈ (pCoreOf 2 K).subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr hxO
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcentral hxN) ⟨l, hl⟩)
  have h1 : ⁅⁅pCoreOf 2 K, L⁆, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hOLc)
  have h2 : ⁅⁅L, pCoreOf 2 K⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L (pCoreOf 2 K)]
    exact h1
  have h3 : ⁅⁅L, L⁆, pCoreOf 2 K⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  have := hq.1
  rw [Subgroup.commutator_eq_self, Subgroup.commutator_comm] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

theorem pCoreOf_g0_le_centralizer (c : Core3Ctx T M H K1 L M₁) (hq : CFSG.IsQuasisimple ↥L) :
    pCoreOf 2 (S1421.g0Of T M H K1) ≤ Subgroup.centralizer (L : Set G) :=
  pCoreOf_le_centralizer_of_isQuasisimple (le_of_mem_cComp c.mem) c.normal hq

theorem exists_involution_mem_inf_centerOf {S N : Subgroup G} (hS : IsPGroup 2 S) (hNS : N ≤ S)
    (hN : S ≤ Subgroup.normalizer (N : Set G)) (hN1 : N ≠ ⊥) :
    ∃ z : G, z ∈ N ∧ z ∈ centerOf S ∧ z ≠ 1 ∧ z ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have hn : (N.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNS).mpr hN
  have hne : N.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hN1
    rw [eq_bot_iff]
    intro w hw
    have hw' : (⟨w, hNS hw⟩ : ↥S) ∈ N.subgroupOf S := Subgroup.mem_subgroupOf.mpr hw
    rw [hbot, Subgroup.mem_bot] at hw'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hw')
  have hI : N.subgroupOf S ⊓ Subgroup.center ↥S ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hI2 : IsPGroup 2 ↥(N.subgroupOf S ⊓ Subgroup.center ↥S) := hS.to_subgroup _
  have hdvd : 2 ∣ Nat.card ↥(N.subgroupOf S ⊓ Subgroup.center ↥S) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hI2
    rw [hk]
    refine dvd_pow_self 2 fun hk0 => hI ?_
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(N.subgroupOf S ⊓ Subgroup.center ↥S)) 2 hdvd
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  refine ⟨(((x : ↥S)) : G), Subgroup.mem_subgroupOf.mp x.2.1, ⟨(x : ↥S).2, ?_⟩, ?_, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2.2 ⟨y, hy⟩)
  · intro h
    exact hx1 (Subtype.ext (Subtype.ext h))
  · have h1 := pow_orderOf_eq_one x
    rw [hx] at h1
    have h2 := congrArg
      (fun w : ↥(N.subgroupOf S ⊓ Subgroup.center ↥S) => (((w : ↥S)) : G)) h1
    simpa using h2

theorem exists_zL (c : Core3Ctx T M H K1 L M₁) (hq : CFSG.IsQuasisimple ↥L)
    (hLS : S1421.g0Of T M H K1 = L ⊔ sOf T K1) :
    ∃ ZL : Subgroup G, ZL ≠ ⊥ ∧ ZL ≤ omegaOneCenterOf (sOf T K1) ∧
      S1421.g0Of T M H K1 ≤ Subgroup.centralizer (ZL : Set G) := by
  have hOc := pCoreOf_g0_le_centralizer c hq
  have hSyl : IsSylowTwoOf (sOf T K1) (g0Of T M H K1) := isSylowTwoOf_g0 c.inM c.sylow
  have hOS : pCoreOf 2 (g0Of T M H K1) ≤ sOf T K1 := pCoreOf_two_le_of_isSylowTwoOf hSyl
  have hOn : sOf T K1 ≤ Subgroup.normalizer (pCoreOf 2 (g0Of T M H K1) : Set G) :=
    (le_sup_right : sOf T K1 ≤ g0Of T M H K1).trans (le_normalizer_pCoreOf 2 _)
  obtain ⟨z, hzO, hzC, hz1, hz2⟩ :=
    exists_involution_mem_inf_centerOf (isPGroup_sOf c.st) hOS hOn c.pCore_ne
  refine ⟨omegaOneCenterOf (sOf T K1) ⊓ Subgroup.centralizer (L : Set G), ?_, inf_le_left, ?_⟩
  · intro h
    have hz : z ∈ omegaOneCenterOf (sOf T K1) ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨Subgroup.subset_closure ⟨hzC, hz2⟩, hOc hzO⟩
    rw [h, Subgroup.mem_bot] at hz
    exact hz1 hz
  · refine hLS.le.trans (sup_le (fun l hl => ?_) (fun s hs => ?_))
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp hx.2 l hl).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp
        (A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ hx.1)) s hs).symm

theorem exists_inM_normalizer (h2 : Lemma14215Step2) (c : Core3Ctx T M H K1 L M₁)
    {ZL : Subgroup G} (hZL : ZL ≠ ⊥) (hZ2 : IsPGroup 2 ZL)
    (hc : S1421.g0Of T M H K1 ≤ Subgroup.centralizer (ZL : Set G)) :
    ∃ M₁' : Subgroup G, InM (Subgroup.normalizer (ZL : Set G)) M₁' ∧
      InM (S1421.g0Of T M H K1) M₁' ∧ ¬ T ≤ M₁' ∧ IsSylowTwoOf (sOf T K1) M₁' := by
  have hO : pCoreOf 2 (Subgroup.normalizer (ZL : Set G)) ≠ ⊥ := by
    intro h
    have h1 := le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : ZL ≤ Subgroup.normalizer (ZL : Set G)) le_rfl hZ2
    rw [h] at h1
    exact hZL (le_bot_iff.mp h1)
  obtain ⟨M₁', hM₁'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have hG0 : InM (g0Of T M H K1) M₁' :=
    ⟨hM₁'.1, (hc.trans (Subgroup.centralizer_le_normalizer (s := (ZL : Set G)))).trans hM₁'.2⟩
  have hT : ¬ T ≤ M₁' := not_le_of_inM_G0 c.st hG0
  exact ⟨M₁', hM₁', hG0, hT, h2 G T M H K1 c.st c.lt c.pCore_y M₁' hG0 hT⟩

theorem le_mcOf_of_le_normalizer_char (st : Setting1427 T M H K1) (hlt : sOf T K1 < T)
    (h210 : Lemma14210) {C L : Subgroup G} (hC : C ≠ ⊥) (hCS : C ≤ sOf T K1)
    (hchar : (C.subgroupOf (sOf T K1)).Characteristic) (hK1L : K1 ≤ L)
    (hLC : L ≤ Subgroup.normalizer (C : Set G)) : L ≤ mcOf T := by
  have hyp := st.hyp
  have hC2 : IsPGroup 2 C := (isPGroup_sOf st).to_le hCS
  have hTS : T ≤ Subgroup.normalizer (C : Set G) :=
    (T_le_normalizer_sOf st hlt.ne).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hCS hchar)
  have hKT : K1 ⊔ T ≤ Subgroup.normalizer (C : Set G) := sup_le (hK1L.trans hLC) hTS
  have hO : pCoreOf 2 (Subgroup.normalizer (C : Set G)) ≠ ⊥ := by
    intro h
    have h1 := le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : C ≤ Subgroup.normalizer (C : Set G)) le_rfl hC2
    rw [h] at h1
    exact hC (le_bot_iff.mp h1)
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have hTSyl : IsSylowTwoOf T (mcOf T) :=
    isSylowTwoOf_of_isSylowTwo hyp.sylow hyp.toQTFE14.t_le_mc
  have huniq := h210 G T M H K1 st hlt T hTSyl sOf_le_T
  have heq := huniq.2 M' ⟨hM'.1, hKT.trans hM'.2⟩
  rw [heq] at hM'
  exact hLC.trans hM'.2

end S1421

end CFSG.Quasithin
