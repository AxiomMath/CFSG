module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Basic
public import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofNoSz
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (PPrimeCoreIn)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

open CFSG.LocalAnalysis.UniquenessCase.UC6S846

private theorem k89oc_sz_of_isKGroup
    {Y : Type} [Group Y] [Finite Y] (hK : CFSG.IsKGroup Y) (h3 : ¬ 3 ∣ Nat.card Y)
    (H : Subgroup Y) (N : Subgroup H) [N.Normal] [IsSimpleGroup (H ⧸ N)]
    (hnab : ∃ a b : H ⧸ N, a * b ≠ b * a) : 5 ∣ Nat.card (H ⧸ N) := by
  obtain ⟨f, hf⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_isKGroup_section hK h3 H N hnab
  exact CFSG.RankThree.PartTwo.Sec16.KSL3PiNoSzProof.five_dvd_card_of_suzukiModel hf



private theorem k89oc_exists_maximal_normal
    {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) (hK : K ≠ ⊥) :
    ∃ N : Subgroup ↥K, N.Normal ∧ N ≠ ⊤ ∧
      ∀ M : Subgroup ↥K, M.Normal → N < M → M = ⊤ := by
  classical
  have hbot_ne_top : (⊥ : Subgroup ↥K) ≠ ⊤ := by
    intro h
    have hKbot : K = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ (⊥ : Subgroup ↥K) := by
        rw [h]; exact Subgroup.mem_top _
      simpa using this
    exact hK hKbot
  obtain ⟨N, ⟨hNnorm, hNne⟩, hNmax⟩ := Set.exists_max_image
      {L : Subgroup ↥K | L.Normal ∧ L ≠ ⊤} (fun L => Nat.card L)
      (Set.toFinite _) ⟨⊥, inferInstance, hbot_ne_top⟩
  refine ⟨N, hNnorm, hNne, fun M hMnorm hNM => ?_⟩
  by_contra hMne
  have hcard : Nat.card N < Nat.card M := r889_card_lt_of_lt hNM
  have hle := hNmax M ⟨hMnorm, hMne⟩
  omega

private theorem k89oc_isSimpleGroup_quotient_of_maximal_normal
    {H : Type} [Group H] (N : Subgroup H) [N.Normal] (hNne : N ≠ ⊤)
    (hmax : ∀ M : Subgroup H, M.Normal → N < M → M = ⊤) :
    IsSimpleGroup (H ⧸ N) := by
  refine { toNontrivial := QuotientGroup.nontrivial_iff.mpr hNne,
           eq_bot_or_eq_top_of_normal := ?_ }
  intro P hP
  have : P.Normal := hP
  have hN_le_comap : N ≤ P.comap (QuotientGroup.mk' N) := by
    intro n hn
    show (QuotientGroup.mk' N) n ∈ P
    have h1 : (QuotientGroup.mk' N) n = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hn
    rw [h1]
    exact P.one_mem
  have hcomap_normal : (P.comap (QuotientGroup.mk' N)).Normal :=
    hP.comap (QuotientGroup.mk' N)
  have hcomap_eq : P.comap (QuotientGroup.mk' N) = N ∨
      P.comap (QuotientGroup.mk' N) = ⊤ := by
    by_cases h : P.comap (QuotientGroup.mk' N) = N
    · exact Or.inl h
    · exact Or.inr (hmax _ hcomap_normal (lt_of_le_of_ne hN_le_comap (Ne.symm h)))
  have hmap : P = (P.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) :=
    (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) P).symm
  rcases hcomap_eq with h | h
  · left
    rw [hmap, h]
    exact (Subgroup.map_eq_bot_iff N).mpr (by rw [QuotientGroup.ker_mk'])
  · right
    rw [hmap, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

private theorem k89oc_solvable_of_five_dvd_nonabelian_sections
    {Y : Type} [Group Y] [Finite Y]
    (h5 : ¬ 5 ∣ Nat.card Y)
    (hsz : ∀ (H : Subgroup Y) (N : Subgroup H) [N.Normal] [IsSimpleGroup (H ⧸ N)],
      (∃ a b : H ⧸ N, a * b ≠ b * a) → 5 ∣ Nat.card (H ⧸ N)) :
    Group.IsSolvable Y := by
  classical
  by_contra hns
  obtain ⟨K, hKns, hKmin⟩ := Set.exists_min_image
      {K : Subgroup Y | ¬ Group.IsSolvable ↥K} (fun K => Nat.card K)
      (Set.toFinite _) ⟨⊤, by
        intro h
        exact hns (Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv (G := Y)).toMonoidHom)
          (Subgroup.topEquiv (G := Y)).surjective)⟩
  have hKne_bot : K ≠ ⊥ := by
    intro h
    apply hKns
    rw [h]
    infer_instance
  obtain ⟨N, hNnorm, hNne, hNmax⟩ := k89oc_exists_maximal_normal K hKne_bot
  have : N.Normal := hNnorm
  have hsimple : IsSimpleGroup (K ⧸ N) :=
    k89oc_isSimpleGroup_quotient_of_maximal_normal N hNne hNmax
  let N' : Subgroup Y := N.map K.subtype
  have hN'_le : N' ≤ K := Subgroup.map_subtype_le N
  have hN'_card : Nat.card N' = Nat.card N :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hN'_lt : N' < K := by
    have htopmap : (⊤ : Subgroup ↥K).map K.subtype = K := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have := (Subgroup.map_subtype_lt_map_subtype (G' := K) (H := N) (K := ⊤)).mpr
      (lt_top_iff_ne_top.mpr hNne)
    rwa [htopmap] at this
  have hN'solv : Group.IsSolvable ↥N' := by
    by_contra hN'ns
    have hle := hKmin N' hN'ns
    have hcard : Nat.card N' < Nat.card K := r889_card_lt_of_lt hN'_lt
    omega
  have hNsolv : Group.IsSolvable ↥N := by
    have : Group.IsSolvable ↥N' := hN'solv
    let e := Subgroup.equivMapOfInjective N K.subtype K.subtype_injective
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  by_cases hab : ∀ a b : K ⧸ N, a * b = b * a
  · have : IsMulCommutative (K ⧸ N) := ⟨⟨hab⟩⟩
    have : Group.IsSolvable ↥N := hNsolv
    exact hKns (Group.isSolvable_of_subgroup_quotient N)
  · push Not at hab
    obtain ⟨a, b, hab'⟩ := hab
    have h5dvd : 5 ∣ Nat.card (K ⧸ N) := hsz K N ⟨a, b, hab'⟩
    have hdvd : Nat.card (K ⧸ N) ∣ Nat.card K := Subgroup.card_quotient_dvd_card N
    have hdvd' : Nat.card K ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card K
    exact h5 (h5dvd.trans (hdvd.trans hdvd'))


private theorem k89oc_card_Bar2_K
    {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G} {ω : G}
    (hFacts : AllFacts889 D) (hω : Set889 D L P ω) :
    Nat.card (Bar2 (K889 L ω)) = 1080 := by
  obtain ⟨-, hZ, hAlt⟩ := (hFacts L P ω hω).alt6
  have hcard_quot :
      Nat.card (Bar2 (K889 L ω) ⧸ Subgroup.center (Bar2 (K889 L ω))) = 360 := by
    obtain ⟨e⟩ := hAlt
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Bar2 (K889 L ω)))
  rw [hZ, hcard_quot] at h
  norm_num at h
  exact h

private theorem k89oc_five_dvd_card_K
    {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G} {ω : G}
    (hFacts : AllFacts889 D) (hω : Set889 D L P ω) :
    5 ∣ Nat.card (K889 L ω) := by
  have hF := hFacts L P ω hω
  obtain ⟨-, hZ, hAlt⟩ := hF.alt6
  have hcard_quot :
      Nat.card (Bar2 (K889 L ω) ⧸ Subgroup.center (Bar2 (K889 L ω))) = 360 := by
    obtain ⟨e⟩ := hAlt
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hcard_bar : Nat.card (Bar2 (K889 L ω)) = 1080 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Bar2 (K889 L ω)))
    rw [hZ, hcard_quot] at h
    norm_num at h
    exact h
  have h5bar : 5 ∣ Nat.card (Bar2 (K889 L ω)) := by
    rw [hcard_bar]; norm_num
  exact h5bar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥(K889 L ω)))



private theorem k89oc_mem_zpowers_of_orderOf_eq_prime
    {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y} (hS : IsCyclic ↥S)
    {p : ℕ} (hp : p.Prime) {e f : Y} (heS : e ∈ S) (he : orderOf e = p)
    (hfS : f ∈ S) (hf : orderOf f = p) :
    f ∈ Subgroup.zpowers e := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic ↥S := hS
  have : Fintype ↥S := Fintype.ofFinite _
  let eS : ↥S := ⟨e, heS⟩
  let fS : ↥S := ⟨f, hfS⟩
  have heS_order : orderOf eS = p := by rw [← Subgroup.orderOf_coe eS, he]
  have hfS_order : orderOf fS = p := by rw [← Subgroup.orderOf_coe fS, hf]
  have hcard_zp : Nat.card (Subgroup.zpowers eS) = p := by
    rw [Nat.card_zpowers, heS_order]
  have : Fintype {x : ↥S | x ^ p = 1} := Fintype.ofFinite _
  have hU : ({x : ↥S | x ^ p = 1} : Set ↥S).ncard ≤ p := by
    rw [Set.ncard_eq_toFinset_card']
    simpa using IsCyclic.card_pow_eq_one_le (α := ↥S) (n := p) hp.pos
  have hsub : (Subgroup.zpowers eS : Set ↥S) ⊆ {x : ↥S | x ^ p = 1} := by
    intro x hx
    refine (orderOf_dvd_iff_pow_eq_one).mp ?_
    have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers eS) hx
    rwa [Nat.card_zpowers, heS_order] at this
  have hzp_ncard : (Subgroup.zpowers eS : Set ↥S).ncard = p := by
    rw [← Nat.card_coe_set_eq]
    exact hcard_zp
  have heq : (Subgroup.zpowers eS : Set ↥S) = {x : ↥S | x ^ p = 1} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hzp_ncard]; exact hU)
  have hfU : fS ∈ {x : ↥S | x ^ p = 1} :=
    (orderOf_dvd_iff_pow_eq_one).mp (by rw [hfS_order])
  have hf_zp : fS ∈ Subgroup.zpowers eS := by
    show fS ∈ (Subgroup.zpowers eS : Set ↥S)
    rw [heq]
    exact hfU
  have : f ∈ (Subgroup.zpowers eS).map S.subtype := ⟨fS, hf_zp, rfl⟩
  simpa [MonoidHom.map_zpowers] using this

private theorem k89oc_exists_sylow5_containing
    {G : Type} [Group G] [Finite G] {X : Subgroup G} {e : G} (heX : e ∈ X) (he : orderOf e = 5) :
    ∃ S : Subgroup G, IsSylowOf 5 S X ∧ e ∈ S := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let eX : ↥X := ⟨e, heX⟩
  have horder : orderOf eX = 5 := by rw [← Subgroup.orderOf_coe eX, he]
  have hP : IsPGroup 5 (Subgroup.zpowers eX) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, horder, pow_one])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  refine ⟨(Q : Subgroup ↥X).map X.subtype, ⟨Q, rfl⟩, ?_⟩
  exact ⟨eX, hQ (Subgroup.mem_zpowers eX), rfl⟩

private theorem k89oc_pRank_five_X_le_one
    {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (h885 : R885 D) (hFacts : AllFacts889 D) (hFive : S889Five D)
    {L P : Subgroup G} {ω : G} (hω : Set889 D L P ω)
    {X : Subgroup G} (hXne : X ≠ ⊤) (hKX : K889 L ω ≤ X) (hXM : ¬ X ≤ D.M) :
    CFSG.Open.pRank 5 X ≤ 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hS : Set880 D L P := hω.set880
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hS.mem
  have h5mem : 5 ∈ D.sig := by rw [(h885 L P hS).2.1]; simp
  have hsp5 : IsStronglyPEmbedded 5 D.M := sp_of_mem_sig hSg hns h5mem
  have h5K : 5 ∣ Nat.card (K889 L ω) := k89oc_five_dvd_card_K hFacts hω
  have hK_le_XM : K889 L ω ≤ X ⊓ D.M :=
    le_inf hKX ((r889_K889_le_left L ω).trans (r889_le_M hS))
  have h5XM : 5 ∣ Nat.card ↥(X ⊓ D.M) := h5K.trans (Subgroup.card_dvd_of_le hK_le_XM)
  obtain ⟨S₀, hS₀⟩ := exists_isSylowOf 5 (X ⊓ D.M)
  have hS₀_le_M : S₀ ≤ D.M := hS₀.le.trans inf_le_right
  have hS₀_ne_bot : S₀ ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card S₀ = 1 := by rw [hbot, Subgroup.card_bot]
    have hcard' := hS₀.card_eq
    rw [hcard] at hcard'
    have hk : 0 < (Nat.card ↥(X ⊓ D.M)).factorization 5 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_five
        (Nat.card_pos (α := ↥(X ⊓ D.M))).ne' h5XM
    have hlt : 1 < 5 ^ (Nat.card ↥(X ⊓ D.M)).factorization 5 :=
      one_lt_pow' (by norm_num : (1 : ℕ) < 5) hk.ne'
    exact (ne_of_gt hlt) hcard'.symm
  have hS₀_cyc : IsCyclic ↥S₀ :=
    CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_five (by norm_num) hS₀.isPGroup
      hS₀.le (hFive L P ω hω X hXne hKX hXM)
  have hS₀_sylow_X : IsSylowOf 5 S₀ X := by
    by_contra hnot
    have hS₀_le_X : S₀ ≤ X := hS₀.le.trans inf_le_left
    obtain ⟨Q, hQle⟩ := (hS₀.isPGroup.comap_subtype (K := X)).exists_le_sylow
    have hS₀_le_T : S₀ ≤ (Q : Subgroup ↥X).map X.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hS₀_le_X]
      exact Subgroup.map_mono hQle
    have hT_pgroup : IsPGroup 5 ((Q : Subgroup ↥X).map X.subtype) :=
      Q.isPGroup'.map X.subtype
    have hS₀_lt_T : S₀ < (Q : Subgroup ↥X).map X.subtype := by
      refine lt_of_le_of_ne hS₀_le_T ?_
      intro hEq
      exact hnot ⟨Q, hEq.symm⟩
    obtain ⟨x, hxT, hx_norm, hx_not_mem⟩ :=
      r889_exists_mem_normalizer_of_lt hT_pgroup hS₀_lt_T
    have hxX : x ∈ X := Subgroup.map_subtype_le _ hxT
    have hxM : x ∈ D.M := hsp5.normalizer_le hS₀_ne_bot hS₀.isPGroup hS₀_le_M hx_norm
    have hzp : IsPGroup 5 (Subgroup.zpowers x) :=
      hT_pgroup.to_le (Subgroup.zpowers_le.mpr hxT)
    have hsup_le : (S₀ ⊔ Subgroup.zpowers x : Subgroup G) ≤ X ⊓ D.M := by
      refine sup_le hS₀.le ?_
      exact Subgroup.zpowers_le.mpr ⟨hxX, hxM⟩
    have hsup_pgroup : IsPGroup 5 ↥(S₀ ⊔ Subgroup.zpowers x : Subgroup G) := by
      rw [sup_comm]
      exact r889_isPGroup_sup hzp hS₀.isPGroup (Subgroup.zpowers_le.mpr hx_norm)
    have hEq : (S₀ ⊔ Subgroup.zpowers x : Subgroup G) = S₀ :=
      IsSylowOf.eq_of_le hS₀ le_sup_left hsup_le hsup_pgroup
    have hx_sup : x ∈ (S₀ ⊔ Subgroup.zpowers x : Subgroup G) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    exact hx_not_mem (hEq ▸ hx_sup)
  obtain ⟨Q₀, hQ₀⟩ := hS₀_sylow_X.exists_sylow_eq_subgroupOf
  have hQ₀_cyc : IsCyclic (Q₀ : Subgroup ↥X) := by
    rw [hQ₀]
    exact (Subgroup.subgroupOfEquivOfLe hS₀_sylow_X.le).isCyclic.mpr hS₀_cyc
  have := CFSG.AGLEmbedding.pRank_le_one_of_isCyclic_sylow Nat.prime_five Q₀ hQ₀_cyc
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup X] at this

theorem s889_odd_core
    {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D) (h885 : R885 D)
    (hFacts : AllFacts889 D) (hFive : S889Five D) : S889OddCore D := by
  intro L P ω hω X hXne hKX hXM
  classical
  have h880 : Set880 D L P := hω.set880
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC h880.mem
  let I := PPrimeCoreIn 3 X
  have hI_le_X : I ≤ X := by
    show (PPrimeCoreIn 3 X) ≤ X
    exact Subgroup.map_subtype_le _
  have hI_ne_top : I ≠ ⊤ := fun h => hXne (top_le_iff.mp (h ▸ hI_le_X))
  have hI_normal : X ≤ Subgroup.normalizer (I : Set G) := by
    have hsub : (I.subgroupOf X).Normal := by
      have hIeq : I.subgroupOf X = CFSG.pPrimeCore 3 ↥X := by
        show (PPrimeCoreIn 3 X).subgroupOf X = CFSG.pPrimeCore 3 ↥X
        rw [PPrimeCoreIn, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
      rw [hIeq]
      infer_instance
    rwa [Subgroup.normal_subgroupOf_iff_le_normalizer hI_le_X] at hsub
  have hI_coprime : Nat.Coprime 3 (Nat.card ↥I) := by
    have hcard : Nat.card ↥I = Nat.card ↥(CFSG.pPrimeCore 3 ↥X) := by
      show Nat.card ↥(PPrimeCoreIn 3 X) = Nat.card ↥(CFSG.pPrimeCore 3 ↥X)
      exact Subgroup.card_map_of_injective (K := CFSG.pPrimeCore 3 ↥X) X.subtype_injective
    rw [hcard]
    exact CFSG.pPrimeCore_coprime_card
  have h5I : ¬ 5 ∣ Nat.card ↥I := by
    intro h5dvd
    obtain ⟨eK, heK⟩ := exists_prime_orderOf_dvd_card' 5 (k89oc_five_dvd_card_K hFacts hω)
    let e : G := eK
    have heK_mem : e ∈ K889 L ω := eK.2
    have he_order : orderOf e = 5 := by
      rw [Subgroup.orderOf_coe eK, heK]
    obtain ⟨S, hS_syl, heS⟩ := k89oc_exists_sylow5_containing (X := X) (hKX heK_mem) he_order
    have hXrank : CFSG.Open.pRank 5 X ≤ 1 :=
      k89oc_pRank_five_X_le_one hSg h885 hFacts hFive hω hXne hKX hXM
    have hS_cyc : IsCyclic ↥S :=
      CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_five (by norm_num) hS_syl.isPGroup hS_syl.le hXrank
    have hIS_sylow : IsSylowOf 5 (S ⊓ I) I :=
      hS_syl.inf_of_le_normalizer hI_le_X hI_normal
    have h5IS : 5 ∣ Nat.card ↥(S ⊓ I) := by
      rw [hIS_sylow.card_eq]
      exact dvd_pow_self 5 (Nat.Prime.factorization_pos_of_dvd Nat.prime_five
        (Nat.card_pos (α := ↥I)).ne' h5dvd).ne'
    obtain ⟨fK, hfK⟩ := exists_prime_orderOf_dvd_card' 5 h5IS
    let f : G := fK
    have hfIS_mem : f ∈ S ⊓ I := fK.2
    have hf_order : orderOf f = 5 := by
      rw [Subgroup.orderOf_coe fK, hfK]
    have hfS : f ∈ S := hfIS_mem.1
    have hf_zp : f ∈ Subgroup.zpowers e :=
      k89oc_mem_zpowers_of_orderOf_eq_prime hS_cyc Nat.prime_five heS he_order hfS hf_order
    have he_I : e ∈ I := by
      have hle : Subgroup.zpowers f ≤ Subgroup.zpowers e := Subgroup.zpowers_le.mpr hf_zp
      have hcard_f : Nat.card (Subgroup.zpowers f) = 5 := by rw [Nat.card_zpowers, hf_order]
      have hcard_e : Nat.card (Subgroup.zpowers e) = 5 := by rw [Nat.card_zpowers, he_order]
      have heq : Subgroup.zpowers f = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcard_e, hcard_f])
      have he_zp : e ∈ Subgroup.zpowers f := by
        rw [heq]
        exact Subgroup.mem_zpowers e
      exact (Subgroup.zpowers_le.mpr hfIS_mem.2) he_zp
    let Ksub := K889 L ω
    let J : Subgroup G := I ⊓ Ksub
    have he_J : e ∈ J := ⟨he_I, heK_mem⟩
    have hJ_normal : (J.subgroupOf Ksub).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro x hx
      exact r889_mem_normalizer_inf (hI_normal (hKX hx)) (Subgroup.le_normalizer hx)
    let π := QuotientGroup.mk' (CFSG.pCore 2 ↥Ksub)
    let Nbar : Subgroup (Bar2 Ksub) := (J.subgroupOf Ksub).map π
    have hNbar_normal : Nbar.Normal :=
      Subgroup.Normal.map hJ_normal π (QuotientGroup.mk'_surjective _)
    have hQ : CFSG.Open.IsQuasisimple (Bar2 Ksub) :=
      ⟨Group.isPerfect_def.mp (hFacts L P ω hω).alt6.1.1, (hFacts L P ω hω).alt6.1.2.1⟩
    have hNbar_coprime : Nat.Coprime 3 (Nat.card Nbar) := by
      have hdvd1 : Nat.card Nbar ∣ Nat.card ↥(J.subgroupOf Ksub) :=
        Subgroup.card_map_dvd (J.subgroupOf Ksub) π
      have hdvd2 : Nat.card ↥(J.subgroupOf Ksub) ∣ Nat.card ↥I := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact hI_coprime.coprime_dvd_right (hdvd1.trans hdvd2)
    have hJ_le_O2 : J ≤ pCoreOf 2 Ksub := by
      rcases GL83.I243.normal_le_center_or_eq_top (Q := Bar2 Ksub) hQ Nbar with hcenter | htop
      · have hcardN : Nat.card Nbar = 1 := by
          have hdvd : Nat.card Nbar ∣ 3 := by
            rw [← (hFacts L P ω hω).alt6.2.1]
            exact Subgroup.card_dvd_of_le hcenter
          exact Nat.eq_one_of_dvd_coprimes (a := 3) (b := Nat.card Nbar)
            (k := Nat.card Nbar) hNbar_coprime hdvd dvd_rfl
        have hNbar_bot : Nbar = ⊥ := Subgroup.eq_bot_of_card_eq (H := Nbar) hcardN
        have hsub : J.subgroupOf Ksub ≤ CFSG.pCore 2 ↥Ksub := by
          rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥Ksub)]
          exact (Subgroup.map_eq_bot_iff (J.subgroupOf Ksub)).mp hNbar_bot
        calc J = (J.subgroupOf Ksub).map Ksub.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
          _ ≤ (CFSG.pCore 2 ↥Ksub).map Ksub.subtype := Subgroup.map_mono hsub
          _ = pCoreOf 2 Ksub := rfl
      · exfalso
        have h3dvd : 3 ∣ Nat.card Nbar := by
          rw [htop, Subgroup.card_top, k89oc_card_Bar2_K hFacts hω]
          norm_num
        exact (Nat.prime_three.coprime_iff_not_dvd).mp hNbar_coprime h3dvd
    have he_O2 : e ∈ pCoreOf 2 Ksub := hJ_le_O2 he_J
    have hO2_pgroup : IsPGroup 2 (pCoreOf 2 Ksub) := by
      show IsPGroup 2 ((CFSG.pCore 2 ↥Ksub).map Ksub.subtype)
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥Ksub)).map Ksub.subtype
    obtain ⟨k, hk⟩ := hO2_pgroup.exists_orderOf_dvd_pow ⟨e, he_O2⟩
    have hk5 : 5 ∣ 2 ^ k := by
      simpa [he_order, Subgroup.orderOf_coe] using hk
    have h52 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow hk5
    norm_num at h52
  refine ⟨h5I, ?_⟩
  have hKgroup : CFSG.Open.IsKGroup ↥I := D.standing.kProper.isKGroup I hI_ne_top
  have hK : CFSG.IsKGroup ↥I :=
    CFSG.Assembly.kGroupAllSimple_of_kGroupNonab_of_catalogImp
      (fun X _ _ _ _ h => h) CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple hKgroup
  have h3I : ¬ 3 ∣ Nat.card ↥I :=
    (Nat.prime_three.coprime_iff_not_dvd).mp hI_coprime
  exact k89oc_solvable_of_five_dvd_nonabelian_sections h5I (k89oc_sz_of_isKGroup hK h3I)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
