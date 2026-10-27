module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List880Center
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ThreeConjugateRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKLeaves
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OppNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.GroupTheory.ComponentCovering
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup
public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R76Sig)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (R82 List880)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

private theorem isQuasisimple_of_open {X : Type} [Group X]
    (h : CFSG.Open.IsQuasisimple X) : CFSG.IsQuasisimple X := by
  obtain ⟨hperf, hsimple⟩ := h
  refine ⟨Group.isPerfect_def.mpr hperf, hsimple, ?_⟩
  by_contra hcomm
  have hc : ∀ a b : X ⧸ Subgroup.center X, a * b = b * a := fun a b =>
    by_contra fun hne => hcomm ⟨a, b, hne⟩
  have hle : commutator X ≤ Subgroup.center X := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have h1 := map_commutatorElement (QuotientGroup.mk' (Subgroup.center X)) x y
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hc _ _)] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨a, ha⟩ := @exists_ne (X ⧸ Subgroup.center X) hsimple.toNontrivial 1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  have hx : x ∈ commutator X := by
    rw [hperf]
    exact Subgroup.mem_top x
  exact ha ((QuotientGroup.eq_one_iff x).2 (hle hx))
private theorem isSylowOf_subgroupOf_of_isSylowOf {G : Type} [Group G] [Finite G]
    {L Q H : Subgroup G}
    (hLH : L ≤ H) (hQ : IsSylowOf 3 Q L) :
    IsSylowOf 3 (Q.subgroupOf H) (L.subgroupOf H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hle, hp, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hQ
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  exact ⟨fun x hx => hle hx, hp.comap_subtype, by
    rw [Subgroup.relIndex_subgroupOf hLH]; exact hdvd⟩

private theorem sup_inf_normalizer_eq_of_isSylowOf_three {G : Type} [Group G] [Finite G]
    {L Q H : Subgroup G}
    (hLH : L ≤ H) (hHnorm : H ≤ normalizer (L : Set G))
    (hQ : IsSylowOf 3 Q L) (hQH : Q ≤ H) :
    L ⊔ (H ⊓ normalizer (Q : Set G)) = H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHnorm
  have hQ' : IsSylowOf 3 (Q.subgroupOf H) (L.subgroupOf H) :=
    isSylowOf_subgroupOf_of_isSylowOf hLH hQ
  obtain ⟨P, hP⟩ := hQ'.exists_sylow_eq_subgroupOf
  have hPmap : (P : Subgroup ↥(L.subgroupOf H)).map (L.subgroupOf H).subtype =
      Q.subgroupOf H := by
    rw [hP, Subgroup.map_subgroupOf_eq_of_le]
    exact fun x hx => hQ.le hx
  have hfratt : L.subgroupOf H ⊔ Subgroup.normalizer
      ((Q.subgroupOf H : Subgroup ↥H) : Set ↥H) = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top P
    rw [hPmap] at h
    exact (sup_comm ..).trans h
  have hsub : (L ⊔ (H ⊓ normalizer (Q : Set G))).subgroupOf H = ⊤ := by
    rw [Subgroup.subgroupOf_sup hLH inf_le_left, Subgroup.inf_subgroupOf_left,
      Subgroup.subgroupOf_normalizer_eq hQH]
    exact hfratt
  have hle : L ⊔ (H ⊓ normalizer (Q : Set G)) ≤ H := sup_le hLH inf_le_left
  have heq : (L ⊔ (H ⊓ normalizer (Q : Set G))).subgroupOf H = H.subgroupOf H := by
    rw [hsub, Subgroup.subgroupOf_self]
  have h2 := Subgroup.subgroupOf_inj.mp heq
  rwa [inf_eq_left.mpr hle, inf_idem] at h2

private theorem pRank_subgroupOf_eq_aux {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K D : Subgroup G} (h : K ≤ D) :
    CFSG.Open.pRank p (K.subgroupOf D) = CFSG.Open.pRank p K := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (K.subgroupOf D),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv
    (Fact.out : p.Prime).one_lt (Subgroup.subgroupOfEquivOfLe h)

private theorem pRank_inf_normalizer_le_one_of_action {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H Q : Subgroup G}
    (hAut : ¬ p ∣ Nat.card (MulAut ↥Q))
    (hC : CFSG.Open.pRank p (H ⊓ centralizer (Q : Set G)) ≤ 1) :
    CFSG.Open.pRank p (H ⊓ normalizer (Q : Set G)) ≤ 1 := by
  set D : Subgroup G := H ⊓ normalizer (Q : Set G)
  have hDH : D ≤ H := inf_le_left
  have hDN : D ≤ normalizer (Q : Set G) := inf_le_right
  let θ : ↥D →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom (H := Q)).comp (Subgroup.inclusion hDN)
  have hker : θ.ker = (D ⊓ centralizer (Q : Set G)).subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker]
    change Q.normalizerMonoidHom ((Subgroup.inclusion hDN) x) = 1 ↔
      (x : G) ∈ D ∧ (x : G) ∈ centralizer (Q : Set G)
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hrange : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥Q)) = 0 :=
    CFSG.pRank_eq_zero_of_not_dvd_card (Fact.out : p.Prime) hAut
  have hineq := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map
    (p := p) (Fact.out : p.Prime) θ (⊤ : Subgroup ↥D)
  rw [top_inf_eq, ← MonoidHom.range_eq_map] at hineq
  have h1 : CFSG.Open.pRank p θ.ker ≤ 1 := by
    rw [hker]
    rw [pRank_subgroupOf_eq_aux inf_le_left]
    refine (CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt ?_).trans hC
    exact le_inf ((inf_le_left : D ⊓ centralizer (Q : Set G) ≤ D).trans hDH) inf_le_right
  have h2 : CFSG.Open.pRank p θ.range = 0 :=
    le_antisymm ((CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt
      (le_top : θ.range ≤ ⊤)).trans (le_of_eq hrange)) (Nat.zero_le _)
  have h3 : CFSG.Open.pRank p D = CFSG.Open.pRank p (⊤ : Subgroup ↥D) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup D
  omega

private theorem pRank_le_add_one_of_isSylowOf_three {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {M L Q B : Subgroup G}
    (hp2 : p ≠ 2) (hBL : B ≤ normalizer (L : Set G)) (hBM : B ≤ M) (hLM : L ≤ M)
    (hQsyl : IsSylowOf 3 Q L) (hAut : ¬ p ∣ Nat.card (MulAut ↥Q))
    (hC : CFSG.Open.pRank p (M ⊓ centralizer (Q : Set G)) ≤ 1) :
    CFSG.Open.pRank p B ≤ CFSG.Open.pRank p L + 1 := by
  have hp := (Fact.out : p.Prime)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := B ⊔ L with hH
  have hBH : B ≤ H := le_sup_left
  have hLH : L ≤ H := le_sup_right
  have hHleM : H ≤ M := sup_le hBM hLM
  have hHnorm : H ≤ normalizer (L : Set G) :=
    sup_le hBL (le_normalizer : L ≤ normalizer (L : Set G))
  have hQH : Q ≤ H := hQsyl.le.trans hLH
  have : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHnorm
  have hFr : L ⊔ (H ⊓ normalizer (Q : Set G)) = H :=
    sup_inf_normalizer_eq_of_isSylowOf_three hLH hHnorm hQsyl hQH
  have hFr' : H ⊓ normalizer (Q : Set G) ⊔ L = H := by rw [sup_comm]; exact hFr
  have hC' : CFSG.Open.pRank p (H ⊓ centralizer (Q : Set G)) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt
      (le_inf (inf_le_left.trans hHleM) inf_le_right)).trans hC
  have hN1 : CFSG.Open.pRank p (H ⊓ normalizer (Q : Set G)) ≤ 1 :=
    pRank_inf_normalizer_le_one_of_action hAut hC'
  have hNle : H ⊓ normalizer (Q : Set G) ≤ H := inf_le_left
  let φ : ↥(H ⊓ normalizer (Q : Set G)) →* (↥H ⧸ L.subgroupOf H) :=
    (QuotientGroup.mk' (L.subgroupOf H)).comp (Subgroup.inclusion hNle)
  have hLker : (L.subgroupOf H).map (QuotientGroup.mk' (L.subgroupOf H)) = ⊥ :=
    (Subgroup.map_eq_bot_iff (L.subgroupOf H)).mpr
      (le_of_eq (QuotientGroup.ker_mk' (L.subgroupOf H)).symm)
  have hsup : (H ⊓ normalizer (Q : Set G)).subgroupOf H ⊔ L.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNle hLH, hFr', Subgroup.subgroupOf_self]
  have hNmap : ((H ⊓ normalizer (Q : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (L.subgroupOf H)) = ⊤ := by
    have h2 : ((H ⊓ normalizer (Q : Set G)).subgroupOf H ⊔ L.subgroupOf H).map
        (QuotientGroup.mk' (L.subgroupOf H)) = ⊤ := by
      rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rwa [Subgroup.map_sup, hLker, sup_bot_eq] at h2
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.inclusion_range hNle]
    exact hNmap
  have hN1' : CFSG.pRank p ↥(H ⊓ normalizer (Q : Set G)) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ←
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H ⊓ normalizer (Q : Set G))]
    exact hN1
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ L.subgroupOf H)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
      hp hp2 hN1' φ hφsurj
  have hineq := CFSG.AGLEmbedding.pRank_le_pRank_inf_add_pRank_map (p := p) hp
    (L.subgroupOf H) (B.subgroupOf H)
  rw [pRank_subgroupOf_eq_aux hBH] at hineq
  have hBsup : B.subgroupOf H ⊔ L.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBH hLH, show B ⊔ L = H from hH.symm,
      Subgroup.subgroupOf_self]
  have hmap : (B.subgroupOf H).map (QuotientGroup.mk' (L.subgroupOf H)) = ⊤ := by
    have h2 : (B.subgroupOf H ⊔ L.subgroupOf H).map
        (QuotientGroup.mk' (L.subgroupOf H)) = ⊤ := by
      rw [hBsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rwa [Subgroup.map_sup, hLker, sup_bot_eq] at h2
  have hfirst : CFSG.Open.pRank p (B.subgroupOf H ⊓ L.subgroupOf H) ≤
      CFSG.Open.pRank p L := by
    rw [← pRank_subgroupOf_eq_aux hLH]
    exact CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right
  have hsecond : CFSG.Open.pRank p
      ((B.subgroupOf H).map (QuotientGroup.mk' (L.subgroupOf H))) ≤ 1 := by
    rw [hmap]; exact hquot
  omega

private theorem isSylowOf_top_of_sylow_three {X : Type} [Group X] [Finite X] (S : Sylow 3 X) :
    IsSylowOf 3 (S : Subgroup X) ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
  exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩

private theorem rank_sylow_three_le_two_of_list880 {G : Type} [Group G] [Finite G]
    {L Q : Subgroup G}
    (hSyl : List880SylowThreeTwoGenerated) (hlist : List880 (Bar2 L))
    (hm3 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 2)
    (hQsyl : IsSylowOf 3 Q L) : Group.rank ↥Q ≤ 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O2 : Subgroup ↥L := CFSG.pCore 2 ↥L
  let π : ↥L →* Bar2 L := QuotientGroup.mk' O2
  let Qbar : Subgroup (Bar2 L) := (Q.subgroupOf L).map π
  obtain ⟨P₀, hP₀⟩ := hQsyl.exists_sylow_eq_subgroupOf
  have hP₀map : (P₀ : Subgroup ↥L).map π = Qbar := by rw [hP₀]
  have hQbar_sylow : IsSylowOf 3 Qbar ⊤ := by
    have h := isSylowOf_top_of_sylow_three
      (P₀.mapSurjective (QuotientGroup.mk'_surjective O2))
    rwa [Sylow.coe_mapSurjective, hP₀map] at h
  have hQbar_rank : Group.rank ↥Qbar ≤ 2 := hSyl (Bar2 L) hlist hm3 Qbar hQbar_sylow
  let f : ↥Q →* ↥Qbar :=
    { toFun := fun x => ⟨π ⟨(x : G), hQsyl.le x.2⟩,
        Subgroup.mem_map_of_mem π (show (⟨(x : G), hQsyl.le x.2⟩ : ↥L) ∈ Q.subgroupOf L from x.2)⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have hdisj : Q.subgroupOf L ⊓ O2 = ⊥ := by
    have h3 : IsPGroup 3 (Q.subgroupOf L) := hQsyl.isPGroup.comap_subtype
    have h2 : IsPGroup 2 O2 := CFSG.pCore_isPGroup
    exact disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ h3 h2)
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : π ⟨(a : G), hQsyl.le a.2⟩ = π ⟨(b : G), hQsyl.le b.2⟩ :=
      congrArg Subtype.val hab
    have hmem : (⟨(a : G), hQsyl.le a.2⟩ : ↥L) * (⟨(b : G), hQsyl.le b.2⟩ : ↥L)⁻¹ ∈
        Q.subgroupOf L ⊓ O2 := by
      refine ⟨(Q.subgroupOf L).mul_mem a.2 ((Q.subgroupOf L).inv_mem b.2), ?_⟩
      rw [show O2 = π.ker from (QuotientGroup.ker_mk' O2).symm]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h1, mul_inv_cancel])
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact Subtype.ext (mul_inv_eq_one.mp (Subtype.ext_iff.mp hmem))
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨(w : G), hw⟩, Subtype.ext hwy⟩
  have hrank := Group.rank_congr (MulEquiv.ofBijective f ⟨hinj, hsurj⟩)
  omega

theorem r881_of_r82
    {G : Type} [Group G] [Finite G] (D : Data G) (h82 : R82 D) : R881 D := by
  intro L P hset
  obtain ⟨hmem, hlist, hnot, -⟩ := hset
  obtain ⟨hsub, hperf, hquasi⟩ := hmem
  have h2bar : 2 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)) :=
    two_le_pRank_three_of_list880 hlist
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd
    (Y := L) (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2)] at h2bar
  refine le_antisymm ?_ h2bar
  by_contra hle
  have h3 : 2 < CFSG.Open.pRank 3 L := not_le.mp hle
  exact hnot (h82 L ⟨hsub, hperf, h3, Or.inl (isQuasisimple_of_open hquasi)⟩)

theorem r882_of_r881
    {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D) (h881 : R881 D) : R882 D := by
  intro L P h880
  obtain ⟨hL, hList, hnot, hP⟩ := h880
  by_cases hN : D.M ≤ Subgroup.normalizer (L : Set G)
  · exact Or.inl hN
  · right
    have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
    have h3σ : 3 ∉ D.sig := fun h => hnot (UC6S846.sp_of_mem_sig hSg hns h)
    have hm3M : CFSG.Open.pRank 3 D.M ≤ 3 := by
      by_contra h
      exact h3σ (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega))
    have hrL : CFSG.Open.pRank 3 L = 2 := h881 L P ⟨hL, hList, hnot, hP⟩
    have hZ : 3 ∣ Nat.card (Subgroup.center (UC22.Bar2 L)) := by
      by_contra hZ
      obtain ⟨E, hEL, hEel, hEcard⟩ :=
        CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
      rw [hrL] at hEcard
      have h4 := UC6S846.calCRankTwice D.M L hL hN 3 Nat.prime_three (by norm_num) hZ
        E hEL hEel 2 hEcard
      omega
    have hshape := list880_center_three_imp hList hZ
    have hle2 : (UC22.conjSetOf D.M L).ncard ≤ 2 :=
      ncard_conjSetOf_le_two_of_three_conj_rank
        (fun L₁ h1 L₂ h2 L₃ h3 h12 h13 h23 =>
          four_le_pRank_three_of_three_conj hL h1 h2 h3 h12 h13 h23 hshape) hm3M
    have hge2 : 2 ≤ (UC22.conjSetOf D.M L).ncard :=
      two_le_ncard_conjSetOf_of_not_le_normalizer hN
    have heq2 : (UC22.conjSetOf D.M L).ncard = 2 := by omega
    exact ⟨hshape, heq2⟩

theorem r883_of_inputs {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (h76 : R76Sig D) (h856 : R856 D) (h881 : R881 D) (h882 : R882 D)
    (hSL3 : List880NotSL3PiType) (hSyl : List880SylowThreeTwoGenerated) : R883 D := by
  intro L P hLP p hp
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ D.M := hLP.mem.1.le
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hLP.mem
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hp
  have hp3 : p ≠ 3 := fun h => hLP.notStrong (h ▸ hsp)
  have h5 : 5 ≤ p := hpp.five_le_of_ne_two_of_ne_three hp2 hp3
  have hge3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hp
  refine ⟨?_, by omega⟩
  set Q : Subgroup G := P ⊓ L
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q L :=
    hLP.sylow.inf_of_isSubnormal hLP.mem.1
  have hh881L : CFSG.Open.pRank 3 L = 2 := h881 L P hLP
  have hQ3 : IsPGroup 3 Q := hQsyl.isPGroup
  have hQrank3 : 2 ≤ CFSG.Open.pRank 3 Q := by
    rw [CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf Nat.prime_three hQsyl]
    omega
  have hQbar : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 2 := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd Nat.prime_three
      (by norm_num : (3 : ℕ) ≠ 2)]
    exact hh881L
  have hQrank : Group.rank ↥Q ≤ 2 :=
    rank_sylow_three_le_two_of_list880 hSyl hLP.list hQbar hQsyl
  have hAut : ¬ p ∣ Nat.card (MulAut ↥Q) :=
    not_dvd_card_mulAut_of_pGroup_three_of_rank_le_two hQ3 hQrank hpp h5
  have h76c : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p :=
    fun r hr E hEM hEel hEcard h0 hX =>
      h76 p hp hp2 hsp r hr E hEM hEel hEcard h0 hX
  have hC : CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (Q : Set G)) ≤ 1 := by
    by_contra h
    rw [not_le] at h
    have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (Q : Set G)) := by omega
    have hQle : Q ≤ D.M := inf_le_left.trans hLP.sylow.le
    have hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ D.M :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer
        hsp h76c hQle hQ3 hQrank3 h2
    rcases h856 L hLP.mem hh881L Q hQsyl hΓ with hstrong | hsl3
    · exact hLP.notStrong hstrong
    · exact hSL3 (Bar2 L) hLP.list hsl3
  have hBL : CFSG.LocalAnalysis.UniquenessCase.UC22.Opp p D.M ≤ normalizer (L : Set G) := by
    rcases h882 L P hLP with hnorm | ⟨-, hcard⟩
    · exact (CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le p D.M).trans hnorm
    · exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.opp_le_normalizer_of_ncard_conjSetOf_le_two
        hp2 (by
          rw [show CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf D.M L = MConjSet D.M L from rfl]
          exact le_of_eq hcard)
  have hBM : CFSG.LocalAnalysis.UniquenessCase.UC22.Opp p D.M ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le p D.M
  have hbound := pRank_le_add_one_of_isSylowOf_three hp2 hBL hBM hLM hQsyl hAut hC
  have hpM : CFSG.Open.pRank p (CFSG.LocalAnalysis.UniquenessCase.UC22.Opp p D.M) =
      CFSG.Open.pRank p D.M := by
    apply le_antisymm
    · exact CFSG.SectionRank.pRank_mono hpp.one_lt
        (CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le p D.M)
    · exact CFSG.LocalAnalysis.RankThreeUC.pRank_le_pElementSubgroup hpp D.M
  rw [hpM] at hbound
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
