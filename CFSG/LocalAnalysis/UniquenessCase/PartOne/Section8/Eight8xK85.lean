module

public import CFSG.Adapters.LieModelTorusRank
public import CFSG.ClassicalGroups.SpecialLinear.ComponentCartanRank
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicSubgroupCharacteristic
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.JStarGenericFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKLeaves2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKLeaves

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (Data DataExt Bar2 IsSpor UniqueMax calC pRank_bar2_eq_of_odd)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R76Sig)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsSU5)
open CFSG.LocalAnalysis.UniquenessCase.UC6 (R6_3)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
  (SigmaStd card_map_of_disjoint_ker exists_lift_pGroup isElemAbelian_of_disjoint_ker le_pRank'
    not_solvable_of_mem_calC sp_of_mem_sig)

@[expose] def imBar2 {G : Type} [Group G] (M A : Subgroup G) : Subgroup (Bar2 M) :=
  (A.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))

theorem sig_facts_of_set880 {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (h883 : R883 D) {L P : Subgroup G} (hset : Set880 D L P) {p : ℕ} (hp : p ∈ D.sig) :
    p.Prime ∧ 5 ≤ p ∧ 3 ≤ CFSG.Open.pRank p D.M ∧ 2 ≤ CFSG.Open.pRank p L ∧
      CFSG.Open.pRank p D.M - 1 ≤ CFSG.Open.pRank p L := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hset.mem
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hset.notStrong (sp_of_mem_sig hSg hns hp)
  have h5 : 5 ≤ p := by
    have h2 := hpp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hpp (by norm_num)
    omega
  obtain ⟨h1, h2⟩ := h883 L P hset p hp
  exact ⟨hpp, h5, hSg.three_le p hp, by omega, h1⟩

theorem normalizer_of_set880_of_two_le_pRank {G : Type} [Group G] [Finite G] (D : Data G)
    (h882 : R882 D) (hIns : List880PRankInspection) {L P : Subgroup G} (hset : Set880 D L P)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h2 : 2 ≤ CFSG.Open.pRank p L) :
    D.M ≤ normalizer (L : Set G) := by
  rcases h882 L P hset with hN | ⟨hcov, -⟩
  · exact hN
  · exfalso
    have hr : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) := by
      rw [pRank_bar2_eq_of_odd hp (by omega)]
      exact h2
    exact (hIns (Bar2 L) hset.list p hp h5 hr).1 hcov

private theorem k85a_mem_pCore_iff {G : Type} [Group G] {L : Subgroup G} (l : ↥L) :
    l ∈ CFSG.pCore 2 ↥L ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 L := by
  constructor
  · intro hl
    exact ⟨l, hl, rfl⟩
  · rintro ⟨n, hn, hnl⟩
    have hnl' : n = l := Subtype.ext hnl
    rwa [← hnl']

theorem exists_bar2_embedding {G : Type} [Group G] [Finite G] {L M : Subgroup G} (hLM : L ≤ M)
    (hN : M ≤ normalizer (L : Set G)) :
    ∃ ι : Bar2 L →* Bar2 M, Function.Injective ι ∧ ι.range.Normal ∧
      ∀ x : ↥L, ι (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hLM x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOle : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM)
      (hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  let O_L : Subgroup ↥L := CFSG.pCore 2 ↥L
  let O_M : Subgroup ↥M := CFSG.pCore 2 ↥M
  let j : ↥L →* ↥M := Subgroup.inclusion hLM
  let f : ↥L →* Bar2 M := (QuotientGroup.mk' O_M).comp j
  have hker : O_L ≤ f.ker := by
    intro x hx
    have hxO : (x : G) ∈ CFSG.Open.pCoreOf 2 L := (k85a_mem_pCore_iff x).mp hx
    have hxM : ((j x : ↥M) : G) ∈ CFSG.Open.pCoreOf 2 M := by
      simpa [j] using hOle hxO
    have hjO : j x ∈ O_M := (k85a_mem_pCore_iff (j x)).mpr hxM
    show f x = 1
    show QuotientGroup.mk' O_M (j x) = 1
    exact (QuotientGroup.eq_one_iff (j x)).mpr hjO
  have hcomap : f.ker = O_M.comap j := by
    show ((QuotientGroup.mk' O_M).comp j).ker = O_M.comap j
    rw [← MonoidHom.comap_ker (QuotientGroup.mk' O_M) j, QuotientGroup.ker_mk']
  have hker_eq : O_L = f.ker := by
    refine le_antisymm hker ?_
    rw [hcomap]
    exact le_sSup ⟨inferInstance,
      CFSG.pCore_isPGroup.comap_of_injective j (Subgroup.inclusion_injective hLM)⟩
  let ι : Bar2 L →* Bar2 M := QuotientGroup.lift O_L f hker
  have hcompat : ∀ x : ↥L, ι (QuotientGroup.mk' O_L x) =
      QuotientGroup.mk' O_M (Subgroup.inclusion hLM x) :=
    fun x => DFunLike.congr_fun (QuotientGroup.lift_comp_mk' (N := O_L) (φ := f) hker) x
  have hrange : ι.range = (L.subgroupOf M).map (QuotientGroup.mk' O_M) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O_L z
      refine Subgroup.mem_map.mpr ⟨j x, ?_, (hcompat x).symm⟩
      rw [Subgroup.mem_subgroupOf]
      exact x.2
    · rintro ⟨m, hm, rfl⟩
      let x : ↥L := ⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩
      refine ⟨QuotientGroup.mk' O_L x, ?_⟩
      rw [hcompat]
      have hjm : j x = m := Subtype.ext rfl
      rw [hjm]
  refine ⟨ι, ?_, ?_, hcompat⟩
  · exact (QuotientGroup.injective_lift_iff O_L f hker).mpr hker_eq
  · rw [hrange]
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hN).map
      (QuotientGroup.mk' O_M) (QuotientGroup.mk'_surjective O_M)

private theorem k85a_factorization_three_bar2 {G : Type} [Group G] [Finite G] {L : Subgroup G} :
    (Nat.card ↥L).factorization 3 = (Nat.card (Bar2 L)).factorization 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hcardmul : Nat.card O * Nat.card (Bar2 L) = Nat.card ↥L := by
    have hh := Subgroup.card_ker_mul_card_of_surjective (f := QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective O)
    simpa [O, Bar2, QuotientGroup.ker_mk'] using hh
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  have h3O : ¬ 3 ∣ Nat.card O := by
    rw [hn]
    intro h3
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hfacO : (Nat.card O).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3O
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card (Bar2 L) ≠ 0 := Nat.card_pos.ne'
  rw [← hcardmul, Nat.factorization_mul hO0 hB0, Finsupp.add_apply, hfacO, zero_add]

theorem isSylowOf_imBar2 {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    (hQ : IsSylowOf 3 Q L) : IsSylowOf 3 (imBar2 L Q) (⊤ : Subgroup (Bar2 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQL : Q ≤ L := hQ.le
  have hQp : IsPGroup 3 Q := hQ.isPGroup
  have hdisj : Disjoint (Q.subgroupOf L) (CFSG.pCore 2 ↥L) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hQp.comap_subtype CFSG.pCore_isPGroup
  have hcard : Nat.card (imBar2 L Q) = Nat.card Q := by
    have hdisj' : Disjoint (Q.subgroupOf L) (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
      rwa [QuotientGroup.ker_mk']
    have h1 : Nat.card (imBar2 L Q) = Nat.card (Q.subgroupOf L) :=
      card_map_of_disjoint_ker (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (Q.subgroupOf L) hdisj'
    have h2 : Nat.card (Q.subgroupOf L) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
    exact h1.trans h2
  have hfac := k85a_factorization_three_bar2 (L := L)
  have hQcard : Nat.card Q = 3 ^ (Nat.card (⊤ : Subgroup (Bar2 L))).factorization 3 := by
    rw [Subgroup.card_top, ← hfac]
    exact hQ.card_eq
  exact CFSG.ABGLocalTools.isSylowOf_of_card le_top (hcard.trans hQcard)

private theorem k85a_centralizer_subgroupOf_map {G : Type} [Group G] {M A : Subgroup G}
    (hAM : A ≤ M) :
    (Subgroup.centralizer (A.subgroupOf M : Set ↥M)).map M.subtype =
      M ⊓ Subgroup.centralizer (A : Set G) := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m.2, ?_⟩
    intro a ha
    have hy : (⟨a, hAM ha⟩ : ↥M) ∈ A.subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      exact ha
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hm) ⟨a, hAM ha⟩ hy)
  · rintro ⟨hgM, hgc⟩
    refine ⟨⟨g, hgM⟩, ?_, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hgc) (y : G) (Subgroup.mem_subgroupOf.mp hy)

theorem pRank_centralizer_imBar2 {G : Type} [Group G] [Finite G] {M A : Subgroup G} (hAM : A ≤ M)
    (hA : IsPGroup 3 A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (centralizer ((imBar2 M A : Subgroup (Bar2 M)) : Set (Bar2 M))) =
      CFSG.Open.pRank p (M ⊓ centralizer (A : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥M := CFSG.pCore 2 ↥M
  have : N.Normal := CFSG.pCore_normal
  let E : Subgroup ↥M := A.subgroupOf M
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
  have hs : ¬ 3 ∣ Nat.card N := by
    rw [hn]
    intro h3
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hp' : ¬ p ∣ Nat.card N := by
    rw [hn]
    intro hpd
    have hp2' : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow hp hpd)
    exact hp2 hp2'
  have hE : IsPGroup 3 E := hA.comap_subtype (K := M)
  have hstep := CFSG.GroupTheory.CoprimeTransport.pRank_centralizer_map_mk_eq
    (N := N) (s := 3) (p := p) hs hp' hE
  have hmap := k85a_centralizer_subgroupOf_map hAM
  have hsub := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp M.subtype
    M.subtype_injective (Subgroup.centralizer (E : Set ↥M))
  change CFSG.Open.pRank p (Subgroup.centralizer
      (((A.subgroupOf M).map (QuotientGroup.mk' N) : Subgroup (Bar2 M)) : Set (Bar2 M))) =
    CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G))
  rw [hstep, ← hsub, hmap]

private theorem k85b_disjoint {G : Type} [Group G] {L A : Subgroup G} (hA : IsPGroup 3 A) :
    Disjoint (A.subgroupOf L) (CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.disjoint_of_ne 3 2 (by norm_num) (A.subgroupOf L) (CFSG.pCore 2 ↥L)
    (hA.comap_subtype (K := L)) CFSG.pCore_isPGroup

private theorem k85b_orderOf_mk {G : Type} [Group G] [Finite G] {L A : Subgroup G}
    (hAL : A ≤ L) (hA : IsPGroup 3 A) {x : G} (hx : x ∈ A) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨x, hAL hx⟩ : ↥L)) = orderOf x := by
  have hdisj : Disjoint (A.subgroupOf L) (CFSG.pCore 2 ↥L) := k85b_disjoint hA
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (A.subgroupOf L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    exact Subtype.ext
      (Subgroup.disjoint_def.1 hdisj w.2 ((QuotientGroup.eq_one_iff (w : ↥L)).1 hw))
  let z : ↥(A.subgroupOf L) := ⟨⟨x, hAL hx⟩, hx⟩
  have h1 : orderOf ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (A.subgroupOf L).subtype z) =
      orderOf z := orderOf_injective _ hinj z
  have h2 : orderOf z = orderOf x := by
    rw [Subgroup.orderOf_mk (⟨x, hAL hx⟩ : ↥L) hx, Subgroup.orderOf_mk x (hAL hx)]
  change orderOf ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (A.subgroupOf L).subtype z) =
    orderOf x
  exact h1.trans h2

private theorem k85b_image {G : Type} [Group G] {L M A : Subgroup G} (hLM : L ≤ M)
    (hAL : A ≤ L) (ι : Bar2 L →* Bar2 M)
    (hι : ∀ x : ↥L, ι (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hLM x)) :
    (imBar2 L A).map ι = imBar2 M A := by
  unfold imBar2
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hz
    exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hLM a, ha, (hι a).symm⟩
  · rintro ⟨b, hb, rfl⟩
    have hbA : (b : G) ∈ A := hb
    have hbL : (b : G) ∈ L := hAL hbA
    refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨(b : G), hbL⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.2 ⟨⟨(b : G), hbL⟩, hbA, rfl⟩
    · rw [hι]
      rfl

theorem pRank_facts_of_centralizer_ranks {G : Type} [Group G] [Finite G] {L M Q : Subgroup G}
    (hLM : L ≤ M) (hQL : Q ≤ L) (ι : Bar2 L →* Bar2 M)
    (hι : ∀ x : ↥L, ι (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hLM x))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : 0 < CFSG.Open.pRank p
      (centralizer ((ι '' (imBar2 L Q : Set (Bar2 L)) : Set (Bar2 M)))))
    (h2 : ∀ e ∈ imBar2 L Q, orderOf e = 3 →
      2 ≤ CFSG.Open.pRank p (centralizer ({ι e} : Set (Bar2 M)))) :
    ∀ E : Subgroup G, E ≤ Q → IsElemAbelian 3 E → Nat.card E = 9 →
      0 < CFSG.Open.pRank p (M ⊓ centralizer (E : Set G)) ∧
        ∀ X : Subgroup G, X ≤ E → Nat.card X = 3 →
          1 < CFSG.Open.pRank p (M ⊓ normalizer (X : Set G)) := by
  intro E hEQ hEel hEcard
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hEM : E ≤ M := hEQ.trans (hQL.trans hLM)
  have hEpg : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
  have hsub : (imBar2 M E : Set (Bar2 M)) ⊆ (ι '' (imBar2 L Q : Set (Bar2 L))) := by
    have hle : imBar2 M E ≤ (imBar2 L Q).map ι := by
      rw [k85b_image hLM hQL ι hι]
      unfold imBar2
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono M hEQ)
    intro y hy
    exact hle hy
  have hcentral : centralizer ((ι '' (imBar2 L Q : Set (Bar2 L))) : Set (Bar2 M)) ≤
      centralizer ((imBar2 M E : Subgroup (Bar2 M)) : Set (Bar2 M)) :=
    Subgroup.centralizer_le hsub
  refine ⟨?_, ?_⟩
  · have hpos : 0 < CFSG.Open.pRank p
        (centralizer ((imBar2 M E : Subgroup (Bar2 M)) : Set (Bar2 M))) :=
      h1.trans_le (CFSG.SectionRank.pRank_mono hp.one_lt hcentral)
    exact (pRank_centralizer_imBar2 hEM hEpg hp hp2) ▸ hpos
  · intro X hXE hXcard
    have hXQ : X ≤ Q := hXE.trans hEQ
    have hXL : X ≤ L := hXQ.trans hQL
    have hXM : X ≤ M := hXL.trans hLM
    have hXpg : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [hXcard]; norm_num)
    have : Nontrivial ↥X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hXcard]; norm_num)
    obtain ⟨xG, hxGX, hxG1⟩ : ∃ xG : G, xG ∈ X ∧ xG ≠ 1 := by
      obtain ⟨g, hg1⟩ := exists_ne (1 : ↥X)
      exact ⟨(g : G), g.2, fun h => hg1 (Subtype.ext h)⟩
    have hgQ : xG ∈ Q := hXQ hxGX
    have hgL : xG ∈ L := hQL hgQ
    have hdvd : orderOf xG ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard X hxGX
      rwa [hXcard] at this
    have hne1 : orderOf xG ≠ 1 := fun h => hxG1 (orderOf_eq_one_iff.mp h)
    have hg3 : orderOf xG = 3 := by
      rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf xG) hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hXzp : X = Subgroup.zpowers xG := by
      have hcard : Nat.card X ≤ Nat.card (Subgroup.zpowers xG) :=
        le_of_eq (hXcard.trans (hg3.symm.trans (Nat.card_zpowers xG).symm))
      exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxGX) hcard).symm
    have hXsub : X.subgroupOf L = Subgroup.zpowers (⟨xG, hgL⟩ : ↥L) := by
      rw [hXzp]
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    let e : Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨xG, hgL⟩
    have he_mem : e ∈ imBar2 L Q := by
      rw [imBar2]
      exact Subgroup.mem_map.2 ⟨⟨xG, hgL⟩, hgQ, rfl⟩
    have he_ord : orderOf e = 3 := by
      change orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨xG, hgL⟩) = 3
      rw [k85b_orderOf_mk hXL hXpg hxGX, hg3]
    have hImL : imBar2 L X = Subgroup.zpowers e := by
      unfold imBar2
      rw [hXsub, MonoidHom.map_zpowers]
    have hImM : imBar2 M X = Subgroup.zpowers (ι e) := by
      rw [← k85b_image hLM hXL ι hι, hImL, MonoidHom.map_zpowers]
    have hle : imBar2 M X ≤ Subgroup.zpowers (ι e) := hImM.le
    have hcent : centralizer ({ι e} : Set (Bar2 M)) ≤
        centralizer ((imBar2 M X : Subgroup (Bar2 M)) : Set (Bar2 M)) := by
      calc centralizer ({ι e} : Set (Bar2 M))
          = centralizer (Subgroup.zpowers (ι e)) := by
            rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        _ ≤ centralizer ((imBar2 M X : Subgroup (Bar2 M)) : Set (Bar2 M)) :=
            Subgroup.centralizer_le hle
    have h2le : 2 ≤ CFSG.Open.pRank p
        (centralizer ((imBar2 M X : Subgroup (Bar2 M)) : Set (Bar2 M))) :=
      (h2 e he_mem he_ord).trans (CFSG.SectionRank.pRank_mono hp.one_lt hcent)
    have h2central : 2 ≤ CFSG.Open.pRank p (M ⊓ centralizer (X : Set G)) :=
      (pRank_centralizer_imBar2 hXM hXpg hp hp2) ▸ h2le
    have hmono : M ⊓ centralizer (X : Set G) ≤ M ⊓ normalizer (X : Set G) :=
      inf_le_inf le_rfl (Subgroup.centralizer_le_normalizer (X : Set G))
    exact lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2)
      (h2central.trans (CFSG.SectionRank.pRank_mono hp.one_lt hmono))

theorem exists_e9_of_imBar2 {G : Type} [Group G] [Finite G] {L Q : Subgroup G} (hQL : Q ≤ L)
    (hQ : IsPGroup 3 Q)
    (h : ∀ e ∈ imBar2 L Q, orderOf e = 3 →
      ∃ E : Subgroup (Bar2 L), e ∈ E ∧ E ≤ imBar2 L Q ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∀ x ∈ Q, orderOf x = 3 →
      ∃ E : Subgroup G, x ∈ E ∧ E ≤ Q ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  intro x hxQ hx3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxL : x ∈ L := hQL hxQ
  let e : Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩
  have he_mem : e ∈ imBar2 L Q := by
    rw [imBar2]
    exact Subgroup.mem_map.2 ⟨⟨x, hxL⟩, hxQ, rfl⟩
  have he_ord : orderOf e = 3 := by
    change orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩) = 3
    rw [k85b_orderOf_mk hQL hQ hxQ, hx3]
  obtain ⟨E', heE', hE'Q, hE'ab, hE'card⟩ := h e he_mem he_ord
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let E₀ : Subgroup ↥L := (Q.subgroupOf L) ⊓ E'.comap π
  have hdisj : Disjoint E₀ π.ker := by
    rw [show π.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _]
    exact Disjoint.mono_left inf_le_left (k85b_disjoint hQ)
  have hmap : E₀.map π = E' := by
    apply le_antisymm
    · rintro y ⟨l, hl, rfl⟩
      exact hl.2
    · intro y hy
      obtain ⟨l, hlQ, hl⟩ := Subgroup.mem_map.1 (hE'Q hy)
      refine Subgroup.mem_map.2 ⟨l, ⟨hlQ, ?_⟩, hl⟩
      show (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) l ∈ E'
      exact hl.symm ▸ hy
  have hcard : Nat.card E₀ = 9 := by
    rw [← card_map_of_disjoint_ker π E₀ hdisj, hmap, hE'card]
  have hab : IsElemAbelian 3 E₀ :=
    isElemAbelian_of_disjoint_ker π E₀ hdisj (hmap.symm ▸ hE'ab)
  have hxE₀ : (⟨x, hxL⟩ : ↥L) ∈ E₀ := by
    exact ⟨hxQ, heE'⟩
  refine ⟨E₀.map L.subtype, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map.2 ⟨⟨x, hxL⟩, hxE₀, rfl⟩
  · rintro y ⟨l, hl, rfl⟩
    exact hl.1
  · exact CFSG.SectionRank.isElemAbelian_map hab L.subtype
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hcard]

open CFSG.LocalAnalysis.RankThreeUC in
private theorem k85c_cyclic {G : Type} [Group G] [Finite G] {M Q Q' : Subgroup G}
    (hE9contain : ∀ x ∈ Q, orderOf x = 3 →
      ∃ E : Subgroup G, x ∈ E ∧ E ≤ Q ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hE9 : ∀ E : Subgroup G, E ≤ Q → IsElemAbelian 3 E → Nat.card E = 9 →
      rankThreeGamma 1 3 E ≤ M)
    (hcyc : IsCyclic Q') (hQ'Q : Q' ≤ Q) (hQ'rank : 1 ≤ CFSG.Open.pRank 3 Q') :
    Subgroup.normalizer (Q' : Set G) ≤ M := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxQ', hxord⟩ :=
    CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank Nat.prime_three hQ'rank
  have hxQ : x ∈ Q := hQ'Q hxQ'
  have hx1 : x ≠ 1 := by
    intro h
    rw [h] at hxord
    simp at hxord
  obtain ⟨E, hxE, hEQ, hEel, hEcard⟩ := hE9contain x hxQ hxord
  have hxpowE : Subgroup.zpowers x ≤ E := Subgroup.zpowers_le.mpr hxE
  have hzcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hxord]
  have hzpowrank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x) := by
    have hea : IsElemAbelian 3 (Subgroup.zpowers x) :=
      CFSG.GroupTheory.isElemAbelian_of_card_prime hzcard
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num : 1 < 3) le_rfl hea
      (by rw [hzcard]; norm_num)
  calc Subgroup.normalizer (Q' : Set G)
      ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
        CFSG.GorensteinWalter.normalizer_le_normalizer_of_le_cyclic hcyc
          (Subgroup.zpowers_le.mpr hxQ')
    _ ≤ CFSG.Open.rankThreeGamma 1 3 E :=
        CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hxpowE hzpowrank
    _ ≤ M := hE9 E hEQ hEel hEcard

open CFSG.LocalAnalysis.RankThreeUC in
private theorem k85c_noncyclic {G : Type} [Group G] [Finite G] {M Q Q' : Subgroup G}
    (hQp : IsPGroup 3 Q) (hQM : Q ≤ M)
    (hE9 : ∀ E : Subgroup G, E ≤ Q → IsElemAbelian 3 E → Nat.card E = 9 →
      rankThreeGamma 1 3 E ≤ M)
    (h63 : ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 →
      rankThreeGamma 1 3 E ≤ M → UniqueMax M E)
    (hcyc : ¬ IsCyclic Q') (hQ'Q : Q' ≤ Q) :
    Subgroup.normalizer (Q' : Set G) ≤ M := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ'p : IsPGroup 3 Q' := hQp.to_le hQ'Q
  have : Fact (IsPGroup 3 Q') := ⟨hQ'p⟩
  obtain ⟨E₀, -, hE₀card, hE₀el⟩ :=
    CFSG.lemma_4_5_a (R := Q') (p := 3) (by norm_num : (3 : ℕ) ≠ 2) hcyc
  let E : Subgroup G := E₀.map Q'.subtype
  have hEQ' : E ≤ Q' := Subgroup.map_subtype_le E₀
  have hEel : IsElemAbelian 3 E :=
    CFSG.SectionRank.isElemAbelian_map
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.2 hE₀el) Q'.subtype
  have hEcard : Nat.card E = 9 := by
    change Nat.card (E₀.map Q'.subtype) = 9
    rw [Subgroup.card_map_of_injective Q'.subtype_injective, hE₀card]
    norm_num
  have hE9M : rankThreeGamma 1 3 E ≤ M := hE9 E (hEQ'.trans hQ'Q) hEel hEcard
  have hEM : E ≤ M := (hEQ'.trans hQ'Q).trans hQM
  have hU : CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E = {M} :=
    h63 E hEM hEel hEcard hE9M
  have hMmax : rankThreeIsMaxTwoLocal M := by
    have hmem : M ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E := by
      rw [hU]
      exact Set.mem_singleton M
    exact hmem.1
  have hEunique : E ∈ uniqueSet M := by
    refine mem_uniqueSet_of_forall hMmax hEM ?_
    intro H hH hEH
    have hmem : H ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calMOf E := ⟨hH, hEH⟩
    rw [hU] at hmem
    simpa using hmem
  have hQ'min : Q' ≤ M := hQ'Q.trans hQM
  have hQ'unique : Q' ∈ uniqueSet M :=
    mem_uniqueSet_of_le hEunique hEQ' hQ'min
  exact normalizer_le_of_mem_uniqueSet hMmax hQ'unique

theorem rankThreeGamma_le_of_forall_e9 {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
    (hQp : IsPGroup 3 Q) (hQM : Q ≤ M)
    (hE9contain : ∀ x ∈ Q, orderOf x = 3 →
      ∃ E : Subgroup G, x ∈ E ∧ E ≤ Q ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hE9 : ∀ E : Subgroup G, E ≤ Q → IsElemAbelian 3 E → Nat.card E = 9 →
      rankThreeGamma 1 3 E ≤ M)
    (h63 : ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 →
      rankThreeGamma 1 3 E ≤ M → UniqueMax M E) :
    rankThreeGamma 1 3 Q ≤ M := by
  classical
  unfold CFSG.Open.rankThreeGamma
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro Q' hQ'Q hQ'rank
  by_cases hcyc : IsCyclic Q'
  · exact k85c_cyclic hE9contain hE9 hcyc hQ'Q hQ'rank
  · exact k85c_noncyclic hQp hQM hE9 h63 hcyc hQ'Q

theorem not_rankThreeGamma_le_of_set880 {G : Type} [Group G] [Finite G] (D : Data G)
    (h856 : R856 D) (h881 : R881 D) (hSL3 : List880NotSL3PiType) {L P : Subgroup G}
    (hset : Set880 D L P) (hnorm : D.M ≤ normalizer (L : Set G)) :
    ¬ rankThreeGamma 1 3 (P ⊓ L) ≤ D.M := by
  intro hΓ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hset.mem.1
  have hQ : IsSylowOf 3 (P ⊓ L) L := hset.sylow.inf_of_le_normalizer hLM hnorm
  rcases h856 L hset.mem (h881 L P hset) (P ⊓ L) hQ hΓ with hs | hsl
  · exact hset.notStrong hs
  · exact hSL3 _ hset.list hsl

private theorem two_pow_mod_fifteen (m : ℕ) : 2 ^ m % 15 = 2 ^ (m % 4) % 15 := by
  conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem exists_prime_ge_seven_dvd_two_pow_add_one (m : ℕ) (hm : 2 < m) (h5 : 5 ∣ 2 ^ m + 1)
    (h25 : ¬ 25 ∣ 2 ^ m + 1) : ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ m + 1 ∧ 7 ≤ r := by
  obtain ⟨k, hk⟩ := h5
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hk1 : k ≠ 1 := by omega
  have hk5 : ¬ 5 ∣ k := fun ⟨j, hj⟩ => h25 ⟨j, by rw [hk, hj]; omega⟩
  have hmod := two_pow_mod_fifteen m
  have hm4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hev : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have h3 : ¬ 3 ∣ 2 ^ m + 1 := by
    interval_cases h : m % 4 <;> norm_num at hmod <;> omega
  refine ⟨k.minFac, Nat.minFac_prime hk1, ?_, ?_⟩
  · rw [hk]
    exact dvd_mul_of_dvd_right (Nat.minFac_dvd k) 5
  · have hp := Nat.minFac_prime hk1
    have hdk : k.minFac ∣ 2 ^ m + 1 := by
      rw [hk]
      exact dvd_mul_of_dvd_right (Nat.minFac_dvd k) 5
    by_contra hlt
    have h2 := hp.two_le
    interval_cases h : k.minFac
    · omega
    · exact h3 hdk
    · omega
    · exact hk5 (h ▸ Nat.minFac_dvd k)
    · omega

theorem exists_sigma_prime_of_u5 {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    {L : Subgroup G} (hL : L ∈ calC D.M) {m : ℕ} (hm : 2 < m) (hSU : IsSU5 (Bar2 L) m)
    (hZ : Nat.card (center (Bar2 L)) = 1) (h5 : 5 ∣ 2 ^ m + 1) (h25 : ¬ 25 ∣ 2 ^ m + 1) :
    ∃ r : ℕ, r.Prime ∧ 7 ≤ r ∧ r ∣ 2 ^ m + 1 ∧ r ∈ D.sig ∧ IsStronglyPEmbedded r D.M := by
  classical
  obtain ⟨r, hr, hrd, hr7⟩ := exists_prime_ge_seven_dvd_two_pow_add_one m hm h5 h25
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hr5 : ¬ r ∣ 5 := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h
    omega
  have h4q : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup (Bar2 L ⧸ center (Bar2 L))) :=
    CFSG.Blueprint.LieModel.le_pRank_psu_of_dvd hSU.2 hr hrd (by norm_num) (Or.inr hr5)
  have h4b : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup (Bar2 L)) := by
    rw [CFSG.ClassicalGroups.SpecialLinear.pRank_top_eq_of_mulEquiv_center_quotient hr
      (MulEquiv.refl _) (by rw [hZ]; exact hr.not_dvd_one)]
    exact h4q
  obtain ⟨S⟩ : Nonempty (Sylow r (Bar2 L)) := inferInstance
  obtain ⟨Eb, -, hEbel, hEbcard⟩ :=
    CFSG.AGLEmbedding.exists_elem_le_sylow_of_le_pRank (p := r) (k := 4) h4b S
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  obtain ⟨Q, -, hQmap, hQdisj⟩ :=
    exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hr hr2 Eb hEbel.isPGroup
  have hel : IsElemAbelian r (Q.map L.subtype) :=
    (isElemAbelian_of_disjoint_ker π Q hQdisj (by rw [hQmap]; exact hEbel)).map _
  have hcard : Nat.card (Q.map L.subtype) = r ^ 4 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      ← card_map_of_disjoint_ker π Q hQdisj, hQmap, hEbcard]
  have hLM : L ≤ D.M := hL.1.le
  have h4M : 4 ≤ CFSG.Open.pRank r D.M :=
    le_pRank' hr ((Subgroup.map_subtype_le Q).trans hLM) hel hcard
  have hmem : r ∈ D.sig := hSg.four_mem r hr hr2 h4M
  exact ⟨r, hr, hr7, hrd, hmem, sp_of_mem_sig hSg (not_solvable_of_mem_calC hL) hmem⟩

theorem sig_eq_five_of_isSpor_j2 {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (hExt : DataExt D) (h883 : R883 D) (hJ2 : J2FivePRank) {L P : Subgroup G}
    (hset : Set880 D L P) (hJ : IsSpor (Bar2 L) .J2) : D.sig = {5} ∧ evenRank G = 3 := by
  obtain ⟨h52, hlt⟩ := hJ2 (Bar2 L) hJ
  have hfive : ∀ q ∈ D.sig, q = 5 := by
    intro q hq
    obtain ⟨hqp, hq5, -, hq2, -⟩ := sig_facts_of_set880 D hSg h883 hset hq
    by_contra hne
    have hr : CFSG.Open.pRank q (⊤ : Subgroup (Bar2 L)) ≤ 1 := hlt q hqp hq5 hne
    rw [pRank_bar2_eq_of_odd hqp (by omega)] at hr
    omega
  obtain ⟨q₀, hq₀⟩ := hSg.nonempty
  have hq₀5 : q₀ = 5 := hfive q₀ hq₀
  have h5mem : 5 ∈ D.sig := hq₀5 ▸ hq₀
  have hsig : D.sig = {5} := by
    ext q
    exact ⟨fun hq => hfive q hq, fun hq => by rw [Set.mem_singleton_iff.mp hq]; exact h5mem⟩
  refine ⟨hsig, ?_⟩
  obtain ⟨-, -, -, hL5, hM5⟩ := sig_facts_of_set880 D hSg h883 hset h5mem
  have h5L : CFSG.Open.pRank 5 L = 2 := by
    rw [← pRank_bar2_eq_of_odd (Y := L) (by norm_num) (by norm_num)]
    exact h52
  have h3 : 3 ≤ evenRank G := D.standing.rank
  by_contra hne
  have h4 := hExt.four_le (by omega) 5 h5mem
  omega

theorem false_of_set880_not_isSpor_j2 {G : Type} [Group G] [Finite G] (D : Data G)
    (hSg : SigmaStd D) (h63 : R6_3 D) (h76 : R76Sig D) (h856 : R856 D) (h881 : R881 D)
    (h882 : R882 D) (h883 : R883 D) (hSL3 : List880NotSL3PiType)
    (hIns : List880PRankInspection) (hE9 : List880ThreeInE9) (hRk : List880CentralizerRanks)
    {L P : Subgroup G} (hset : Set880 D L P) (hJ : ¬ IsSpor (Bar2 L) .J2) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hset.mem.1
  obtain ⟨p, hpsig, hexc⟩ : ∃ p ∈ D.sig, ¬ List880CRExc (Bar2 L) p := by
    obtain ⟨p₀, hp₀⟩ := hSg.nonempty
    by_cases h : List880CRExc (Bar2 L) p₀
    · obtain ⟨-, m, hm2, hm, hcen, h5, h25⟩ := h
      obtain ⟨r, -, hr7, -, hrsig, -⟩ :=
        exists_sigma_prime_of_u5 D hSg hset.mem hm2 hm hcen h5 h25
      exact ⟨r, hrsig, fun hx => by have := hx.1; omega⟩
    · exact ⟨p₀, hp₀, h⟩
  obtain ⟨hpp, h5, hM3, hL2, -⟩ := sig_facts_of_set880 D hSg h883 hset hpsig
  have hp2 : p ≠ 2 := (D.sig_prime p hpsig).2
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hset.mem
  have hnorm : D.M ≤ normalizer (L : Set G) :=
    normalizer_of_set880_of_two_le_pRank D h882 hIns hset hpp h5 hL2
  obtain ⟨ι, hιinj, hιnorm, hιcompat⟩ := exists_bar2_embedding hLM hnorm
  have hQsyl : IsSylowOf 3 (P ⊓ L) L := hset.sylow.inf_of_le_normalizer hLM hnorm
  have hSsyl : IsSylowOf 3 (imBar2 L (P ⊓ L)) (⊤ : Subgroup (Bar2 L)) := isSylowOf_imBar2 hQsyl
  have h3rank : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 2 := by
    rw [pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)]
    exact h881 L P hset
  have hrk1 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) := by
    rw [pRank_bar2_eq_of_odd hpp hp2]
    exact hL2
  have hrk3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 D.M)) := by
    rw [pRank_bar2_eq_of_odd hpp hp2]
    exact hM3
  obtain ⟨hc1, hc2⟩ := hRk (Bar2 L) (Bar2 D.M) ι hιinj hιnorm hset.list hJ h3rank p hpp h5 hrk1
    hrk3 hexc (imBar2 L (P ⊓ L)) hSsyl
  have hfacts := pRank_facts_of_centralizer_ranks hLM (inf_le_right : P ⊓ L ≤ L) ι hιcompat hpp
    hp2 hc1 hc2
  have hsp : IsStronglyPEmbedded p D.M := sp_of_mem_sig hSg hns hpsig
  have hΓE : ∀ E : Subgroup G, E ≤ P ⊓ L → IsElemAbelian 3 E → Nat.card E = 9 →
      rankThreeGamma 1 3 E ≤ D.M := by
    intro E hEQ hEel hEcard
    have hEM : E ≤ D.M := hEQ.trans (inf_le_right.trans hLM)
    obtain ⟨hf1, hf2⟩ := hfacts E hEQ hEel hEcard
    exact h76 p hpsig hp2 hsp 3 Nat.prime_three E hEM hEel (by rw [hEcard]; norm_num) hf1
      (fun X hXE hXcard => hf2 X hXE hXcard)
  have hQp : IsPGroup 3 ↥(P ⊓ L) := ((CFSG.ABGLocalTools.isSylowOf_iff).1 hQsyl).2.1
  have hE9contain := exists_e9_of_imBar2 (inf_le_right : P ⊓ L ≤ L) hQp
    (fun e he he3 => hE9 (Bar2 L) hset.list h3rank (imBar2 L (P ⊓ L)) hSsyl e he he3)
  have hΓ : rankThreeGamma 1 3 (P ⊓ L) ≤ D.M :=
    rankThreeGamma_le_of_forall_e9 hQp (inf_le_right.trans hLM) hE9contain hΓE
      (fun E hEM hEel hEcard hΓ => h63 3 Nat.prime_three (by norm_num) E hEM hEel
        (by rw [hEcard]; norm_num) hΓ)
  exact not_rankThreeGamma_le_of_set880 D h856 h881 hSL3 hset hnorm hΓ

theorem r885_of_inputs {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (hExt : DataExt D) (h63 : R6_3 D) (h76 : R76Sig D) (h856 : R856 D) (h881 : R881 D)
    (h882 : R882 D) (h883 : R883 D) (hSL3 : List880NotSL3PiType)
    (hIns : List880PRankInspection) (hJ2 : J2FivePRank) (hRk : List880CentralizerRanks)
    (hE9 : List880ThreeInE9) : R885 D := by
  intro L P hset
  by_cases hJ : IsSpor (Bar2 L) .J2
  · obtain ⟨hsig, hrank⟩ := sig_eq_five_of_isSpor_j2 D hSg hExt h883 hJ2 hset hJ
    exact ⟨hJ, hsig, hrank⟩
  · exact (false_of_set880_not_isSpor_j2 D hSg h63 h76 h856 h881 h882 h883 hSL3 hIns hE9 hRk
      hset hJ).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
