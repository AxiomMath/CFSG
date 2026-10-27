module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63J2Tits
public import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33PartialRanks
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK332
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65FrattiniWeak
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofCore
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (PPrimeCoreIn)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

private theorem k89sp_card_map {X Y : Type} [Group X] [Group Y] (φ : X →* Y) (A : Subgroup X)
    (h : A ⊓ φ.ker = ⊥) : Nat.card (A.map φ) = Nat.card A := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : A => (⟨φ x, Subgroup.mem_map_of_mem φ x.2⟩ : A.map φ)) ⟨?_, ?_⟩)).symm
  · intro x y hxy
    have h1 : φ x = φ y := congrArg Subtype.val hxy
    have h2 : (x : X)⁻¹ * y ∈ A ⊓ φ.ker :=
      ⟨A.mul_mem (A.inv_mem x.2) y.2, MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, h1]; group)⟩
    rw [h, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  · rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

private theorem k89sp_eq_bot_of_pGroup_coprime {G : Type} [Group G] [Finite G]
    {X : Subgroup G} {r : ℕ} (hr : r.Prime) (h1 : IsPGroup r X)
    (h2 : Nat.Coprime r (Nat.card X)) : X = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp h1
  rw [hn] at h2
  have hn0 : n = 0 := by
    by_contra hn0
    have : r ∣ r ^ n := dvd_pow_self r hn0
    exact hr.one_lt.ne' (Nat.eq_one_of_dvd_one (h2 ▸ Nat.dvd_gcd (dvd_refl r) this))
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq _ hn

private theorem k89sp_card_Z {G : Type} [Group G] [Finite G] (D : Data G)
    (hFacts : AllFacts889 D) {L P : Subgroup G} {ω : G} (hω : Set889 D L P ω) :
    Nat.card (ZOf (P ⊓ L)) = 3 := by
  have hF := hFacts L P ω hω
  let K : Subgroup G := K889 L ω
  have hZK : ZOf (P ⊓ L) ≤ K := (inf_le_left : ZOf (P ⊓ L) ≤ P ⊓ L).trans hF.qLe
  let ZK : Subgroup ↥K := Subgroup.subgroupOf (ZOf (P ⊓ L)) K
  have hZ3 : IsPGroup 3 ZK :=
    (hω.sylow3.isPGroup.to_le (inf_le_left.trans inf_le_left)).comap_subtype
  have hO2 : IsPGroup 2 (CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
  have hdisj : Disjoint ZK (CFSG.pCore 2 ↥K) :=
    IsPGroup.disjoint_of_coprime hZ3 hO2 (by decide)
  have hinf : ZK ⊓ CFSG.pCore 2 ↥K = ⊥ := disjoint_iff.mp hdisj
  let π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hker : π.ker = CFSG.pCore 2 ↥K := QuotientGroup.ker_mk' _
  have hinf' : ZK ⊓ π.ker = ⊥ := by rw [hker]; exact hinf
  have hcardmap : Nat.card (ZK.map π) = Nat.card ZK := k89sp_card_map π ZK hinf'
  have hcardsub : Nat.card ZK = Nat.card (ZOf (P ⊓ L)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK)
  calc Nat.card (ZOf (P ⊓ L)) = Nat.card ZK := hcardsub.symm
    _ = Nat.card (ZK.map π) := hcardmap.symm
    _ = Nat.card (Subgroup.center (Bar2 K)) := by
        rw [show ZK.map π = ((ZOf (P ⊓ L)).subgroupOf (K889 L ω)).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(K889 L ω))) from rfl, hF.centerEq]
    _ = 3 := hF.alt6.2.1

private theorem k89sp_Z_inf_I {G : Type} [Group G] [Finite G] (D : Data G)
    {L P : Subgroup G} {ω : G} (hω : Set889 D L P ω) (X : Subgroup G) :
    ZOf (P ⊓ L) ⊓ PPrimeCoreIn 3 X = ⊥ := by
  have hZ3 : IsPGroup 3 ((ZOf (P ⊓ L) ⊓ PPrimeCoreIn 3 X : Subgroup G)) :=
    (hω.sylow3.isPGroup.to_le (inf_le_left.trans inf_le_left)).to_inf_left
  have hcardI : Nat.card (PPrimeCoreIn 3 X) = Nat.card (CFSG.pPrimeCore 3 ↥X) :=
    Subgroup.card_map_of_injective (K := CFSG.pPrimeCore 3 ↥X) X.subtype_injective
  have hcopI : Nat.Coprime 3 (Nat.card (PPrimeCoreIn 3 X)) := by
    rw [hcardI]; exact CFSG.pPrimeCore_coprime_card
  have hdvd : Nat.card ((ZOf (P ⊓ L) ⊓ PPrimeCoreIn 3 X : Subgroup G)) ∣
      Nat.card (PPrimeCoreIn 3 X) :=
    Subgroup.card_dvd_of_le (H := (ZOf (P ⊓ L) ⊓ PPrimeCoreIn 3 X : Subgroup G))
      (K := PPrimeCoreIn 3 X) inf_le_right
  exact k89sp_eq_bot_of_pGroup_coprime Nat.prime_three hZ3 (hcopI.coprime_dvd_right hdvd)

private theorem k89sp_pRank_three_le_three {G : Type} [Group G] [Finite G] (D : Data G)
    (hrank : Rank889 D) {L P : Subgroup G} {ω : G} (hω : Set889 D L P ω) (X : Subgroup G) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 3 := by
  have hp3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) = CFSG.Open.pRank 3 P :=
    (CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow Nat.prime_three
      hω.sylow3).symm
  have hPM : P ≤ D.M := fun x hx => hω.normP (Subgroup.le_normalizer hx)
  have hM3 : CFSG.Open.pRank 3 D.M ≤ 3 :=
    (hrank L P hω.set880 D.M D.maxLocal.1).1
  calc CFSG.Open.pRank 3 (⊤ : Subgroup ↥X)
      = CFSG.Open.pRank 3 X := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup X).symm
    _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := CFSG.SectionRank.pRank_mono (by norm_num) le_top
    _ = CFSG.Open.pRank 3 P := hp3
    _ ≤ CFSG.Open.pRank 3 D.M := CFSG.SectionRank.pRank_mono (by norm_num) hPM
    _ ≤ 3 := hM3

private theorem k89sp_card_of_isA6Z3 {Y : Type} [Group Y] (h : IsA6Z3 Y) : Nat.card Y = 1080 := by
  obtain ⟨-, hz, e⟩ := h
  have hq : Nat.card (Y ⧸ Subgroup.center Y) = 360 := by
    obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
  rw [hq, hz] at hcard
  omega

private theorem k89sp_action_le_inner
    {K J : Type} [Group K] [Finite K] [Group J] [Finite J]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer J))
    (φ : K →* MulAut J) :
    ∀ k, φ k ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner J := by
  have : Group.IsPerfect K := ⟨hperf⟩
  intro k
  obtain ⟨e, he⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner φ k
  exact MonoidHom.mem_range.mpr ⟨e, he.symm⟩

private theorem k89sp_act_trivial_of_pRank_three_le_one (hAct : S889Act)
    {K J : Type} [Group K] [Finite K] [Group J] [Finite J]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hA6 : IsA6Z3 (K ⧸ CFSG.pCore 2 K))
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer J))
    (hJ : CFSG.Open.pRank 3 (⊤ : Subgroup J) ≤ 1)
    (φ : K →* MulAut J) : ∀ k, φ k = 1 := by
  have : Group.IsPerfect K := ⟨hperf⟩
  have hin := k89sp_action_le_inner hperf hOut φ
  by_contra hne
  push Not at hne
  obtain ⟨k0, hk0⟩ := hne
  let ψ : K →* ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner J) :=
    φ.codRestrict _ hin
  have hψne : ψ.range ≠ ⊥ := by
    intro hbot
    have hmem : ψ k0 ∈ ψ.range := ⟨k0, rfl⟩
    rw [hbot] at hmem
    exact hk0 (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem))
  have hres := hAct K hperf hA6
  obtain ⟨V, hV, hAlt⟩ := hres
    ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner J) ψ hψne
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥ψ.range ⧸ V)) = 2 :=
    pRank_three_eq_two_of_isAlt_six hAlt
  have hJ' : CFSG.pRank 3 J ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hJ
  have hinner : CFSG.pRank 3 ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner J) ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
      Nat.prime_three (by decide) hJ'
      (MulAut.conj.rangeRestrict : J →* ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner J))
      (MonoidHom.rangeRestrict_surjective _)
  have hinner' : CFSG.Open.pRank 3
      (⊤ : Subgroup ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner J)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hinner
  have hrange : CFSG.Open.pRank 3 (⊤ : Subgroup ↥ψ.range) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner J)) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup ψ.range]
    exact CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top
  have hrange1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥ψ.range) ≤ 1 := hrange.trans hinner'
  have hrange1' : CFSG.pRank 3 ↥ψ.range ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hrange1
  have hV1 : CFSG.pRank 3 (↥ψ.range ⧸ V) ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
      Nat.prime_three (by decide) hrange1' (QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V)
  have hV1' : CFSG.Open.pRank 3 (⊤ : Subgroup (↥ψ.range ⧸ V)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hV1
  omega

private theorem k89sp_five_dvd_card_of_action (hAct : S889Act)
    {K J : Type} [Group K] [Finite K] [Group J] [Finite J]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hA6 : IsA6Z3 (K ⧸ CFSG.pCore 2 K))
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer J))
    (φ : K →* MulAut J) (hφ : φ.range ≠ ⊥) : 5 ∣ Nat.card J := by
  have : Group.IsPerfect K := ⟨hperf⟩
  have htop : (φ.rangeRestrict).range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ (MonoidHom.rangeRestrict_surjective φ)
  have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot φ.range).mpr hφ
  have hne : (φ.rangeRestrict).range ≠ ⊥ := by
    rw [htop]; exact top_ne_bot
  have hres := hAct K hperf hA6
  obtain ⟨V, hV, hAlt⟩ := hres ↥φ.range φ.rangeRestrict hne
  have hcardq : Nat.card (↥(φ.rangeRestrict).range ⧸ V) = 360 := by
    obtain ⟨e⟩ := hAlt
    rw [Nat.card_congr e.toEquiv, CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4]
    norm_num
  have h5 : 5 ∣ Nat.card (↥(φ.rangeRestrict).range ⧸ V) := by rw [hcardq]; norm_num
  have h1 : 5 ∣ Nat.card ↥(φ.rangeRestrict).range :=
    h5.trans (Subgroup.card_quotient_dvd_card V)
  have h2 : Nat.card ↥(φ.rangeRestrict).range = Nat.card φ.range := by
    rw [htop, Subgroup.card_top]
  have h3 : Nat.card φ.range ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.inner J) :=
    Subgroup.card_dvd_of_le (fun x hx => by
      obtain ⟨k, rfl⟩ := hx
      exact k89sp_action_le_inner hperf hOut φ k)
  have h4 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner J) ∣ Nat.card J :=
    Subgroup.card_dvd_of_surjective
      (f := (MulAut.conj.rangeRestrict :
        J →* ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner J)))
      (MonoidHom.rangeRestrict_surjective _)
  exact ((h2 ▸ h1).trans h3).trans h4

private theorem k89sp_chain {V : Type} [Group V] [Finite V] {N : Subgroup V}
    (hrk : CFSG.Open.pRank 3 N ≤ 1) {A B : Subgroup V} (hAN : A ≤ N) (hBN : B ≤ N)
    (hA : IsPGroup 3 A) (hB : IsPGroup 3 B) (hAB : A ≤ Subgroup.centralizer (B : Set V)) :
    A ≤ B ∨ B ≤ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnorm : A ≤ Subgroup.normalizer (B : Set V) :=
    hAB.trans (Subgroup.centralizer_le_normalizer _)
  have hU : IsPGroup 3 ↥(A ⊔ B) := r889_isPGroup_sup hA hB hnorm
  have hcyc : IsCyclic ↥(A ⊔ B) :=
    CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) hU (sup_le hAN hBN) hrk
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hA)
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card.mp hB)
  have hAc : Nat.card (A.subgroupOf (A ⊔ B)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hBc : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rcases le_total a b with hab | hab
  · left
    have hdvd : Nat.card (A.subgroupOf (A ⊔ B)) ∣ Nat.card (B.subgroupOf (A ⊔ B)) := by
      rw [hAc, hBc, ha, hb]
      exact pow_dvd_pow 3 hab
    have hle := (IsCyclic.subgroup_le_iff_card_dvd (G := ↥(A ⊔ B))
      (H := A.subgroupOf (A ⊔ B)) (K := B.subgroupOf (A ⊔ B))).mpr hdvd
    intro x hx
    exact hle (show (⟨x, (le_sup_left : A ≤ A ⊔ B) hx⟩ : ↥(A ⊔ B)) ∈ A.subgroupOf (A ⊔ B) from hx)
  · right
    have hdvd : Nat.card (B.subgroupOf (A ⊔ B)) ∣ Nat.card (A.subgroupOf (A ⊔ B)) := by
      rw [hAc, hBc, ha, hb]
      exact pow_dvd_pow 3 hab
    have hle := (IsCyclic.subgroup_le_iff_card_dvd (G := ↥(A ⊔ B))
      (H := B.subgroupOf (A ⊔ B)) (K := A.subgroupOf (A ⊔ B))).mpr hdvd
    intro x hx
    exact hle (show (⟨x, (le_sup_right : B ≤ A ⊔ B) hx⟩ : ↥(A ⊔ B)) ∈ B.subgroupOf (A ⊔ B) from hx)

private theorem k89sp_perfect_central_sylow {J : Type} [Group J] [Finite J]
    (hJ : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⊤) {p : ℕ} [Fact p.Prime] (P : Sylow p J)
    (hP : (P : Subgroup J) ≤ Subgroup.center J) : (P : Subgroup J) = ⊥ := by
  have hcent : Subgroup.centralizer (P : Set J) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr fun x hx => hP hx
  have hnorm : Subgroup.normalizer (P : Subgroup J) ≤ Subgroup.centralizer (P : Set J) := by
    rw [hcent]; exact le_top
  let f : J →* ↥P := MonoidHom.transferSylow P hnorm
  have hcomm : ∀ a b : ↥P, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hP b.2) a)
  have hker : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ ≤ f.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    simp only [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
    rw [hcomm (f g₁) (f g₂)]
    group
  rw [hJ] at hker
  rw [eq_bot_iff]
  intro g hg
  have h1 : f g = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top g))
  have h2 := MonoidHom.transferSylow_eq_pow P hnorm g hg
  rw [h1] at h2
  have h3 : g ^ (P : Subgroup J).index = 1 := by
    have := congrArg Subtype.val h2
    simpa using this.symm
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
  have h4 : g ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime (P : Subgroup J).index (p ^ k) :=
    (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr P.not_dvd_index).symm)
  have h5 : g ^ Nat.gcd (P : Subgroup J).index (p ^ k) = 1 := pow_gcd_eq_one.mpr ⟨h3, h4⟩
  rw [hcop] at h5
  simpa using h5


private theorem k89sp_pPrimeCore_sub_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hO : CFSG.pPrimeCore 3 Y = ⊥) (W : Subgroup Y) [W.Normal] :
    CFSG.pPrimeCore 3 ↥W = ⊥ := by
  have hnorm : ((CFSG.pPrimeCore 3 ↥W).map W.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hcop : Nat.Coprime 3 (Nat.card ((CFSG.pPrimeCore 3 ↥W).map W.subtype)) := by
    rw [Subgroup.card_map_of_injective W.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hbot := (CFSG.pPrimeCore_eq_bot_iff.mp hO) _ hnorm hcop
  exact (Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective).mp hbot

private theorem k89sp_three_dvd_card_component {V : Type} [Group V] [Finite V]
    (hO : CFSG.pPrimeCore 3 V = ⊥) {J : Subgroup V} (hJ : IsComponentOf J ⊤) :
    3 ∣ Nat.card J := by
  by_contra hndvd
  have hcop : Nat.Coprime 3 (Nat.card J) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hndvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsub : J.IsSubnormal := CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
    hJ.2.1 Subgroup.IsSubnormal.top
  have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hsub hcop
  rw [hO] at hle
  have hJbot : J = ⊥ := le_bot_iff.mp hle
  have : Nontrivial J := CFSG.ComponentClassification.Quasisimple.nontrivial hJ.2.2
  exact ((Subgroup.nontrivial_iff_ne_bot J).mp this) hJbot

private theorem k89sp_noncentral {V : Type} [Group V] [Finite V]
    (hO : CFSG.pPrimeCore 3 V = ⊥) {J : Subgroup V} (hJ : IsComponentOf J ⊤) :
    ∃ S : Subgroup V, S ≤ J ∧ IsPGroup 3 S ∧ ¬ S ≤ Subgroup.centralizer (J : Set V) := by
  have hdvd := k89sp_three_dvd_card_component hO hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥J) := inferInstance
  refine ⟨(P : Subgroup ↥J).map J.subtype, Subgroup.map_subtype_le _,
    P.isPGroup'.map _, ?_⟩
  intro hS
  have hPc : (P : Subgroup ↥J) ≤ Subgroup.center ↥J := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hS ⟨x, hx, rfl⟩ g g.2)
  have hbot := k89sp_perfect_central_sylow hJ.2.2.1 P hPc
  have h3 : 3 ∣ Nat.card (P : Subgroup ↥J) := P.dvd_card_of_dvd_card hdvd
  rw [hbot, Subgroup.card_bot] at h3
  exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)

private theorem k89sp_component_unique {V : Type} [Group V] [Finite V]
    (hO : CFSG.pPrimeCore 3 V = ⊥) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup V) ≤ 1)
    {J₁ J₂ : Subgroup V} (h₁ : IsComponentOf J₁ ⊤) (h₂ : IsComponentOf J₂ ⊤) : J₁ = J₂ := by
  by_contra hne
  have hcomm : ⁅J₁, J₂⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne J₁ J₂ h₁ h₂ hne
  have h12 : J₁ ≤ Subgroup.centralizer (J₂ : Set V) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have h21 : J₂ ≤ Subgroup.centralizer (J₁ : Set V) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hcomm)
  obtain ⟨S₁, hS₁J, hS₁p, hS₁n⟩ := k89sp_noncentral hO h₁
  obtain ⟨S₂, hS₂J, hS₂p, hS₂n⟩ := k89sp_noncentral hO h₂
  have hS₁c : S₁ ≤ Subgroup.centralizer (S₂ : Set V) :=
    (hS₁J.trans h12).trans (Subgroup.centralizer_le hS₂J)
  rcases k89sp_chain (N := ⊤) hrk le_top le_top hS₁p hS₂p hS₁c with hle | hle
  · exact hS₁n (hle.trans (hS₂J.trans h21))
  · exact hS₂n (hle.trans (hS₁J.trans h12))

private theorem k89sp_layer_cases {V : Type} [Group V] [Finite V]
    (hO : CFSG.pPrimeCore 3 V = ⊥) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup V) ≤ 1) :
    CFSG.ComponentClassification.Layer.subgroup V = ⊥ ∨
      ∃ J : Subgroup V, IsComponentOf J ⊤ ∧ CFSG.ComponentClassification.Layer.subgroup V = J := by
  by_cases h : ∃ J : Subgroup V, IsComponentOf J ⊤
  · obtain ⟨J, hJ⟩ := h
    right
    refine ⟨J, hJ, ?_⟩
    have hset : {C : Subgroup V | IsComponentOf C ⊤} = {J} := by
      ext C
      constructor
      · intro hC
        exact k89sp_component_unique hO hrk hC hJ
      · intro hC
        rw [Set.mem_singleton_iff] at hC
        rw [Set.mem_setOf_eq, hC]
        exact hJ
    rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup, hset, sSup_singleton]
  · left
    have hset : {C : Subgroup V | IsComponentOf C ⊤} = ∅ := by
      ext C
      constructor
      · intro hC
        exact absurd ⟨C, hC⟩ h
      · intro hC
        exact absurd hC (Set.notMem_empty _)
    rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup, hset, sSup_empty]

private theorem k89sp_fitting_eq_pCore {V : Type} [Group V] [Finite V]
    (hO : CFSG.pPrimeCore 3 V = ⊥) :
    CFSG.ComponentClassification.Fitting.subgroup V = CFSG.pCore 3 V := by
  rw [CFSG.ComponentClassification.PrimeCore.fitting_eq_join]
  apply le_antisymm
  · apply iSup_le
    intro prime
    show CFSG.pCore prime.val V ≤ CFSG.pCore 3 V
    by_cases h3 : prime.val = 3
    · exact (congrArg (fun r => CFSG.pCore r V) h3).le
    · have hnorm : (CFSG.pCore prime.val V).Normal := CFSG.pCore_normal
      have : Fact prime.val.Prime := ⟨prime.property⟩
      have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore prime.val V)) := by
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := prime.val) (G := V)).exists_card_eq
        rw [hn]
        exact Nat.Coprime.pow_right n
          ((Nat.coprime_primes Nat.prime_three prime.property).mpr (Ne.symm h3))
      have hbot := (CFSG.pPrimeCore_eq_bot_iff.mp hO) _ hnorm hcop
      rw [hbot]
      exact bot_le
  · exact le_iSup (fun prime : {prime : ℕ // prime.Prime} =>
      CFSG.ComponentClassification.PrimeCore.subgroup prime.val V) ⟨3, Nat.prime_three⟩

private theorem k89sp_perfect_acts_trivially_on_cyclic {Y : Type} [Group Y] [Finite Y] {K : Type}
    [Group K] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (φ : K →* Y)
    (C : Subgroup Y) [C.Normal] [IsCyclic ↥C] (k : K) (x : Y) (hx : x ∈ C) :
    φ k * x * (φ k)⁻¹ = x := by
  let ψ : K →* MulAut ↥C := (MulAut.conjNormal : Y →* MulAut ↥C).comp φ
  have hcomm : ∀ a b : MulAut ↥C, a * b = b * a := fun a b => by
    apply (IsCyclic.mulAutMulEquiv ↥C).injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hker : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ ψ.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    simp only [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
    rw [hcomm (ψ g₁) (ψ g₂)]
    group
  rw [hperf] at hker
  have h1 : ψ k = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top k))
  have h2 : ((ψ k ⟨x, hx⟩ : ↥C) : Y) = x := by
    rw [h1]; rfl
  simpa [ψ, MulAut.conjNormal_apply] using h2

private theorem k89sp_fitting_centralized {Y : Type} [Group Y] [Finite Y] {K : Type} [Group K]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (φ : K →* Y)
    (W : Subgroup Y) [W.Normal] (hO3 : CFSG.pPrimeCore 3 ↥W = ⊥)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥W) ≤ 1) (k : K) :
    (CFSG.ComponentClassification.Fitting.subgroup ↥W).map W.subtype ≤
      Subgroup.centralizer ({φ k} : Set Y) := by
  rw [k89sp_fitting_eq_pCore hO3]
  have : (CFSG.pCore 3 ↥W).Characteristic := CFSG.pCore_characteristic
  have : ((CFSG.pCore 3 ↥W).map W.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hc1 : IsCyclic ↥(CFSG.pCore 3 ↥W) :=
    CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) CFSG.pCore_isPGroup
      le_top hrk
  have : IsCyclic ↥((CFSG.pCore 3 ↥W).map W.subtype) :=
    isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (CFSG.pCore 3 ↥W) W.subtype W.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective (CFSG.pCore 3 ↥W) W.subtype W.subtype_injective).surjective
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact mul_inv_eq_iff_eq_mul.mp (k89sp_perfect_acts_trivially_on_cyclic hperf φ _ k x hx)

private theorem k89sp_act_trivial_quasisimple (hAct : S889Act)
    (hSch : CFSG.LocalAnalysis.UniquenessCase.UCK.KSch)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y)
    {K : Type} [Group K] [Finite K] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hA6 : IsA6Z3 (K ⧸ CFSG.pCore 2 K)) (φ : K →* Y) (J : Subgroup Y) [J.Normal]
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) ≤ 1)
    (k : K) (x : Y) (hx : x ∈ J) : φ k * x * (φ k)⁻¹ = x := by
  have : Group.IsPerfect ↥J := ⟨hJq.1⟩
  have hKS : CFSG.Open.IsKGroup (↥J ⧸ Subgroup.center ↥J) :=
    (hY.subgroup J).quotient (Subgroup.center ↥J)
  have : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJq.2
  have hOutS : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥J ⧸ Subgroup.center ↥J)) :=
    hSch _ inferInstance hKS
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥J
  have h1 := k89sp_act_trivial_of_pRank_three_le_one hAct hperf hA6 inferInstance hrk
    ((MulAut.conjNormal : Y →* MulAut ↥J).comp φ) k
  have h2 : ((((MulAut.conjNormal : Y →* MulAut ↥J).comp φ) k ⟨x, hx⟩ : ↥J) : Y) = x := by
    rw [h1]; rfl
  simpa [MulAut.conjNormal_apply] using h2

private theorem k89sp_layer_centralized (hAct : S889Act)
    (hSch : CFSG.LocalAnalysis.UniquenessCase.UCK.KSch)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y)
    {K : Type} [Group K] [Finite K] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hA6 : IsA6Z3 (K ⧸ CFSG.pCore 2 K)) (φ : K →* Y)
    (W : Subgroup Y) [W.Normal] (hO3 : CFSG.pPrimeCore 3 ↥W = ⊥)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥W) ≤ 1) (k : K) :
    (CFSG.ComponentClassification.Layer.subgroup ↥W).map W.subtype ≤
      Subgroup.centralizer ({φ k} : Set Y) := by
  rcases k89sp_layer_cases hO3 hrk with h | ⟨J, hJ, hEq⟩
  · rw [h, Subgroup.map_bot]; exact bot_le
  · rw [hEq]
    have : J.Characteristic := hEq ▸ CFSG.ComponentClassification.Layer.characteristic ↥W
    have : (J.map W.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hq : CFSG.Open.IsQuasisimple ↥(J.map W.subtype) :=
      hJ.2.2.of_mulEquiv (Subgroup.equivMapOfInjective J W.subtype W.subtype_injective).symm
    have hrkJ : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(J.map W.subtype)) ≤ 1 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (J.map W.subtype)]
      calc CFSG.Open.pRank 3 (J.map W.subtype)
          ≤ CFSG.Open.pRank 3 W :=
            CFSG.SectionRank.pRank_mono (by norm_num) (Subgroup.map_subtype_le J)
        _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥W) :=
            CFSG.SectionRank.pRank_eq_pRank_top_subgroup W
        _ ≤ 1 := hrk
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact mul_inv_eq_iff_eq_mul.mp
      (k89sp_act_trivial_quasisimple hAct hSch hY hperf hA6 φ (J.map W.subtype) hq hrkJ k x hx)

private theorem k89sp_caseA (hAct : S889Act) (hSch : CFSG.LocalAnalysis.UniquenessCase.UCK.KSch)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y)
    {K : Type} [Group K] [Finite K] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hA6 : IsA6Z3 (K ⧸ CFSG.pCore 2 K)) (φ : K →* Y)
    (W : Subgroup Y) [W.Normal] (hO3 : CFSG.pPrimeCore 3 ↥W = ⊥)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥W) ≤ 1)
    (T : Subgroup Y) (hT3 : Nat.card T = 3) (hTW : T ≤ W) (hTφ : T ≤ φ.range) : T.Normal := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Fm, hFm⟩ : ∃ Fm : Subgroup Y,
      Fm = (CFSG.ComponentClassification.GeneralizedFitting.subgroup ↥W).map W.subtype :=
    ⟨_, rfl⟩
  have hFn : Fm.Normal := by
    have : (CFSG.ComponentClassification.GeneralizedFitting.subgroup ↥W).Characteristic :=
      CFSG.ComponentClassification.GeneralizedFitting.characteristic ↥W
    rw [hFm]
    exact ConjAct.normal_of_characteristic_of_normal
  have hcent : ∀ k : K, Fm ≤ Subgroup.centralizer ({φ k} : Set Y) := by
    intro k
    rw [hFm, CFSG.ComponentClassification.GeneralizedFitting.subgroup.eq_sup, Subgroup.map_sup]
    exact sup_le (k89sp_fitting_centralized hperf φ W hO3 hrk k)
      (k89sp_layer_centralized hAct hSch hY hperf hA6 φ W hO3 hrk k)
  have hTF : ∀ t ∈ T, t ∈ Fm ∧ ∀ f ∈ Fm, t * f = f * t := by
    intro t ht
    obtain ⟨k, hk⟩ := hTφ ht
    have hcomm : ∀ f ∈ Fm, t * f = f * t := by
      intro f hf
      have := (Subgroup.mem_centralizer_iff.mp (hcent k hf)) (φ k) rfl
      rw [← hk]; exact this
    refine ⟨?_, hcomm⟩
    have htW : t ∈ W := hTW ht
    have hmem : (⟨t, htW⟩ : ↥W) ∈ Subgroup.centralizer
        ((CFSG.ComponentClassification.GeneralizedFitting.subgroup ↥W : Subgroup ↥W) : Set ↥W) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      apply Subtype.ext
      exact (hcomm (f : Y) (by rw [hFm]; exact ⟨f, hf, rfl⟩)).symm
    have hin := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le ↥W hmem
    rw [hFm]
    exact ⟨⟨t, htW⟩, hin, rfl⟩
  have hrkW : CFSG.Open.pRank 3 W ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup W]; exact hrk
  have hTp : IsPGroup 3 T := IsPGroup.of_card (n := 1) (by rw [hT3]; norm_num)
  have hnormal : ∀ y : Y, T.map (MulAut.conj y).toMonoidHom = T := by
    intro y
    have hT'W : T.map (MulAut.conj y).toMonoidHom ≤ W := by
      rintro _ ⟨t, ht, rfl⟩
      exact Subgroup.Normal.conj_mem inferInstance t (hTW ht) y
    have hT'p : IsPGroup 3 ↥(T.map (MulAut.conj y).toMonoidHom) := hTp.map _
    have hT'card : Nat.card (T.map (MulAut.conj y).toMonoidHom) = Nat.card T :=
      Subgroup.card_map_of_injective (MulAut.conj y).injective
    have hT'F : ∀ u ∈ T.map (MulAut.conj y).toMonoidHom, ∀ f ∈ Fm, u * f = f * u := by
      rintro _ ⟨t, ht, rfl⟩ f hf
      obtain ⟨-, htc⟩ := hTF t ht
      have h1 := htc (y⁻¹ * f * y) (by simpa using hFn.conj_mem f hf y⁻¹)
      show y * t * y⁻¹ * f = f * (y * t * y⁻¹)
      calc y * t * y⁻¹ * f = y * (t * (y⁻¹ * f * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * f * y) * t) * y⁻¹ := by rw [h1]
        _ = f * (y * t * y⁻¹) := by group
    have hT'F' : ∀ u ∈ T.map (MulAut.conj y).toMonoidHom, u ∈ Fm := by
      rintro _ ⟨t, ht, rfl⟩
      exact hFn.conj_mem t (hTF t ht).1 y
    have hAB : T ≤ Subgroup.centralizer ((T.map (MulAut.conj y).toMonoidHom : Subgroup Y) : Set Y) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact ((hTF t ht).2 u (hT'F' u hu)).symm
    rcases k89sp_chain hrkW hTW hT'W hTp hT'p hAB with hle | hle
    · exact (Subgroup.eq_of_le_of_card_ge hle hT'card.le).symm
    · exact Subgroup.eq_of_le_of_card_ge hle hT'card.ge
  exact ⟨fun n hn y => by
    have : y * n * y⁻¹ ∈ T.map (MulAut.conj y).toMonoidHom := ⟨n, hn, rfl⟩
    rwa [hnormal y] at this⟩

private theorem k89sp_simple_case (hAct : S889Act) (hSch : CFSG.LocalAnalysis.UniquenessCase.UCK.KSch)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y)
    {K : Type} [Group K] [Finite K] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hA6 : IsA6Z3 (K ⧸ CFSG.pCore 2 K)) (φ : K →* Y)
    (S : Subgroup Y) [S.Normal] (hS : IsSimpleGroup ↥S)
    (T : Subgroup Y) (hT3 : Nat.card T = 3) (hTS : T ≤ S) (hTφ : T ≤ φ.range) :
    T.Normal ∨ 5 ∣ Nat.card S := by
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S) :=
    hSch ↥S hS (hY.subgroup S)
  by_cases hφ : ((MulAut.conjNormal : Y →* MulAut ↥S).comp φ).range = ⊥
  · left
    have htriv : ∀ k : K, ∀ x : Y, x ∈ S → φ k * x * (φ k)⁻¹ = x := by
      intro k x hx
      have h1 : ((MulAut.conjNormal : Y →* MulAut ↥S).comp φ) k = 1 := by
        have hmem : ((MulAut.conjNormal : Y →* MulAut ↥S).comp φ) k ∈
            ((MulAut.conjNormal : Y →* MulAut ↥S).comp φ).range := ⟨k, rfl⟩
        rw [hφ] at hmem
        exact Subgroup.mem_bot.mp hmem
      have h2 : ((((MulAut.conjNormal : Y →* MulAut ↥S).comp φ) k ⟨x, hx⟩ : ↥S) : Y) = x := by
        rw [h1]; rfl
      simpa [MulAut.conjNormal_apply] using h2
    have hTc : T.subgroupOf S ≤ Subgroup.center ↥S := by
      intro t ht
      obtain ⟨k, hk⟩ := hTφ ht
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      have := htriv k (s : Y) s.2
      rw [hk] at this
      exact mul_inv_eq_iff_eq_mul.mp this |>.symm
    have hcardT : Nat.card (T.subgroupOf S) = 3 := by
      rw [← hT3]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥S) with hb | ht
    · exfalso
      rw [hb] at hTc
      have h1 : T.subgroupOf S = ⊥ := le_bot_iff.mp hTc
      rw [h1, Subgroup.card_bot] at hcardT
      omega
    · have : IsMulCommutative ↥S := Subgroup.center_eq_top_iff.1 ht
      have hprime : (Nat.card ↥S).Prime := (Group.is_simple_iff_prime_card).1 hS
      have hdvd : 3 ∣ Nat.card ↥S := hT3 ▸ Subgroup.card_dvd_of_le hTS
      have hS3 : 3 = Nat.card ↥S := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hprime).mp hdvd
      have hTeq : T = S :=
        Subgroup.eq_of_le_of_card_ge hTS (by rw [hT3, ← hS3])
      rw [hTeq]
      infer_instance
  · right
    exact k89sp_five_dvd_card_of_action hAct hperf hA6 inferInstance _ hφ

private theorem k89sp_le_of_inf_ne_bot {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    {F : Subgroup G} (hF : IsPGroup p F) (hne : F ⊓ M ≠ ⊥) : F ≤ M := by
  by_contra hFM
  have hlt : F ⊓ M < F :=
    lt_of_le_of_ne inf_le_left (fun h => hFM (by rw [← h]; exact inf_le_right))
  obtain ⟨x, hxF, hxN, hxA⟩ := r889_exists_mem_normalizer_of_lt hF hlt
  have hxM : x ∉ M := fun h => hxA ⟨hxF, h⟩
  have hA : F ⊓ M ≤ M ⊓ M.map (MulAut.conj x).toMonoidHom := by
    refine le_inf inf_le_right ?_
    intro a ha
    have hmem : x⁻¹ * a * x ∈ F ⊓ M := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) a).mp ha
      simpa using this
    exact ⟨x⁻¹ * a * x, hmem.2, by simp [mul_assoc]⟩
  have hp : p ∣ Nat.card (F ⊓ M : Subgroup G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp (hF.to_inf_left : IsPGroup p ↥(F ⊓ M)))
    rw [hn]
    refine dvd_pow_self p ?_
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hn, pow_zero]))
  exact hsp.2.2 x hxM (hp.trans (Subgroup.card_dvd_of_le hA))

private theorem k89sp_frattini {H : Type} [Group H] [Finite H] (I Z : Subgroup H) [I.Normal]
    (hI : Nat.Coprime 3 (Nat.card I)) (hZ : Nat.card Z = 3) (hZI : Z ⊓ I = ⊥)
    (hN : (Z.map (QuotientGroup.mk' I)).Normal) :
    ∀ x : H, ∃ n ∈ Subgroup.normalizer (Z : Set H), ∃ i ∈ I, x = n * i := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let q : H →* H ⧸ I := QuotientGroup.mk' I
  let H' : Subgroup H := (Z.map q).comap q
  have hH'n : H'.Normal := Subgroup.normal_comap q
  have hZH' : Z ≤ H' := fun z hz => Subgroup.mem_map_of_mem q hz
  have hZq : Nat.card (Z.map q) = 3 := by
    rw [k89sp_card_map q Z (by rw [QuotientGroup.ker_mk']; exact hZI)]; exact hZ
  let Z'' : Subgroup ↥H' := Z.subgroupOf H'
  have hZ''card : Nat.card Z'' = 3 := by
    rw [← hZ]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH').toEquiv
  have hZ''p : IsPGroup 3 Z'' := IsPGroup.of_card (n := 1) (by rw [hZ''card]; norm_num)
  obtain ⟨S, hS⟩ := hZ''p.exists_le_sylow
  let φ : ↥H' →* H ⧸ I := q.comp H'.subtype
  have hSker : (S : Subgroup ↥H') ⊓ φ.ker = ⊥ := by
    have hUp : IsPGroup 3 ↥(((S : Subgroup ↥H') ⊓ φ.ker).map H'.subtype) :=
      (S.isPGroup'.to_inf_left).map H'.subtype
    have hUI : ((S : Subgroup ↥H') ⊓ φ.ker).map H'.subtype ≤ I := by
      rintro _ ⟨s, hs, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hs.2)
    have hdvd : Nat.card (((S : Subgroup ↥H') ⊓ φ.ker).map H'.subtype) ∣ Nat.card I :=
      Subgroup.card_dvd_of_le hUI
    have hbot := k89sp_eq_bot_of_pGroup_coprime Nat.prime_three hUp (hI.coprime_dvd_right hdvd)
    exact (Subgroup.map_eq_bot_iff_of_injective _ H'.subtype_injective).mp hbot
  have hScard : Nat.card (S : Subgroup ↥H') ≤ 3 := by
    have h1 := k89sp_card_map φ (S : Subgroup ↥H') hSker
    have h2 : (S : Subgroup ↥H').map φ ≤ Z.map q := by
      rintro _ ⟨s, hs, rfl⟩
      exact s.2
    calc Nat.card ↥(S : Subgroup ↥H') = Nat.card ↥((S : Subgroup ↥H').map φ) := h1.symm
      _ ≤ Nat.card ↥(Z.map q) := Subgroup.card_le_of_le h2
      _ = 3 := hZq
  have hSeq : Z'' = (S : Subgroup ↥H') :=
    Subgroup.eq_of_le_of_card_ge hS (hScard.trans hZ''card.ge)
  have hFr := Sylow.normalizer_sup_eq_top S
  have hmapS : (S : Subgroup ↥H').map H'.subtype = Z := by
    rw [← hSeq, Subgroup.subgroupOf_map_subtype]
    exact inf_of_le_left hZH'
  rw [hmapS] at hFr
  intro x
  have hx : x ∈ Subgroup.normalizer (Z : Set H) ⊔ H' := by rw [hFr]; exact Subgroup.mem_top x
  have hle : Subgroup.normalizer (Z : Set H) ≤ Subgroup.normalizer (H' : Set H) := by
    rw [Subgroup.normalizer_eq_top (H := H')]; exact le_top
  obtain ⟨n, hn, h, hh, rfl⟩ := r889_mem_sup_of_le_normalizer hle hx
  obtain ⟨z, hz, hzh⟩ := hh
  refine ⟨n * z, Subgroup.mul_mem _ hn (Subgroup.le_normalizer hz), z⁻¹ * h, ?_, by group⟩
  have h1 : q (z⁻¹ * h) = 1 := by rw [map_mul, map_inv, hzh, inv_mul_cancel]
  exact (QuotientGroup.eq_one_iff _).mp h1

private theorem k89sp_pRank_sub_le {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : 1 < p)
    (W : Subgroup Y) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥W) ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup W]
  exact CFSG.SectionRank.pRank_mono hp le_top

private theorem k89sp_g2_isSimple
    {Y : Type} [Group Y] {r f : ℕ} (h : CFSG.Blueprint.LieModel Y .G2 0 r f) :
    IsSimpleGroup Y :=
  (CFSG.LieType.Simplicity.fam_g2_simplicity Y r f
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).mp h).2).2

private theorem k89sp_dispatch
    (hAct : S889Act) (hSch : CFSG.LocalAnalysis.UniquenessCase.UCK.KSch) (hG2 : G2FiveRankCore)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsKGroup Y) (hO : CFSG.pPrimeCore 3 Y = ⊥)
    (h5 : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 1)
    {K : Type} [Group K] [Finite K] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hA6 : IsA6Z3 (K ⧸ CFSG.pCore 2 K)) (φ : K →* Y)
    (W : Subgroup Y) [W.Normal]
    (T : Subgroup Y) (hT3 : Nat.card T = 3) (hTW : T ≤ W) (hTφ : T ≤ φ.range)
    (hcase : CFSG.Open.pRank 3 (⊤ : Subgroup ↥W) ≤ 1 ∨
      CFSG.Blueprint.LieModel ↥W .PSU 3 3 1 ∨
      (∃ r f : ℕ, r.Prime ∧ CFSG.Blueprint.LieModel ↥W .G2 0 r f) ∨ IsSpor ↥W .J2) :
    T.Normal := by
  rcases hcase with hA | hB | ⟨r, f, hr, hC⟩ | hD
  · exact k89sp_caseA hAct hSch hY hperf hA6 φ W (k89sp_pPrimeCore_sub_eq_bot hO W) hA T hT3 hTW
      hTφ
  · have ht : CFSG.Assembly.LowTwoRank.StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags := by decide
    have hsimp : IsSimpleGroup ↥W :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags ht hB
    have hcard : Nat.card ↥W = 6048 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three (hB.statedClassicalModel ht)
    rcases k89sp_simple_case hAct hSch hY hperf hA6 φ W hsimp T hT3 hTW hTφ with h | h
    · exact h
    · exfalso
      rw [hcard] at h
      omega
  · have hsimp : IsSimpleGroup ↥W := k89sp_g2_isSimple hC
    rcases k89sp_simple_case hAct hSch hY hperf hA6 φ W hsimp T hT3 hTW hTφ with h | h
    · exact h
    · exfalso
      have h2 := hG2 ↥W r f hr hC h
      have h3 := k89sp_pRank_sub_le (p := 5) (by norm_num) W
      omega
  · have hsimp : IsSimpleGroup ↥W := by
      obtain ⟨e⟩ := hD
      exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e
    rcases k89sp_simple_case hAct hSch hY hperf hA6 φ W hsimp T hT3 hTW hTφ with h | h
    · exact h
    · exfalso
      have h2 := pRank_five_eq_two_of_isSpor_J2 hD
      have h3 := k89sp_pRank_sub_le (p := 5) (by norm_num) W
      omega

private theorem k89sp_mem_conjugate {G : Type} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [this] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private theorem k89sp_normalizer_of_subgroupOf {G : Type} [Group G] {X Z : Subgroup G} (hZX : Z ≤ X)
    {n : ↥X} (hn : n ∈ Subgroup.normalizer ((Z.subgroupOf X : Subgroup ↥X) : Set ↥X)) :
    (n : G) ∈ Subgroup.normalizer (Z : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro h
  constructor
  · intro hh
    exact (hn ⟨h, hZX hh⟩).mp hh
  · intro hh
    have hhX : h ∈ X := by
      have h1 : (n : G) * h * (n : G)⁻¹ ∈ X := hZX hh
      have h2 := X.mul_mem (X.mul_mem (X.inv_mem n.2) h1) n.2
      simpa [mul_assoc] using h2
    exact (hn ⟨h, hhX⟩).mpr hh

private theorem k89sp_weakly_closed {G : Type} [Group G] [Finite G] (D : Data G) (hWC : S889WeakClosed D)
    {L P : Subgroup G} {ω : G} (hω : Set889 D L P ω) {X : Subgroup G}
    (hZX : ZOf (P ⊓ L) ≤ X) :
    CFSG.ASVolI.ChIJK.IsWeaklyClosedIn ((ZOf (P ⊓ L)).subgroupOf X)
      (Subgroup.normalizer (((ZOf (P ⊓ L)).subgroupOf X : Subgroup ↥X) : Set ↥X)) := by
  intro g hg
  have hmem : ∀ x : ↥X, x ∈ CFSG.conjugate ((ZOf (P ⊓ L)).subgroupOf X) g ↔
      (g : G) * (x : G) * (g : G)⁻¹ ∈ ZOf (P ⊓ L) := by
    intro x
    rw [k89sp_mem_conjugate]
    rfl
  have h1 : (ZOf (P ⊓ L)).map (MulAut.conj ((g : G)⁻¹)).toMonoidHom ≤
      Subgroup.normalizer (ZOf (P ⊓ L) : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzX : z ∈ X := hZX hz
    have hyX : (g : G)⁻¹ * z * (g : G) ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem g.2) hzX) g.2
    have hconj : (⟨(g : G)⁻¹ * z * (g : G), hyX⟩ : ↥X) ∈
        CFSG.conjugate ((ZOf (P ⊓ L)).subgroupOf X) g := by
      rw [hmem]
      have : (g : G) * ((g : G)⁻¹ * z * (g : G)) * (g : G)⁻¹ = z := by group
      show (g : G) * ((g : G)⁻¹ * z * (g : G)) * (g : G)⁻¹ ∈ ZOf (P ⊓ L)
      rw [this]; exact hz
    have := k89sp_normalizer_of_subgroupOf hZX (hg hconj)
    simpa using this
  have h2 := hWC L P ω hω (g : G)⁻¹ h1
  ext x
  rw [hmem]
  constructor
  · intro hx
    have : (x : G) ∈ (ZOf (P ⊓ L)).map (MulAut.conj ((g : G)⁻¹)).toMonoidHom :=
      ⟨(g : G) * x * (g : G)⁻¹, hx, by simp [mul_assoc]⟩
    rw [h2] at this
    exact this
  · intro hx
    have hx' : (x : G) ∈ (ZOf (P ⊓ L)).map (MulAut.conj ((g : G)⁻¹)).toMonoidHom := by
      rw [h2]; exact hx
    obtain ⟨z, hz, hzx⟩ := hx'
    have hzx' : (g : G)⁻¹ * z * (g : G) = x := by simpa using hzx
    have : (g : G) * (x : G) * (g : G)⁻¹ = z := by rw [← hzx']; group
    rw [this]; exact hz

private theorem k89sp_pRank_image_le_one {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (N M : Subgroup H) [M.Normal] (hN : CFSG.Open.pRank p N ≤ 1) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(N.map (QuotientGroup.mk' M))) ≤ 1 := by
  have hN' : CFSG.pRank p ↥N ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup N]
    exact hN
  let f : ↥N →* ↥(N.map (QuotientGroup.mk' M)) :=
    ((QuotientGroup.mk' M).comp N.subtype).codRestrict _ fun x => ⟨x, x.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have := CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective hp hp2 hN'
    f hf
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at this

private theorem k89sp_perfect_top {G : Type} [Group G] (K : Subgroup G) (h : ⁅K, K⁆ = K) :
    ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
  have h1 : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, h1, h]

private theorem k89sp_five_rank {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (h885 : R885 D) (hFive : S889Five D) (hFacts : AllFacts889 D)
    {L P : Subgroup G} {ω : G} (hω : Set889 D L P ω) {X : Subgroup G} (hXtop : X ≠ ⊤)
    (hKX : K889 L ω ≤ X) (hXM : ¬ X ≤ D.M) :
    CFSG.Open.pRank 5 (⊤ : Subgroup ↥X) ≤ 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hF := hFacts L P ω hω
  have h5sig : 5 ∈ D.sig := by
    rw [(h885 L P hω.set880).2.1]; exact Set.mem_singleton 5
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hω.set880.mem) h5sig
  have hcardBar : Nat.card (Bar2 (K889 L ω)) = 1080 := k89sp_card_of_isA6Z3 hF.alt6
  have h5K : 5 ∣ Nat.card ↥(K889 L ω) :=
    (show 5 ∣ Nat.card (Bar2 (K889 L ω)) by rw [hcardBar]; norm_num).trans
      (Subgroup.card_quotient_dvd_card _)
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' 5 h5K
  have hfX : (f : G) ∈ X := hKX f.2
  have hfM : (f : G) ∈ D.M := (r889_le_M hω.set880) (r889_K889_le_left L ω f.2)
  have hf5 : orderOf (f : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hf
  let fX : ↥X := ⟨(f : G), hfX⟩
  have hfXo : orderOf fX = 5 := by
    have := Subgroup.orderOf_coe fX
    rw [← this]; exact hf5
  have hZp : IsPGroup 5 (Subgroup.zpowers fX) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hfXo]; norm_num)
  obtain ⟨Q, hQ⟩ := hZp.exists_le_sylow
  let F : Subgroup G := (Q : Subgroup ↥X).map X.subtype
  have hFp : IsPGroup 5 F := Q.isPGroup'.map X.subtype
  have hFX : F ≤ X := Subgroup.map_subtype_le _
  have hfF : (f : G) ∈ F := ⟨fX, hQ (Subgroup.mem_zpowers fX), rfl⟩
  have hne : F ⊓ D.M ≠ ⊥ := by
    intro hbot
    have hmem : (f : G) ∈ F ⊓ D.M := ⟨hfF, hfM⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hf5
    omega
  have hFM : F ≤ D.M := k89sp_le_of_inf_ne_bot hsp hFp hne
  have hr1 : CFSG.Open.pRank 5 (X ⊓ D.M) ≤ 1 := hFive L P ω hω X hXtop hKX hXM
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 5 F X := ⟨Q, rfl⟩
  calc CFSG.Open.pRank 5 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 5 X :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup X).symm
    _ = CFSG.Open.pRank 5 F :=
        (CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow Nat.prime_five
          hSyl).symm
    _ ≤ CFSG.Open.pRank 5 (X ⊓ D.M) := CFSG.SectionRank.pRank_mono (by norm_num) (le_inf hFX hFM)
    _ ≤ 1 := hr1

theorem s889_split
    {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.K332Z3)
    (hSch : CFSG.LocalAnalysis.UniquenessCase.UCK.KSch) (hG2 : G2FiveRankCore) (h885 : R885 D)
    (h887 : R887 D) (hrank : Rank889 D) (hFacts : AllFacts889 D) (hFive : S889Five D)
    (hAct : S889Act) (hWC : S889WeakClosed D) : S889Split D := by
  intro L P ω hω X hXtop hKX hXM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF := hFacts L P ω hω
  have hZK : ZOf (P ⊓ L) ≤ K889 L ω := (inf_le_left : ZOf (P ⊓ L) ≤ P ⊓ L).trans hF.qLe
  have hZX : ZOf (P ⊓ L) ≤ X := hZK.trans hKX
  have hY0 : CFSG.Open.IsKGroup ↥X := D.standing.kProper.isKGroup X hXtop
  have hZ'card : Nat.card ((ZOf (P ⊓ L)).subgroupOf X) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv).trans (k89sp_card_Z D hFacts hω)
  have hZ'I : (ZOf (P ⊓ L)).subgroupOf X ⊓ CFSG.pPrimeCore 3 ↥X = ⊥ := by
    have hmapZ : ((ZOf (P ⊓ L)).subgroupOf X).map X.subtype = ZOf (P ⊓ L) := by
      rw [Subgroup.subgroupOf_map_subtype]; exact inf_of_le_left hZX
    have h1 := k89sp_Z_inf_I D hω X
    rw [PPrimeCoreIn, ← hmapZ, ← Subgroup.map_inf_eq _ _ X.subtype X.subtype_injective] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h1
  have hI'cop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 ↥X)) := CFSG.pPrimeCore_coprime_card
  have hOY : CFSG.pPrimeCore 3 (↥X ⧸ CFSG.pPrimeCore 3 ↥X) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hYK : CFSG.Open.IsKGroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X) := hY0.quotient _
  have h5X : CFSG.Open.pRank 5 (⊤ : Subgroup ↥X) ≤ 1 :=
    k89sp_five_rank D hSg h885 hFive hFacts hω hXtop hKX hXM
  have h5Y : CFSG.Open.pRank 5 (⊤ : Subgroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X)) ≤ 1 := by
    have h : CFSG.pRank 5 ↥X ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]; exact h5X
    have := CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
      Nat.prime_five (by norm_num) h (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X))
      (QuotientGroup.mk'_surjective _)
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at this
  let φ : ↥(K889 L ω) →* (↥X ⧸ CFSG.pPrimeCore 3 ↥X) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)).comp (Subgroup.inclusion hKX)
  have hperf := k89sp_perfect_top (K889 L ω) hF.perfect
  have hA6 : IsA6Z3 (↥(K889 L ω) ⧸ CFSG.pCore 2 ↥(K889 L ω)) := hF.alt6
  let T : Subgroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X) :=
    ((ZOf (P ⊓ L)).subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X))
  have hT3 : Nat.card T = 3 := by
    rw [k89sp_card_map _ _ (by rw [QuotientGroup.ker_mk']; exact hZ'I)]; exact hZ'card
  have hTφ : T ≤ φ.range := by
    rintro _ ⟨z', hz', rfl⟩
    exact ⟨⟨(z' : G), hZK hz'⟩, rfl⟩
  let N0 : Subgroup ↥X := Subgroup.normalClosure
    (((ZOf (P ⊓ L)).subgroupOf X : Subgroup ↥X) : Set ↥X)
  have hN0n : N0.Normal := Subgroup.normalClosure_normal
  let W : Subgroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X) :=
    N0.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X))
  have hWn : W.Normal := Subgroup.Normal.map hN0n _ (QuotientGroup.mk'_surjective _)
  have hZ'N0 : (ZOf (P ⊓ L)).subgroupOf X ≤ N0 := Subgroup.le_normalClosure
  have hTW : T ≤ W := Subgroup.map_mono hZ'N0
  have hZ'p : IsPGroup 3 ↥((ZOf (P ⊓ L)).subgroupOf X) :=
    IsPGroup.of_card (n := 1) (by rw [hZ'card]; norm_num)
  have key : T.Normal := by
    refine k89sp_dispatch hAct hSch hG2 hYK hOY h5Y hperf hA6 φ W T hT3 hTW hTφ ?_
    by_cases h1 : CFSG.Open.pRank 3 N0 ≤ 1
    · left
      exact k89sp_pRank_image_le_one Nat.prime_three (by norm_num) N0 _ h1
    obtain ⟨S, hS, hZS⟩ := CFSG.LocalAnalysis.UniquenessCase.UCK.N588A.exists_isSylowOf_ge_of_le
      (K := ⊤) (Q := (ZOf (P ⊓ L)).subgroupOf X) le_top hZ'p
    have hwc := k89sp_weakly_closed D hWC hω hZX
    have hSN : S ≤ Subgroup.normalizer (((ZOf (P ⊓ L)).subgroupOf X : Subgroup ↥X) : Set ↥X) :=
      le_normalizer_of_isWeaklyClosedIn_normalizer hZS hS.isPGroup hwc
    have hwcS : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn ((ZOf (P ⊓ L)).subgroupOf X) S :=
      fun g hg => hwc g (hg.trans hSN)
    have hSrank : CFSG.Open.pRank 3 S ≤ 3 :=
      (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans
        (k89sp_pRank_three_le_three D hrank hω X)
    have hmap : W = Subgroup.normalClosure
        ((((ZOf (P ⊓ L)).subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X)) :
          Subgroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X)) : Set (↥X ⧸ CFSG.pPrimeCore 3 ↥X)) :=
      Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)
    have hK := hK332 ↥X hY0 S _ hS hSrank hZS hZ'card hwcS (Nat.lt_of_not_le h1)
    rw [← hmap] at hK
    rcases hK with hIso | hJ2
    · unfold CFSG.RankThree.PartTwo.Sec4.IsoGTwoPrime at hIso
      rcases hIso with ⟨r, f, hmodel⟩ | hne
      · exact Or.inr (Or.inr (Or.inl ⟨r, f, hmodel.1.1, Or.inr (Or.inl ⟨rfl, by decide, hmodel⟩)⟩))
      · obtain ⟨e⟩ := hne
        exact Or.inr (Or.inl
          (CFSG.RankThree.PartTwo.Sec19.Step1915WProof.lieModel_of_mulEquiv_projSU_three e))
    · exact Or.inr (Or.inr (Or.inr hJ2))
  intro x hx
  obtain ⟨n, hn, i, hi, hxe⟩ := k89sp_frattini (CFSG.pPrimeCore 3 ↥X)
    ((ZOf (P ⊓ L)).subgroupOf X) hI'cop hZ'card hZ'I key ⟨x, hx⟩
  have hxe' : x = (n : G) * (i : G) := congrArg Subtype.val hxe
  have hnM : (n : G) ∈ D.M :=
    h887 L P hω.set880 (k89sp_normalizer_of_subgroupOf hZX hn)
  have hnX : (n : G) ∈ X ⊓ D.M := ⟨n.2, hnM⟩
  have hiI : (i : G) ∈ PPrimeCoreIn 3 X := ⟨i, hi, rfl⟩
  rw [hxe']
  exact Subgroup.mul_mem _
    ((le_sup_right : X ⊓ D.M ≤ PPrimeCoreIn 3 X ⊔ (X ⊓ D.M)) hnX)
    ((le_sup_left : PPrimeCoreIn 3 X ≤ PPrimeCoreIn 3 X ⊔ (X ⊓ D.M)) hiI)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
