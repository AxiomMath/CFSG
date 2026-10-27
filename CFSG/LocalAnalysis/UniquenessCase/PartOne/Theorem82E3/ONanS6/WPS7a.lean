module

public import CFSG.Goldschmidt.Steps.G3aAut
public import CFSG.GroupTheory.CoprimeCentralizerTransport
public import CFSG.GroupTheory.QuasisimpleOddCenterQuotient
public import CFSG.GroupTheory.SylowComap
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2Conj
public import CFSG.LieType.Ree.SuzukiPerfect
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGen
public import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RankOneSz
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzLtStar
public import CFSG.RankThree.PartOne.F106.ZeroStar
public import CFSG.RankThree.PartTwo.Sec16.Item167StepsProofNonsolv
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
public import CFSG.Holt.General.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactNineteenTwentySix
public import CFSG.Quasithin.Background.C124AsmClassify
public import CFSG.Quasithin.Background.C124Interface
public import CFSG.Quasithin.Background.C124YZStar
public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Vol2.Ch12Sec6D29
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Fin
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzCard
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzE
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzLtGrp
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzSz
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WKl2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXX

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open UniquenessCase.PartTwo.Inputs1719 (center_eq_bot_and_suzukiModel_of_not_three_dvd)
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GorensteinLyons (orbitConjugates)
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem center_isPGroup_two_of_quasisimple_isKGroup {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hK : CFSG.Open.IsKGroup K)
    (h3 : ¬ 3 ∣ Nat.card K) : IsPGroup 2 (Subgroup.center K) := by
  classical
  let O : Subgroup K := CFSG.Open.pCoreOf 2 (Subgroup.center K)
  have hOle : O ≤ Subgroup.center K := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _
  have hOn : O.Normal := Subgroup.normal_of_le_center hOle
  letI : O.Normal := hOn
  have hqN : CFSG.Open.IsQuasisimple (K ⧸ O) :=
    CFSG.GroupTheory.isQuasisimple_quotient_pCoreOf_center hq
  have hKN : CFSG.Open.IsKGroup (K ⧸ O) := CFSG.Open.IsKGroup.quotient hK O
  have hZodd : Odd (Nat.card (Subgroup.center (K ⧸ O))) :=
    CFSG.GroupTheory.odd_card_center_quotient_pCoreOf_center hq
  have h3N : ¬ 3 ∣ Nat.card (K ⧸ O) := fun h =>
    h3 (h.trans (Subgroup.card_quotient_dvd_card O))
  have hcenterN : Subgroup.center (K ⧸ O) = ⊥ :=
    (center_eq_bot_and_suzukiModel_of_not_three_dvd
      hqN hKN hZodd h3N).1
  have hZleO : Subgroup.center K ≤ O := by
    have hmap : Subgroup.map (QuotientGroup.mk' O) (Subgroup.center K) ≤
        Subgroup.center (K ⧸ O) :=
      Subgroup.map_center_le_center (QuotientGroup.mk'_surjective O)
    rw [hcenterN, le_bot_iff] at hmap
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    exact hmap
  exact (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 _).to_le hZleO

theorem pCoreOf_center_eq_of_isPGroup_two {K : Type} [Group K] [Finite K]
    (h : IsPGroup 2 (Subgroup.center K)) :
    CFSG.Open.pCoreOf 2 (Subgroup.center K) = Subgroup.center K := by
  have htop : CFSG.pCore 2 (Subgroup.center K) = ⊤ := by
    apply top_le_iff.1
    exact le_sSup ⟨inferInstance, h.to_subgroup ⊤⟩
  unfold CFSG.Open.pCoreOf
  rw [htop, Subgroup.map_top, Subgroup.range_subtype]

theorem suzukiModel_centerQuotient_of_quasisimple_isKGroup {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hK : CFSG.Open.IsKGroup K)
    (h3 : ¬ 3 ∣ Nat.card K) :
    ∃ f : ℕ, CFSG.Blueprint.SuzukiModel (K ⧸ Subgroup.center K) 2 f := by
  classical
  have hZ2 : IsPGroup 2 (Subgroup.center K) :=
    center_isPGroup_two_of_quasisimple_isKGroup hq hK h3
  have hOeq : CFSG.Open.pCoreOf 2 (Subgroup.center K) = Subgroup.center K :=
    pCoreOf_center_eq_of_isPGroup_two hZ2
  let O : Subgroup K := CFSG.Open.pCoreOf 2 (Subgroup.center K)
  have hOle : O ≤ Subgroup.center K := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _
  have hOn : O.Normal := Subgroup.normal_of_le_center hOle
  letI : O.Normal := hOn
  have hqN : CFSG.Open.IsQuasisimple (K ⧸ O) :=
    CFSG.GroupTheory.isQuasisimple_quotient_pCoreOf_center hq
  have hKN : CFSG.Open.IsKGroup (K ⧸ O) := CFSG.Open.IsKGroup.quotient hK O
  have hZodd : Odd (Nat.card (Subgroup.center (K ⧸ O))) :=
    CFSG.GroupTheory.odd_card_center_quotient_pCoreOf_center hq
  have h3N : ¬ 3 ∣ Nat.card (K ⧸ O) := fun h =>
    h3 (h.trans (Subgroup.card_quotient_dvd_card O))
  obtain ⟨-, f, hf⟩ :=
    center_eq_bot_and_suzukiModel_of_not_three_dvd
      hqN hKN hZodd h3N
  have e : (K ⧸ O) ≃* (K ⧸ Subgroup.center K) :=
    QuotientGroup.quotientMulEquivOfEq hOeq
  exact ⟨f, CFSG.CGT.Timmesfeld75.suzukiModel_of_mulEquiv e hf⟩

theorem exists_borel_lift_of_suzuki_quotient {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hZ2 : IsPGroup 2 (Subgroup.center K)) {f : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (K ⧸ Subgroup.center K) 2 f) :
    ∃ (T : Sylow 2 K) (y : K) (r : ℕ),
      r.Prime ∧ r ≠ 2 ∧ orderOf y = r ∧
        y ∈ Subgroup.normalizer (T : Subgroup K) ∧ y ∉ Subgroup.center K := by
  classical
  let Z : Subgroup K := Subgroup.center K
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  let Tbar : Sylow 2 (K ⧸ Z) := default
  have hSz' : CFSG.Quasithin.IsSz f (K ⧸ Z) := hSz
  obtain ⟨hfodd, -, D, hBorel, -, -, hDcard⟩ :=
    CFSG.Quasithin.SBc2.exists_data hSz' Tbar
  have hf3 : 3 ≤ f := by
    obtain ⟨-, a, ha, -, -, -, hf, -, -⟩ := hSz
    omega
  have hDgt : Nat.card D ≠ 1 := by
    rw [hDcard]
    have h1 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd hDgt
  haveI : Fact r.Prime := ⟨hrprime⟩
  have hr2 : r ≠ 2 := by
    intro h2
    have hoddD : Odd (Nat.card D) := by
      rw [hDcard]
      exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
    rw [h2] at hrdvd
    exact (Nat.not_even_iff_odd.mpr hoddD) (even_iff_two_dvd.mpr hrdvd)
  obtain ⟨ybarD, hybarDord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥D) r (by simpa using hrdvd)
  let ybar : K ⧸ Z := (ybarD : K ⧸ Z)
  have hybarOrd : orderOf ybar = r := by
    rw [Subgroup.orderOf_coe, hybarDord]
  have hybarNe : ybar ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hybarOrd
    exact hrprime.ne_one hybarOrd.symm
  have hybarNorm : ybar ∈ Subgroup.normalizer (Tbar : Subgroup (K ⧸ Z)) :=
    hBorel.le ybarD.2
  have hrZ : ¬ r ∣ Nat.card Z := by
    intro hdiv
    obtain ⟨n, hn⟩ := hZ2.exists_card_eq
    rw [hn] at hdiv
    have h2dvd : r ∣ 2 := Nat.Prime.dvd_of_dvd_pow hrprime hdiv
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).mp h2dvd)
  obtain ⟨y, hyOrd, hyMap⟩ :=
    CFSG.GroupTheory.CoprimeTransport.exists_orderOf_eq_prime_mk_eq
      (G := K) (N := Z) (p := r) hrZ hybarOrd
  have hyNotZ : y ∉ Subgroup.center K := by
    intro hy
    have hy1 : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    rw [hyMap] at hy1
    exact hybarNe hy1
  have hker2 : IsPGroup 2 π.ker := by rw [hker]; exact hZ2
  let T : Sylow 2 K := CFSG.sylowComapOfKerIsPGroup π hπ hker2 Tbar
  have hTmap : (T : Subgroup K).map π = (Tbar : Subgroup (K ⧸ Z)) := by
    rw [CFSG.coe_sylowComapOfKerIsPGroup]
    exact Subgroup.map_comap_eq_self_of_surjective hπ Tbar
  have hyNorm : y ∈ Subgroup.normalizer (T : Subgroup K) := by
    refine CFSG.Goldschmidt.G3a.mem_normalizer_of_map T ?_
    rw [hyMap, hTmap]
    exact hybarNorm
  exact ⟨T, y, r, hrprime, hr2, hyOrd, hyNorm, hyNotZ⟩

theorem orbit_components_data (c : Ctx82E3 D) {a : G} {J : Subgroup G}
    (hJ : J ∈ thetaComponentsAt 3 a)
    (hge : 7 ≤ (orbitConjugates (perfectCoreL c a) J).ncard) :
    ∃ (t : ℕ) (A : Fin t → Subgroup G),
      7 ≤ t ∧ (∀ i, A i ∈ thetaComponentsAt 3 a) ∧
        (∀ i, ∃ b ∈ perfectCoreL c a, A i = CFSG.conjugate J b) ∧
          Function.Injective A := by
  classical
  let S : Set (Subgroup G) := orbitConjugates (perfectCoreL c a) J
  let t : ℕ := Nat.card S
  have ht : S.ncard = t := (Nat.card_coe_set_eq S).symm
  have ht7 : 7 ≤ t := by rw [← ht]; exact hge
  let _ : Fintype S := Fintype.ofFinite S
  have hcard : Fintype.card S = t := Nat.card_eq_fintype_card.symm
  let e : S ≃ Fin t := Fintype.equivFinOfCardEq hcard
  let A : Fin t → Subgroup G := fun i => (e.symm i).1
  have hAmem : ∀ i, A i ∈ S := fun i => (e.symm i).2
  have hAinj : Function.Injective A := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  refine ⟨t, A, ht7, ?_, ?_, hAinj⟩
  · intro i
    obtain ⟨b, hb, hbA⟩ := hAmem i
    rw [hbA]
    have hb' : b⁻¹ ∈ perfectCoreL c a := Subgroup.inv_mem _ hb
    exact CFSG.RankThree.PartOne.F106.conj_mem_thetaComponentsAt_cent Nat.prime_three
      (perfectCoreL_le c a hb').2 hJ
  · intro i
    exact hAmem i

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
