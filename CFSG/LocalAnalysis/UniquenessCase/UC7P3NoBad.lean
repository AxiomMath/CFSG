module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Good
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.UniquenessCase.UC7P3GammaLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.StrongP (conjSub mem_conjSub_iff)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree (gammaCore)

variable {G : Type} [Group G] [Finite G]

theorem map_gammaCore_le {p : ℕ} [Fact p.Prime] {J : Type*} [Group J] [Finite J] (f : J →* G)
    (hf : Function.Injective f) (R : Subgroup J) :
    (gammaCore p 1 ⊤ R).map f ≤ gammaCore p 1 ⊤ (R.map f) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨-, S, hSR, hS, hx⟩
  exact Subgroup.subset_closure ⟨Subgroup.mem_top _, S.map f, Subgroup.map_mono hSR,
    hS.trans (CFSG.SectionRank.pRank_le_map (Fact.out : p.Prime).one_lt f hf S),
    Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f hx)⟩

theorem exists_conj_ge_of_gammaCore_eq_top {M J : Subgroup G} (hM : IsStronglyPEmbedded 3 M)
    (R : Sylow 3 ↥J) (hΓ : gammaCore 3 1 ⊤ (R : Subgroup ↥J) = ⊤) :
    ∃ g : G, J ≤ conjSub g M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRG : IsPGroup 3 ↥((R : Subgroup ↥J).map J.subtype) := R.isPGroup'.map J.subtype
  obtain ⟨P, hRP⟩ := hRG.exists_le_sylow
  have hP : CFSG.RankThree.PartOne.IsSylowOf 3 (P : Subgroup G) ⊤ :=
    ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  obtain ⟨g, hg⟩ := hM.exists_conj_ge hP
  have hM' : IsStronglyPEmbedded 3 (conjSub g M) := hM.conj g
  have hle : gammaCore 3 1 ⊤ ((R : Subgroup ↥J).map J.subtype) ≤ conjSub g M := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨-, S, hSR, hS, hy⟩
    exact hM'.normalizer_le (ne_bot_of_one_le_pRank_aux hS) (hRG.to_le hSR)
      (hSR.trans (hRP.trans hg)) hy
  refine ⟨g, fun x hx => ?_⟩
  have hxΓ : (⟨x, hx⟩ : ↥J) ∈ gammaCore 3 1 ⊤ (R : Subgroup ↥J) := by
    rw [hΓ]
    exact Subgroup.mem_top _
  exact hle (map_gammaCore_le (p := 3) J.subtype J.subtype_injective (R : Subgroup ↥J)
    (Subgroup.mem_map_of_mem J.subtype hxΓ))

theorem le_of_le_normalizer_of_dvd_of_strong {p : ℕ} {Y J H : Subgroup G}
    (hY : IsStronglyPEmbedded p Y) (hJY : J ≤ Y) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (hpJ : p ∣ Nat.card J) : H ≤ Y := by
  intro h hh
  by_contra hhY
  refine hY.2.2 h hhY (hpJ.trans (Subgroup.card_dvd_of_le (le_inf hJY fun x hx => ?_)))
  refine mem_conjSub_iff.mpr (hJY ?_)
  have h1 := (Subgroup.mem_normalizer_iff.mp (hHJ (H.inv_mem hh)) x).mp hx
  rwa [inv_inv] at h1

namespace Sec7Core4

theorem exists_layerLift_cover (k : Sec7Core4 G) {H : Subgroup G} (hH : Config k H)
    (h75 : Step75 k) :
    ∃ φ : ↥(layerLift k.p H) →*
        ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)),
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center ↥(layerLift k.p H) := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let π : ↥H →* (↥H ⧸ K₀) := QuotientGroup.mk' K₀
  let Lbar : Subgroup (↥H ⧸ K₀) := CFSG.generalizedFitting (↥H ⧸ K₀)
  let J : Subgroup G := layerLift k.p H
  let KG : Subgroup G := K₀.map H.subtype
  have hJH : J ≤ H := layerLift_le k.p H
  have hsimple := k.isSimpleGroup_generalizedFitting_quotient hH
  haveI : IsSimpleGroup ↥Lbar := hsimple.1
  have hLbarperf : ⁅Lbar, Lbar⁆ = Lbar :=
    Subgroup.isPerfect_iff.mp
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hsimple.2.1).1.1
  have hmap : (J.subgroupOf H).map π = Lbar := map_layerLift_eq k.p H hLbarperf
  let ι : ↥J →* ↥H := Subgroup.inclusion hJH
  let φ₀ : ↥J →* (↥H ⧸ K₀) := π.comp ι
  have hφ₀mem : ∀ x : ↥J, φ₀ x ∈ Lbar := by
    intro x
    have hx : ι x ∈ J.subgroupOf H := Subgroup.mem_subgroupOf.mpr x.2
    have hmem : π (ι x) ∈ (J.subgroupOf H).map π := Subgroup.mem_map_of_mem π hx
    rwa [hmap] at hmem
  let φ : ↥J →* ↥Lbar := φ₀.codRestrict Lbar hφ₀mem
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : ↥H ⧸ K₀) ∈ (J.subgroupOf H).map π := by
      rw [hmap]
      exact y.2
    obtain ⟨h, hh, hπh⟩ := Subgroup.mem_map.mp hy
    have hhJ : (h : G) ∈ J := Subgroup.mem_subgroupOf.mp hh
    refine ⟨⟨(h : G), hhJ⟩, ?_⟩
    apply Subtype.ext
    have hι : ι ⟨(h : G), hhJ⟩ = h := Subtype.ext rfl
    show π (ι ⟨(h : G), hhJ⟩) = (y : ↥H ⧸ K₀)
    rw [hι]
    exact hπh
  have hφker_center : φ.ker ≤ Subgroup.center ↥J := by
    intro x hx
    have hxπ : π (ι x) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxK₀ : ι x ∈ K₀ := by
      rw [← QuotientGroup.ker_mk' K₀]
      exact MonoidHom.mem_ker.mpr hxπ
    have hxKG : (x : G) ∈ KG := Subgroup.mem_map_of_mem H.subtype hxK₀
    have hcommKG : KG ≤ Subgroup.centralizer (J : Set G) := by
      refine (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := KG) (H₂ := J)).mp ?_
      simpa [Subgroup.commutator_comm] using h75 H hH
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcommKG hxKG) (y : G) y.2
  exact ⟨φ, hφsurj, hφker_center⟩

theorem kIDExcluded_of_strongThree (k : Sec7Core4 G) (hp5 : 5 ≤ k.p)
    (h3 : IsStronglyPEmbedded 3 k.M) (hB : BadNoStrongThree) : KIDExcluded k := by
  intro H hH h75 hbad
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let Nbar : Subgroup (↥H ⧸ K₀) := ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' K₀)
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper hH.ne_top
  have hKQ : CFSG.Open.IsKGroup (↥H ⧸ K₀) :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH K₀
  have hO : CFSG.pPrimeCore k.p (↥H ⧸ K₀) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hrank : 2 ≤ CFSG.Open.pRank k.p (⊤ : Subgroup (↥H ⧸ K₀)) :=
    k.two_le_pRank_quotient_pPrimeCore hH
  have hN : IsStronglyPEmbedded k.p Nbar := k.isStronglyPEmbedded_map_quotient_pPrimeCore hH
  have hΓbar := hB k.p hp hp5 (↥H ⧸ K₀) hKQ hO hrank Nbar hN hbad
  obtain ⟨φ, hφsurj, hφker⟩ := k.exists_layerLift_cover hH h75
  have hJperf : Group.IsPerfect ↥(layerLift k.p H) :=
    Subgroup.isPerfect_iff.mpr (commutator_layerLift k.p H)
  obtain ⟨R⟩ : Nonempty (Sylow 3 ↥(layerLift k.p H)) := inferInstance
  have hΓJ := gammaCore_eq_top_of_central_cover 3 hJperf φ hφsurj hφker R
    (hΓbar (R.mapSurjective hφsurj))
  obtain ⟨g, hg⟩ := exists_conj_ge_of_gammaCore_eq_top h3 R hΓJ
  have hpJ : k.p ∣ Nat.card ↥(layerLift k.p H) :=
    (dvd_card_generalizedFitting_quotient k hH).trans (Subgroup.card_dvd_of_surjective hφsurj)
  have hHg : H ≤ conjSub g k.M :=
    le_of_le_normalizer_of_dvd_of_strong (k.strong.conj g) hg (le_normalizer_layerLift k.p H) hpJ
  have hpHM : k.p ∣ Nat.card ↥(H ⊓ k.M) :=
    (dvd_pow_self k.p (by norm_num : (2 : ℕ) ≠ 0)).trans
      ((Nat.pow_dvd_pow k.p hH.two_le_pRank).trans
        (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card k.p hp _))
  have hgM : g ∈ k.M := by
    by_contra hgM
    exact k.strong.2.2 g hgM
      (hpHM.trans (Subgroup.card_dvd_of_le (le_inf inf_le_right (inf_le_left.trans hHg))))
  refine hH.not_le fun x hx => ?_
  have h1 : g⁻¹ * x * g ∈ k.M := mem_conjSub_iff.mp (hHg hx)
  have h2 := k.M.mul_mem (k.M.mul_mem hgM h1) (k.M.inv_mem hgM)
  simpa [mul_assoc] using h2

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
