module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2AutFiveRank
public import TauCeti.GroupTheory.QuotientGroup.MulAut
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.GroupTheory.PowMemSupOfPGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyTwo
public import CFSG.RankThree.PartTwo.Sec17.G1724J2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CentSectionConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSeventeen

public section
namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G}

noncomputable def psiM {D : Data G} {L : Subgroup G}
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G)) :
    ↥D.M →* MulAut (Bar2 L) :=
  (MulAut.mapQuotient (CFSG.pCore 2 ↥L)).comp
    ((Subgroup.normalizerMonoidHom (H := L)).comp
      (Subgroup.inclusion hNL))

theorem psiM_ker {D : Data G} {L : Subgroup G}
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G)) :
    (psiM hNL).ker = (centSection D.M L (pCoreOf 2 L)).subgroupOf D.M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hm
    let φ : MulAut ↥L := (Subgroup.normalizerMonoidHom (H := L))
      (Subgroup.inclusion hNL m)
    have hφ1 : (MulAut.mapQuotient (CFSG.pCore 2 ↥L)) φ = 1 := by
      simpa only [psiM, MonoidHom.comp_apply, φ] using hm
    have hker : φ ∈ (MulAut.mapQuotient (CFSG.pCore 2 ↥L)).ker := by
      rw [MonoidHom.mem_ker]; exact hφ1
    have hcond : ∀ a : ↥L, (φ a : Bar2 L) = (a : Bar2 L) :=
      (MulAut.mem_ker_mapQuotient_iff (N := CFSG.pCore 2 ↥L)).mp hker
    have hBL : D.M ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      fun x hx => CFSG.PreuniquenessRankFour.Helpers.normalizer_le_normalizer_characteristic
        (pCore 2 ↥L) (CFSG.pCore_characteristic (p := 2) (G := ↥L)) (hNL hx)
    refine ⟨m.2, hNL m.2, hBL m.2, ?_⟩
    intro a ha
    let a' : ↥L := ⟨a, ha⟩
    have hmemQ : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (φ a' * a'⁻¹) = 1 := by
      have hq : ((φ a' : Bar2 L) * (a' : Bar2 L)⁻¹) = 1 := by
        rw [hcond a']
        exact mul_inv_cancel _
      simpa using hq
    have hmemB : φ a' * a'⁻¹ ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff (φ a' * a'⁻¹)).mp hmemQ
    have hcoe : ((φ a' * a'⁻¹ : ↥L) : G) = m.1 * a * m.1⁻¹ * a⁻¹ := by
      simp only [φ, a', Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
    have hmap : ((φ a' * a'⁻¹ : ↥L) : G) ∈ pCoreOf 2 L := by
      exact Subgroup.mem_map.mpr ⟨φ a' * a'⁻¹, hmemB, rfl⟩
    rwa [hcoe] at hmap
  · intro hm
    rcases hm with ⟨hmM, hmL, hmB, hcomm⟩
    let φ : MulAut ↥L := (Subgroup.normalizerMonoidHom (H := L))
      (Subgroup.inclusion hNL m)
    have hφeq : φ = (Subgroup.normalizerMonoidHom (H := L))
        (Subgroup.inclusion hNL m) := rfl
    have hcond : ∀ a : ↥L, (φ a : Bar2 L) = (a : Bar2 L) := by
      intro a
      have hmem : φ a * a⁻¹ ∈ CFSG.pCore 2 ↥L := by
        have hcoe : ((φ a * a⁻¹ : ↥L) : G) = m.1 * (a : G) * m.1⁻¹ * (a : G)⁻¹ := by
          simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv,
            Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
        have hmap : ((φ a * a⁻¹ : ↥L) : G) ∈ pCoreOf 2 L := by
          rw [hcoe]
          exact hcomm a a.2
        have hmap' : ((φ a * a⁻¹ : ↥L) : G) ∈ (CFSG.pCore 2 ↥L).map L.subtype := hmap
        obtain ⟨b, hb, hbval⟩ := Subgroup.mem_map.mp hmap'
        have hbeq : b = φ a * a⁻¹ := Subtype.ext hbval
        rwa [hbeq] at hb
      have hq : ((φ a : Bar2 L) * (a : Bar2 L)⁻¹) = 1 := by
        have h := (QuotientGroup.eq_one_iff (φ a * a⁻¹)).mpr hmem
        simpa using h
      exact mul_inv_eq_one.mp hq
    have hψ : (MulAut.mapQuotient (CFSG.pCore 2 ↥L)) φ = 1 := by
      apply MulEquiv.ext
      intro y
      induction y using QuotientGroup.induction_on with
      | H a =>
          rw [MulAut.mapQuotient_mk]
          exact hcond a
    change (MulAut.mapQuotient (CFSG.pCore 2 ↥L)) φ = 1
    exact hψ

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem pRank_centSection_quotient_le_two
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G))
    (hJ2 : IsSpor (Bar2 L) .J2) (hJ2aut : K_J2_aut_five_rank) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (↥D.M ⧸ (psiM (D := D) (L := L) hNL).ker)) ≤ 2 := by
  classical
  have hle : CFSG.Open.pRank 5
      (⊤ : Subgroup (↥D.M ⧸ (psiM (D := D) (L := L) hNL).ker)) ≤
      CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut (Bar2 L))) :=
    CFSG.SectionRank.pRank_top_le_of_injective (p := 5) (by norm_num)
      (QuotientGroup.kerLift (psiM (D := D) (L := L) hNL))
      (QuotientGroup.kerLift_injective _)
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
    CFSG.Sporadic.J2.fam_j2_simplicity.1
  haveI : Fintype (CFSG.Blueprint.NativeSporadic.Carrier .J2) := Fintype.ofFinite _
  haveI : Finite (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J2)) :=
    Finite.of_fintype _
  obtain ⟨e⟩ := hJ2
  have hcard := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num)
    (MulAut.congr e)
  have hJ2aut' := hJ2aut (CFSG.Blueprint.NativeSporadic.Carrier .J2)
    (show IsSpor (CFSG.Blueprint.NativeSporadic.Carrier .J2) .J2 from ⟨MulEquiv.refl _⟩)
  have hEq : CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut (Bar2 L))) =
      CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut
        (CFSG.Blueprint.NativeSporadic.Carrier .J2))) := hcard
  exact hle.trans (le_of_eq (hEq.trans hJ2aut'))

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem five_dvd_centSection
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G))
    (hJ2 : IsSpor (Bar2 L) .J2) (hJ2aut : K_J2_aut_five_rank)
    (hSg : UC6S846.SigmaStd D) (hsig : D.sig = {5}) :
    5 ∣ Nat.card (centSection D.M L (pCoreOf 2 L)) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5sig : 5 ∈ D.sig := by rw [hsig]; simp
  have h3 : 3 ≤ CFSG.Open.pRank 5 D.M := hSg.three_le 5 h5sig
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 5 Nat.prime_five D.M
  by_contra hnot
  have hker := psiM_ker (D := D) (L := L) hNL
  haveI : ((centSection D.M L (pCoreOf 2 L)).subgroupOf D.M).Normal := by
    rw [← hker]; infer_instance
  have hEinf : E ⊓ centSection D.M L (pCoreOf 2 L) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.mp hx
    by_contra hxne
    have hx5 : orderOf x = 5 := by
      have hxpow : x ^ 5 = 1 := hEel.2 x hxE
      have hdvd : orderOf x ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hxpow
      rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
      · exact absurd (orderOf_eq_one_iff.mp h1) hxne
      · exact h5
    have hdvdC : 5 ∣ Nat.card (centSection D.M L (pCoreOf 2 L)) := by
      have h := Subgroup.orderOf_dvd_natCard (centSection D.M L (pCoreOf 2 L)) hxC
      rwa [hx5] at h
    exact hnot hdvdC
  let f : ↥E →* (↥D.M ⧸ (centSection D.M L (pCoreOf 2 L)).subgroupOf D.M) :=
    (QuotientGroup.mk' ((centSection D.M L (pCoreOf 2 L)).subgroupOf D.M)).comp
      (Subgroup.inclusion hEM)
  have hfker : f.ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    intro x y hxy
    let xM : ↥D.M := ⟨x.1, hEM x.2⟩
    let yM : ↥D.M := ⟨y.1, hEM y.2⟩
    have hsub : (xM)⁻¹ * yM ∈
        (centSection D.M L (pCoreOf 2 L)).subgroupOf D.M := by
      have hq : (QuotientGroup.mk' ((centSection D.M L (pCoreOf 2 L)).subgroupOf D.M))
            ((xM)⁻¹ * yM) = 1 := by
        have hxy' : f x = f y := hxy
        change (QuotientGroup.mk' _) xM = (QuotientGroup.mk' _) yM at hxy'
        calc (QuotientGroup.mk' _) ((xM)⁻¹ * yM)
            = (QuotientGroup.mk' _) ((xM)⁻¹) * (QuotientGroup.mk' _) yM := map_mul _ _ _
          _ = ((QuotientGroup.mk' _) xM)⁻¹ * (QuotientGroup.mk' _) yM := by rw [map_inv]
          _ = ((QuotientGroup.mk' _) yM)⁻¹ * (QuotientGroup.mk' _) yM := by rw [hxy']
          _ = 1 := inv_mul_cancel _
      exact (QuotientGroup.eq_one_iff _).mp hq
    have hmem : ((x : G)⁻¹ * (y : G)) ∈ centSection D.M L (pCoreOf 2 L) :=
      Subgroup.mem_subgroupOf.mp hsub
    have hxE : (x : G) ∈ E := x.2
    have hyE : (y : G) ∈ E := y.2
    have hxinv : (x : G)⁻¹ ∈ E := E.inv_mem hxE
    have hxyE : (x : G)⁻¹ * (y : G) ∈ E := E.mul_mem hxinv hyE
    have hbot : (x : G)⁻¹ * (y : G) = 1 := by
      have h := Subgroup.mem_inf.mpr ⟨hxyE, hmem⟩
      rw [hEinf] at h
      exact Subgroup.mem_bot.mp h
    apply Subtype.ext
    have : (x : G)⁻¹ * (y : G) = 1 := hbot
    calc (x : G) = (x : G) * 1 := by simp
      _ = (x : G) * ((x : G)⁻¹ * (y : G)) := by rw [hbot]
      _ = (y : G) := by group
  have hle : CFSG.Open.pRank 5 D.M ≤
      CFSG.Open.pRank 5 (⊤ : Subgroup (↥D.M ⧸
        (centSection D.M L (pCoreOf 2 L)).subgroupOf D.M)) := by
    have hcard : Nat.card ↥E = 5 ^ CFSG.Open.pRank 5 D.M := hEcard
    refine CFSG.SectionRank.le_pRank_of_injective (p := 5) (by norm_num) ?_ ?_
      hcard f ((MonoidHom.ker_eq_bot_iff f).mp hfker)
      (by intro x hx; exact Subgroup.mem_top x)
    · intro a b
      apply Subtype.ext
      exact (CFSG.Open.IsElemAbelian.comm hEel a.2 b.2)
    · intro a
      exact Subtype.ext (hEel.2 a a.2)
  have hbound := pRank_centSection_quotient_le_two (D := D) (L := L) hNL hJ2 hJ2aut
  have hker' := psiM_ker (D := D) (L := L) hNL
  let e := QuotientGroup.quotientMulEquivOfEq hker'
  have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) e
  rw [heq] at hbound
  omega

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

theorem not_strong3_of_J2
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (c : Ctx17_17 D V₀ V L) :
    ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  intro hsp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  rcases h17_22 L P (centerOf P) c hP rfl with hHe | ⟨-, -, hnotΓ, -⟩
  · exact absurd (h17_23 L c) (not_isSpor_He_of_isSpor_J2 (Bar2 L) hHe)
  · exact hnotΓ (CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le_of_le
      hsp (by norm_num) hP.isPGroup (hP.le.trans c.mem_calC.1.le))

theorem evenRank_eq_three_of_J2
    (h880 : F08.R880 D) (hJ2 : IsSpor (Bar2 L) .J2)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (c : Ctx17_17 D V₀ V L) :
    CFSG.Open.evenRank G = 3 := by
  have hlist : F08.List880 (Bar2 L) :=
    list880_of_isSpor (Or.inl rfl) hJ2
  have hns3 := not_strong3_of_J2 (D := D) (V₀ := V₀) (V := V) (L := L)
    h17_22 h17_23 c
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  exact (h880 L c.mem_calC hlist hns3 P hP).2.1.2

theorem two_le_pRank_bar2_J2
    (hJ2 : IsSpor (Bar2 L) .J2) :
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) := by
  classical
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
    CFSG.Sporadic.J2.fam_j2_simplicity.1
  haveI : Fintype (CFSG.Blueprint.NativeSporadic.Carrier .J2) := Fintype.ofFinite _
  obtain ⟨e⟩ := hJ2
  have hrank := CFSG.RankThree.PartTwo.Sec17.G1724.two_le_pRank_five_J2
  have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) e
  rw [heq]
  exact hrank

theorem center_bar2_eq_bot
    (hJ2 : IsSpor (Bar2 L) .J2) :
    Subgroup.center (Bar2 L) = ⊥ := by
  obtain ⟨e⟩ := hJ2
  haveI : IsSimpleGroup (Bar2 L) :=
    (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  refine CFSG.Quasithin.H13.FiveNorm.center_eq_bot_of_card_not_prime ?_
  rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2]
  norm_num

theorem inf_centSection_le_pCore
    (hJ2 : IsSpor (Bar2 L) .J2) :
    L ⊓ centSection D.M L (pCoreOf 2 L) ≤ pCoreOf 2 L := by
  intro x hx
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
  let B : Subgroup ↥L := CFSG.pCore 2 ↥L
  let xL : ↥L := ⟨x, hxL⟩
  have hxbar_center : (QuotientGroup.mk' B xL : Bar2 L) ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H a =>
        have hcomm : (xL : ↥L) * a * (xL : ↥L)⁻¹ * a⁻¹ ∈ B := by
          have h := hxC.2.2.2 a a.2
          have h' : ((xL * a * xL⁻¹ * a⁻¹ : ↥L) : G) ∈ pCoreOf 2 L := by
            simpa [xL, Subgroup.coe_mul, Subgroup.coe_inv] using h
          have hmap' : ((xL * a * xL⁻¹ * a⁻¹ : ↥L) : G) ∈ B.map L.subtype := by
            simpa [B, pCoreOf] using h'
          obtain ⟨b, hb, hbval⟩ := Subgroup.mem_map.mp hmap'
          have hbeq : b = xL * a * xL⁻¹ * a⁻¹ := Subtype.ext hbval
          rwa [hbeq] at hb
        have hq : (QuotientGroup.mk' B (xL * a * xL⁻¹ * a⁻¹) : Bar2 L) = 1 :=
          (QuotientGroup.eq_one_iff (xL * a * xL⁻¹ * a⁻¹)).mpr hcomm
        have hq' : (QuotientGroup.mk' B xL : Bar2 L) * (QuotientGroup.mk' B a) =
            (QuotientGroup.mk' B a) * (QuotientGroup.mk' B xL) := by
          have h1 : (QuotientGroup.mk' B xL : Bar2 L) * (QuotientGroup.mk' B a) *
              (QuotientGroup.mk' B xL)⁻¹ * (QuotientGroup.mk' B a)⁻¹ = 1 := by
            simpa using hq
          exact commutatorElement_eq_one_iff_mul_comm.mp h1
        simpa using hq'.symm
  rw [center_bar2_eq_bot hJ2, Subgroup.mem_bot] at hxbar_center
  have hxmemB : xL ∈ B := (QuotientGroup.eq_one_iff xL).mp hxbar_center
  exact Subgroup.mem_map.mpr ⟨xL, hxmemB, rfl⟩

theorem bar2_conj_eq_of_mem_centSection {f x : G}
    (hf : f ∈ centSection D.M L (pCoreOf 2 L)) (hx : x ∈ L) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨f * x * f⁻¹,
      (Subgroup.mem_normalizer_iff.mp hf.2.1 x).mp hx⟩ : Bar2 L) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx⟩ : Bar2 L) := by
  let B : Subgroup ↥L := CFSG.pCore 2 ↥L
  let a : ↥L := ⟨f * x * f⁻¹, (Subgroup.mem_normalizer_iff.mp hf.2.1 x).mp hx⟩
  let b : ↥L := ⟨x, hx⟩
  have hcomm : f * x * f⁻¹ * x⁻¹ ∈ pCoreOf 2 L := hf.2.2.2 x hx
  have hmemB : a * b⁻¹ ∈ B := by
    have hmap' : ((a * b⁻¹ : ↥L) : G) ∈ B.map L.subtype := by
      simpa [a, b, B, pCoreOf, Subgroup.coe_mul, Subgroup.coe_inv] using hcomm
    obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp hmap'
    have hzeq : z = a * b⁻¹ := Subtype.ext hzval
    rwa [hzeq] at hz
  have hq : (QuotientGroup.mk' B) (a * b⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff (a * b⁻¹)).mpr hmemB
  have hq' : (QuotientGroup.mk' B a : Bar2 L) * ((QuotientGroup.mk' B b : Bar2 L))⁻¹ = 1 := by
    simpa using hq
  exact mul_inv_eq_one.mp hq'

theorem centralizer_map_bar2_eq_top
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G))
    (F : Subgroup G) (hFC : F ≤ centSection D.M L (pCoreOf 2 L))
    (hF5 : IsPGroup 5 F) :
    ((L ⊓ Subgroup.centralizer (F : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : Subgroup ↥L := CFSG.pCore 2 ↥L
  let π : ↥L →* Bar2 L := QuotientGroup.mk' B
  have hFL : F ≤ Subgroup.normalizer (L : Set G) :=
    hFC.trans ((centSection_le _ _ _).trans hNL)
  let ρ : ↥F →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hFL)
  letI : MulDistribMulAction ↥F ↥L := MulDistribMulAction.compHom ↥L ρ
  let ρbar : ↥F →* MulAut (Bar2 L) :=
    (MulAut.mapQuotient B).comp ρ
  letI : MulDistribMulAction ↥F (Bar2 L) := MulDistribMulAction.compHom (Bar2 L) ρbar
  have hequiv : ∀ (a : ↥F) (x : ↥L), π (a • x) = a • π x := by
    intro a x
    change π (ρ a x) = (MulAut.mapQuotient B) (ρ a) (π x)
    exact (MulAut.mapQuotient_mk (N := B) (φ := ρ a) x).symm
  have hker : π.ker = (CFSG.pCore 2 ↥L : Subgroup ↥L) := by
    exact QuotientGroup.ker_mk' B
  have hcop : ¬ 5 ∣ Nat.card ↥π.ker := by
    rw [hker]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hk]
    intro hd
    exact (by norm_num : ¬ (5 : ℕ) ∣ 2)
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd)
  have hfixed : ∀ (a : ↥F) (y : Bar2 L), a • y = y := by
    intro a y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective B y
    change (MulAut.mapQuotient B) (ρ a) (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [MulAut.mapQuotient_mk]
    exact bar2_conj_eq_of_mem_centSection (hFC a.2) x.2
  rw [eq_top_iff]
  intro y hy
  obtain ⟨x0, hx0⟩ := QuotientGroup.mk'_surjective B y
  obtain ⟨x, hxval, hxfix⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_fixed_lift
      (G := ↥L) (K := Bar2 L) (A := ↥F) 5 hF5 π hequiv hcop y
      ⟨x0, hx0⟩ (fun a => hfixed a y)
  refine Subgroup.mem_map.mpr ⟨x, ?_, hxval⟩
  refine Subgroup.mem_subgroupOf.mpr ?_
  refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hfix := hxfix ⟨f, hf⟩
  change ρ ⟨f, hf⟩ x = x at hfix
  have hval : ((ρ ⟨f, hf⟩ x : ↥L) : G) = f * (x : G) * f⁻¹ := by
    simp [ρ, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
  have : f * (x : G) * f⁻¹ = (x : G) := by
    rw [← hval, hfix]
  calc f * (x : G) = (f * (x : G) * f⁻¹) * f := by group
    _ = (x : G) * f := by rw [this]

theorem two_le_pRank_centralizer
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G))
    (hJ2 : IsSpor (Bar2 L) .J2)
    (F : Subgroup G) (hFC : F ≤ centSection D.M L (pCoreOf 2 L))
    (hF5 : IsPGroup 5 F) :
    2 ≤ CFSG.Open.pRank 5 (L ⊓ Subgroup.centralizer (F : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let CL : Subgroup G := L ⊓ Subgroup.centralizer (F : Set G)
  have hCLle : CL ≤ L := inf_le_left
  let K : Subgroup ↥L := CL.subgroupOf L
  let B : Subgroup ↥L := CFSG.pCore 2 ↥L
  let π : ↥L →* Bar2 L := QuotientGroup.mk' B
  have hKmap : K.map π = ⊤ := by
    simpa [CL, K, B, π] using centralizer_map_bar2_eq_top (D := D) (L := L) hNL F hFC hF5
  have hsurj : Function.Surjective (π.comp K.subtype) := by
    intro y
    have hy : y ∈ K.map π := by rw [hKmap]; exact Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, hxy⟩
  let φ : ↥K →* Bar2 L := π.comp K.subtype
  let N : Subgroup ↥K := B.subgroupOf K
  have hNker : φ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change π x.1 = 1 ↔ (x.1 : ↥L) ∈ B
    exact QuotientGroup.eq_one_iff (x.1 : ↥L)
  have hN2 : IsPGroup 2 ↥N := by
    let f : ↥N →* ↥B :=
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.mp x.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl }
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).of_injective f
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : ↥B => (z : ↥L)) h)))
  have hNcop : ¬ 5 ∣ Nat.card ↥N := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    rw [hk]
    intro hd
    exact (by norm_num : ¬ (5 : ℕ) ∣ 2)
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd)
  have hquot : CFSG.Open.pRank 5 (⊤ : Subgroup (↥K ⧸ N)) =
      CFSG.Open.pRank 5 (⊤ : Subgroup ↥K) :=
    CFSG.SectionRank.pRank_quotient_eq N hNcop
  have hbar : CFSG.Open.pRank 5 (⊤ : Subgroup (↥K ⧸ N)) =
      CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) := by
    let eQ : (↥K ⧸ N) ≃* Bar2 L :=
      (QuotientGroup.quotientMulEquivOfEq hNker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) eQ
  have hK : CFSG.Open.pRank 5 (⊤ : Subgroup ↥K) =
      CFSG.Open.pRank 5 (⊤ : Subgroup ↥CL) := by
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num)
      (Subgroup.subgroupOfEquivOfLe hCLle)
  have h2bar : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) :=
    two_le_pRank_bar2_J2 (L := L) hJ2
  have hCLtop : CFSG.Open.pRank 5 CL =
      CFSG.Open.pRank 5 (⊤ : Subgroup ↥CL) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup CL
  have hchain : CFSG.Open.pRank 5 CL =
      CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) := by
    calc CFSG.Open.pRank 5 CL
        = CFSG.Open.pRank 5 (⊤ : Subgroup ↥CL) := hCLtop
      _ = CFSG.Open.pRank 5 (⊤ : Subgroup ↥K) := hK.symm
      _ = CFSG.Open.pRank 5 (⊤ : Subgroup (↥K ⧸ N)) := hquot.symm
      _ = CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) := hbar
  rw [hchain]
  exact h2bar

theorem pRank_five_centSection_le_one
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G))
    (hJ2 : IsSpor (Bar2 L) .J2) (h880 : F08.R880 D)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (c : Ctx17_17 D V₀ V L) :
    CFSG.Open.pRank 5 (centSection D.M L (pCoreOf 2 L)) ≤ 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  have h2C : 2 ≤ CFSG.Open.pRank 5 (centSection D.M L (pCoreOf 2 L)) := by omega
  obtain ⟨F, hFC, hFel, hFcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 5 Nat.prime_five
      (centSection D.M L (pCoreOf 2 L))
  have hF5 : IsPGroup 5 F := hFel.isPGroup
  have h2CL : 2 ≤ CFSG.Open.pRank 5 (L ⊓ Subgroup.centralizer (F : Set G)) :=
    two_le_pRank_centralizer (D := D) (L := L) hNL hJ2 F hFC hF5
  obtain ⟨E, hECL, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 5 Nat.prime_five
      (L ⊓ Subgroup.centralizer (F : Set G))
  have hEL : E ≤ L := hECL.trans inf_le_left
  have hECF : E ≤ Subgroup.centralizer (F : Set G) := hECL.trans inf_le_right
  have hE5 : IsPGroup 5 E := hEel.isPGroup
  have hEinfF : E ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxF⟩ := Subgroup.mem_inf.mp hx
    have hxLC : x ∈ L ⊓ centSection D.M L (pCoreOf 2 L) :=
      Subgroup.mem_inf.mpr ⟨hEL hxE, hFC hxF⟩
    have hxO2 : x ∈ pCoreOf 2 L := inf_centSection_le_pCore (D := D) (L := L) hJ2 hxLC
    have hx2 : orderOf x ∣ Nat.card (pCoreOf 2 L) :=
      Subgroup.orderOf_dvd_natCard (pCoreOf 2 L) hxO2
    have hx5 : orderOf x ∣ Nat.card E := Subgroup.orderOf_dvd_natCard E hxE
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hE5
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    have h2 : Nat.card (pCoreOf 2 L) = 2 ^ b := by
      rw [show pCoreOf 2 L = (CFSG.pCore 2 ↥L).map L.subtype from rfl,
        Subgroup.card_map_of_injective L.subtype_injective, hb]
    rw [ha] at hx5
    rw [h2] at hx2
    have hdvd : orderOf x ∣ Nat.gcd (5 ^ a) (2 ^ b) := Nat.dvd_gcd hx5 hx2
    have hgcd : Nat.gcd (5 ^ a) (2 ^ b) = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow a b (by norm_num : Nat.Coprime 5 2))
    rw [hgcd] at hdvd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  have hcomm : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e := by
    intro e he f hf
    exact (Subgroup.mem_centralizer_iff.mp (hECF he) f hf).symm
  have hEFel : IsElemAbelian 5 (E ⊔ F) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hEel hFel hcomm
  have hFleCE : F ≤ Subgroup.centralizer (E : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact hcomm e he f hf
  have hFnormE : F ≤ Subgroup.normalizer (E : Set G) :=
    hFleCE.trans (Subgroup.centralizer_le_normalizer (E : Set G))
  have hcardEF : Nat.card ↥(E ⊔ F) = Nat.card E * Nat.card F :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E F hFnormE
      (disjoint_iff.mpr hEinfF)
  have hEFM : E ⊔ F ≤ D.M :=
    sup_le (hEL.trans c.mem_calC.1.le) (hFC.trans (centSection_le _ _ _))
  have hcard5 : Nat.card ↥(E ⊔ F) = 5 ^
      (CFSG.Open.pRank 5 (centSection D.M L (pCoreOf 2 L)) +
        CFSG.Open.pRank 5 (L ⊓ Subgroup.centralizer (F : Set G))) := by
    rw [hcardEF, hEcard, hFcard, ← pow_add, add_comm]
  have h4M : 4 ≤ CFSG.Open.pRank 5 D.M := by
    have hsum : 4 ≤ CFSG.Open.pRank 5 (centSection D.M L (pCoreOf 2 L)) +
        CFSG.Open.pRank 5 (L ⊓ Subgroup.centralizer (F : Set G)) := by omega
    exact hsum.trans (CFSG.SectionRank.le_pRank (p := 5) (by norm_num) hEFM hEFel hcard5)
  have h4e : 4 ≤ CFSG.Open.evenRank G :=
    h4M.trans (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank
      5 Nat.prime_five (by norm_num) D.M D.maxLocal.1)
  have he3 : CFSG.Open.evenRank G = 3 :=
    evenRank_eq_three_of_J2 (D := D) (V₀ := V₀) (V := V) (L := L)
      h880 hJ2 h17_22 h17_23 c
  omega

theorem pRank_five_centSection_eq_one
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G))
    (hJ2 : IsSpor (Bar2 L) .J2) (hJ2aut : K_J2_aut_five_rank)
    (hSg : UC6S846.SigmaStd D) (hsig : D.sig = {5}) (h880 : F08.R880 D)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (c : Ctx17_17 D V₀ V L) :
    CFSG.Open.pRank 5 (centSection D.M L (pCoreOf 2 L)) = 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5dvd : 5 ∣ Nat.card (centSection D.M L (pCoreOf 2 L)) :=
    five_dvd_centSection (D := D) (L := L) hNL hJ2 hJ2aut hSg hsig
  have h1 : 1 ≤ CFSG.Open.pRank 5 (centSection D.M L (pCoreOf 2 L)) := by
    obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centSection D.M L (pCoreOf 2 L)))
      5 (by simpa using h5dvd)
    let X : Subgroup G := Subgroup.zpowers (x : G)
    have hXle : X ≤ centSection D.M L (pCoreOf 2 L) :=
      Subgroup.zpowers_le.mpr x.2
    have hxpow : x ^ 5 = 1 := by
      rw [← hx5]
      exact pow_orderOf_eq_one x
    have hX5 : (x : G) ^ 5 = 1 := by
      simpa using congrArg (fun y : ↥(centSection D.M L (pCoreOf 2 L)) => (y : G)) hxpow
    have hXel : IsElemAbelian 5 X := CFSG.Open.isElemAbelian_zpowers hX5
    have hXcard : Nat.card X = 5 ^ 1 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx5, pow_one]
    exact CFSG.SectionRank.le_pRank (p := 5) (by norm_num) hXle hXel hXcard
  have hle := pRank_five_centSection_le_one (D := D) (V₀ := V₀) (V := V) (L := L)
    hNL hJ2 h880 h17_22 h17_23 c
  omega

theorem solvable_centSection_of_J2
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (c : Ctx17_17 D V₀ V L) :
    Group.IsSolvable ↥(centSection D.M L (pCoreOf 2 L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  rcases h17_22 L P (centerOf P) c hP rfl with hHe | ⟨-, -, -, -, -, -, hsolv⟩
  · exact absurd (h17_23 L c) (not_isSpor_He_of_isSpor_J2 (Bar2 L) hHe)
  · exact hsolv

theorem solvable_sup_T_centSection
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G))
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (c : Ctx17_17 D V₀ V L) :
    Group.IsSolvable ↥(D.T ⊔ centSection D.M L (pCoreOf 2 L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centSection D.M L (pCoreOf 2 L)
  let Y : Subgroup G := D.T ⊔ C
  have hCY : C ≤ Y := le_sup_right
  have hCnormM : D.M ≤ Subgroup.normalizer (C : Set G) :=
    centSection_le_normalizer (M := D.M) (L := L) hNL
  have hYnorm : Y ≤ Subgroup.normalizer (C : Set G) :=
    (sup_le D.sylowM.le (centSection_le _ _ _)).trans hCnormM
  let N : Subgroup ↥Y := C.subgroupOf Y
  have hNnormal : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCY).mpr hYnorm
  have hCsolv : Group.IsSolvable ↥C :=
    solvable_centSection_of_J2 (D := D) (V₀ := V₀) (V := V) (L := L) h17_22 h17_23 c
  have hNsolv : Group.IsSolvable ↥N := by
    have e : ↥N ≃* ↥C := Subgroup.subgroupOfEquivOfLe hCY
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hQ2 : IsPGroup 2 (↥Y ⧸ N) :=
    CFSG.GroupTheory.isPGroup_quotient_sup_left (p := 2) D.sylowM.isPGroup
  have hQsolv : Group.IsSolvable (↥Y ⧸ N) :=
    @IsNilpotent.to_isSolvable (↥Y ⧸ N) _ (hQ2.isNilpotent)
  exact Group.isSolvable_of_subgroup_quotient N

theorem pRank_five_sup_le_one
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G))
    (hJ2 : IsSpor (Bar2 L) .J2) (hJ2aut : K_J2_aut_five_rank)
    (hSg : UC6S846.SigmaStd D) (hsig : D.sig = {5}) (h880 : F08.R880 D)
    (h17_22 : R17_22At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (c : Ctx17_17 D V₀ V L) :
    CFSG.Open.pRank 5 (D.T ⊔ centSection D.M L (pCoreOf 2 L)) ≤ 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centSection D.M L (pCoreOf 2 L)
  let Y : Subgroup G := D.T ⊔ C
  have hCY : C ≤ Y := le_sup_right
  have hPRC : CFSG.Open.pRank 5 C ≤ 1 := by
    rw [show CFSG.Open.pRank 5 C = 1 from
      pRank_five_centSection_eq_one (D := D) (V₀ := V₀) (V := V) (L := L)
        hNL hJ2 hJ2aut hSg hsig h880 h17_22 h17_23 c]
  have hYnorm : Y ≤ Subgroup.normalizer (C : Set G) :=
    (sup_le D.sylowM.le (centSection_le _ _ _)).trans
      (centSection_le_normalizer (M := D.M) (L := L) hNL)
  have hNnormalY : (C.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCY).mpr hYnorm
  letI := hNnormalY
  have hQ2 : IsPGroup 2 (↥Y ⧸ (C.subgroupOf Y)) :=
    CFSG.GroupTheory.isPGroup_quotient_sup_left (p := 2) D.sylowM.isPGroup
  have hYP : ∀ E : Subgroup G, E ≤ Y → IsElemAbelian 5 E → E ≤ C := by
    intro E hEY hEel
    intro e he
    let eY : ↥Y := ⟨e, hEY he⟩
    have hpow : e ^ 5 = 1 := hEel.2 e he
    have hdvd5 : orderOf (QuotientGroup.mk' (C.subgroupOf Y) eY) ∣ 5 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have hpowY : eY ^ 5 = 1 := Subtype.ext hpow
      have h1 : (QuotientGroup.mk' (C.subgroupOf Y) eY) ^ 5 = 1 := by
        simpa using congrArg (QuotientGroup.mk' (C.subgroupOf Y)) hpowY
      exact h1
    have hdvd2 : orderOf (QuotientGroup.mk' (C.subgroupOf Y) eY) ∣
        Nat.card (↥Y ⧸ (C.subgroupOf Y)) := by
      have h := Subgroup.orderOf_dvd_natCard
        (⊤ : Subgroup (↥Y ⧸ (C.subgroupOf Y)))
        (show (QuotientGroup.mk' (C.subgroupOf Y) eY) ∈
          (⊤ : Subgroup (↥Y ⧸ (C.subgroupOf Y))) from Subgroup.mem_top _)
      simpa using h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
    rw [hk] at hdvd2
    have hdvd : orderOf (QuotientGroup.mk' (C.subgroupOf Y) eY) ∣
        Nat.gcd 5 (2 ^ k) := Nat.dvd_gcd hdvd5 hdvd2
    have hgcd : Nat.gcd 5 (2 ^ k) = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 5 2))
    rw [hgcd] at hdvd
    have hone : (QuotientGroup.mk' (C.subgroupOf Y) eY) = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    exact (QuotientGroup.eq_one_iff eY).mp hone
  obtain ⟨E, hEY, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 5 Nat.prime_five Y
  have hEC : E ≤ C := hYP E hEY hEel
  have hleYC : CFSG.Open.pRank 5 Y ≤ CFSG.Open.pRank 5 C :=
    CFSG.SectionRank.le_pRank (p := 5) (by norm_num) hEC hEel hEcard
  exact hleYC.trans hPRC

end S17
