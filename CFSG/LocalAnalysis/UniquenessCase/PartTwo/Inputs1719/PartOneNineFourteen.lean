module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOneNineNarrow
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4Aux
import CFSG.LocalAnalysis.UniquenessCase.UCFront09q
import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover
import CFSG.Quasithin.H13.NQBlockCommonResidual
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactWiring3Kf1
import CFSG.LocalAnalysis.UniquenessCase.UCFront09l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartTwo (fixedSubgroupOf mem_fixedSubgroupOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09
open CFSG.SignalizerFunctorTheorem.McBride.Near (IsChiefFactorOf)

variable {G : Type} [Group G] [Finite G]

private theorem ne_top_of_hyp97' {D : Data G} {Y H D₃ S : Subgroup G} (hY : Hyp97 D Y H D₃ S) :
    H ≠ ⊤ := by
  haveI := D.standing.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : H ≠ ⊥ := by
    intro h
    have hD : D₃ ≤ ⊥ := h ▸ hY.1.2.2.1.trans ((opp_le_self 3 Y).trans hY.1.2.1.1)
    have h3 := hY.1.2.2.2
    rw [le_bot_iff.1 hD, card_bot] at h3
    exact absurd h3 (by norm_num)
  have hne := CFSG.LocalAnalysis.UniquenessCase.PartTwo.pCoreOf_ne_bot_of_fstar hY.2.2.1.2 hH
  intro htop
  refine CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab
    (show IsTwoLocal (normalizer (pCoreOf 2 H : Set G)) from
      ⟨pCoreOf 2 H, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, rfl⟩) ?_
  exact top_le_iff.1 (htop.ge.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))

private theorem chiefFactor_subgroupOf_normal {H A B : Subgroup G}
    (hc : IsChiefFactorOf H A B) :
    (B.subgroupOf H).Normal ∧ (A.subgroupOf H).Normal :=
  ⟨Subgroup.normal_subgroupOf_of_le_normalizer hc.1.2,
    Subgroup.normal_subgroupOf_of_le_normalizer hc.2.1.2⟩

private theorem chiefFactor_map_minimal {H A B : Subgroup G}
    [hB : (B.subgroupOf H).Normal] (hc : IsChiefFactorOf H A B) :
    ∀ N : Subgroup (↥H ⧸ B.subgroupOf H), N.Normal →
      N ≤ (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) →
        N = ⊥ ∨ N = (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) := by
  intro N hNn hNK
  let π : ↥H →* (↥H ⧸ B.subgroupOf H) := QuotientGroup.mk' (B.subgroupOf H)
  let K : Subgroup G := (N.comap π).map H.subtype
  have hBAH : B.subgroupOf H ≤ A.subgroupOf H := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact hc.2.2.1.le hz
  have hNpre_le : N.comap π ≤ A.subgroupOf H := by
    intro x hx
    have hxK : π x ∈ (A.subgroupOf H).map π := hNK hx
    obtain ⟨y, hyA, hyx⟩ := Subgroup.mem_map.1 hxK
    have hmemB : y⁻¹ * x ∈ B.subgroupOf H := by
      have h1 : π (y⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, ← hyx]
        exact inv_mul_cancel _
      have h1' : QuotientGroup.mk' (B.subgroupOf H) (y⁻¹ * x) = 1 := h1
      rw [QuotientGroup.mk'_apply] at h1'
      rw [← QuotientGroup.eq_one_iff (y⁻¹ * x)]
      exact h1'
    have hx_eq : x = y * (y⁻¹ * x) := by group
    rw [hx_eq]
    exact (A.subgroupOf H).mul_mem hyA (hBAH hmemB)
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hKsub : K.subgroupOf H = N.comap π :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective (N.comap π)
  have hKn : (K.subgroupOf H).Normal := by
    rw [hKsub]
    exact hNn.comap π
  haveI : (K.subgroupOf H).Normal := hKn
  have hKnorm : H ≤ normalizer (K : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hKH
  have hBK : B ≤ K := by
    intro b hb
    refine Subgroup.mem_map.mpr ⟨⟨b, hc.1.1 hb⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h1 : π ⟨b, hc.1.1 hb⟩ = 1 := by
      change QuotientGroup.mk' (B.subgroupOf H) ⟨b, hc.1.1 hb⟩ = 1
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (⟨b, hc.1.1 hb⟩ : ↥H)).mpr hb
    rw [h1]
    exact N.one_mem
  have hKA : K ≤ A := by
    calc K = (N.comap π).map H.subtype := rfl
      _ ≤ (A.subgroupOf H).map H.subtype := Subgroup.map_mono hNpre_le
      _ = A := Subgroup.map_subgroupOf_eq_of_le hc.2.1.1
  rcases hc.2.2.2 K ⟨hKH, hKnorm⟩ hBK hKA with hKB | hKAeq
  · left
    have hNpre_eq : N.comap π = B.subgroupOf H := by
      calc N.comap π = ((N.comap π).map H.subtype).subgroupOf H :=
            (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm
        _ = K.subgroupOf H := rfl
        _ = B.subgroupOf H := by rw [hKB]
    have hmapbot : (B.subgroupOf H).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro x hx
      exact (QuotientGroup.eq_one_iff x).mpr hx
    calc N = (N.comap π).map π :=
          (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) N).symm
      _ = (B.subgroupOf H).map π := by rw [hNpre_eq]
      _ = ⊥ := hmapbot
  · right
    have hNpre_eq : N.comap π = A.subgroupOf H := by
      calc N.comap π = ((N.comap π).map H.subtype).subgroupOf H :=
            (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm
        _ = K.subgroupOf H := rfl
        _ = A.subgroupOf H := by rw [hKAeq]
    calc N = (N.comap π).map π :=
          (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) N).symm
      _ = (A.subgroupOf H).map π := by rw [hNpre_eq]

private theorem chiefFactor_map_not_isMulCommutative {H A B : Subgroup G}
    [hB : (B.subgroupOf H).Normal] [hBA : (B.subgroupOf A).Normal]
    (hc : IsChiefFactorOf H A B)
    (hns : ¬ Group.IsSolvable (↥A ⧸ B.subgroupOf A)) :
    ¬ IsMulCommutative ↥((A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H))) := by
  let π : ↥H →* (↥H ⧸ B.subgroupOf H) := QuotientGroup.mk' (B.subgroupOf H)
  let f : ↥A →* ↥((A.subgroupOf H).map π) :=
    { toFun := fun a =>
        ⟨π ⟨(a : G), hc.2.1.1 a.2⟩,
          Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr a.2)⟩
      map_one' := by
        ext
        change (QuotientGroup.mk' (B.subgroupOf H)) ⟨1, _⟩ = 1
        rw [QuotientGroup.mk'_apply]
        exact map_one (QuotientGroup.mk' (B.subgroupOf H))
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_mk, map_mul]
        rfl }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
    ext
    exact hxy
  have hker : f.ker = B.subgroupOf A := by
    ext a
    constructor
    · intro ha
      have h1 : f a = 1 := MonoidHom.mem_ker.mp ha
      have h2 : π ⟨(a : G), hc.2.1.1 a.2⟩ = 1 := congrArg Subtype.val h1
      have h3 : (⟨(a : G), hc.2.1.1 a.2⟩ : ↥H) ∈ B.subgroupOf H := by
        rw [QuotientGroup.mk'_apply] at h2
        rw [← QuotientGroup.eq_one_iff]
        exact h2
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h3)
    · intro ha
      have haB : (a : G) ∈ B := Subgroup.mem_subgroupOf.mp ha
      apply MonoidHom.mem_ker.mpr
      ext
      change π ⟨(a : G), hc.2.1.1 a.2⟩ = 1
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (⟨(a : G), hc.2.1.1 a.2⟩ : ↥H)).mpr haB
  let e : (↥A ⧸ B.subgroupOf A) ≃* ↥((A.subgroupOf H).map π) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  intro hcomm
  haveI : Group.IsSolvable ↥((A.subgroupOf H).map π) :=
    Group.isSolvable_of_comm fun a b => hcomm.is_comm.comm a b
  exact hns (CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv e.symm)

private theorem chiefFactor_three_not_dvd {H A B : Subgroup G}
    [hB : (B.subgroupOf H).Normal] (hc : IsChiefFactorOf H A B)
    (hAI : A ≤ PPrimeCoreIn 3 H) :
    ¬ 3 ∣ Nat.card ↥((A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H))) ∧
      ¬ 3 ∣ Nat.card B := by
  constructor
  · intro h
    have hdvd1 : Nat.card ↥((A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H))) ∣
        Nat.card ↥(A.subgroupOf H) :=
      Subgroup.card_map_dvd (A.subgroupOf H) (QuotientGroup.mk' (B.subgroupOf H))
    have hcardA : Nat.card ↥(A.subgroupOf H) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.2.1.1).toEquiv
    have hdvd2 : Nat.card A ∣ Nat.card (PPrimeCoreIn 3 H) := Subgroup.card_dvd_of_le hAI
    exact not_dvd_card_I9 H (h.trans (hdvd1.trans (hcardA ▸ hdvd2)))
  · intro h
    have hdvd : Nat.card B ∣ Nat.card (PPrimeCoreIn 3 H) :=
      Subgroup.card_dvd_of_le (hc.2.2.1.le.trans hAI)
    exact not_dvd_card_I9 H (h.trans hdvd)

theorem r9_14S_holds
    (D : Data G) : R9_14S D := by
  intro Y H D₃ S h97 S₀ hS₀ hS₀M A B hBinst hc hAI hns
  haveI : (B.subgroupOf A).Normal := hBinst
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHtop : H ≠ ⊤ := ne_top_of_hyp97' h97
  have hD₃H : D₃ ≤ H :=
    h97.1.2.2.1.trans ((opp_le_self 3 Y).trans h97.1.2.1.1)
  have hD₃3 : Nat.card D₃ = 3 := h97.1.2.2.2
  have hD₃U : D₃ ∈ uniqueSet D.M :=
    h97.1.1.2.2 D₃ (h97.1.2.2.1.trans (opp_le_self 3 Y)) hD₃3
  have hCD : Subgroup.centralizer (D₃ : Set G) ≤ D.M :=
    (Subgroup.centralizer_le_normalizer (s := (D₃ : Set G))).trans
      (normalizer_le_of_mem_uniqueSet D.maxLocal hD₃U)
  obtain ⟨hBnor, hAnor⟩ := chiefFactor_subgroupOf_normal hc
  haveI : (B.subgroupOf H).Normal := hBnor
  have hBA : B ≤ A := hc.2.2.1.le
  have hAH : A ≤ H := hc.2.1.1
  have hBH : B ≤ H := hc.1.1
  let π : ↥H →* (↥H ⧸ B.subgroupOf H) := QuotientGroup.mk' (B.subgroupOf H)
  let Kbar : Subgroup (↥H ⧸ B.subgroupOf H) := (A.subgroupOf H).map π
  let W : Subgroup (↥H ⧸ B.subgroupOf H) := ((H ⊓ D.M).subgroupOf H).map π
  let T : Subgroup (↥H ⧸ B.subgroupOf H) := (S₀.subgroupOf H).map π
  have hKbarNormal : Kbar.Normal := hAnor.map π (QuotientGroup.mk'_surjective _)
  have hKbarMin : ∀ N : Subgroup (↥H ⧸ B.subgroupOf H), N ≤ Kbar →
      (N.subgroupOf Kbar).Normal → ⊤ ≤ normalizer (N : Set (↥H ⧸ B.subgroupOf H)) →
        N = ⊥ ∨ N = Kbar := by
    intro N hNK _ hnorm
    have hNn : N.Normal :=
      Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hnorm)
    exact chiefFactor_map_minimal (hB := hBnor) hc N hNn hNK
  have hKbarNC : ∃ x ∈ Kbar, ∃ y ∈ Kbar, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hcomm : IsMulCommutative ↥Kbar :=
      IsMulCommutative.of_comm fun x y => Subtype.ext (hcon x x.2 y y.2)
    exact chiefFactor_map_not_isMulCommutative hc hns hcomm
  obtain ⟨h3Kbar, h3B⟩ := chiefFactor_three_not_dvd hc hAI
  obtain ⟨r, Sfac, _, hSfacK, hSfacNorm, hSfacSimple, hSfacNC, _, _, hSfacSup⟩ :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.exists_aSimple_factors
      (A := ⊤) (K := Kbar)
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hKbarNormal])
      hKbarNC hKbarMin
  have hSfacNCN : ∀ i, ∃ a b : ↥(Sfac i), a * b ≠ b * a := fun i => by
    obtain ⟨x, hx, y, hy, hxy⟩ := hSfacNC i
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  have hSfacComp : ∀ i, CFSG.IsComponent (Sfac i) := fun i =>
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (hSfacNCN i)).1,
      Subgroup.IsSubnormal.step (Sfac i) Kbar (hSfacK i) hKbarNormal.isSubnormal
        (hSfacNorm i)⟩
  have hSfacZ : ∀ i, center ↥(Sfac i) = ⊥ := fun i =>
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (hSfacNCN i)).2
  have hKΓ : CFSG.IsKGroup (↥H ⧸ B.subgroupOf H) :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.isKGroup_of_ne_top_of_isKProper
      D.standing.kProper hHtop).quotient (B.subgroupOf H)
  have hcat : ∀ i, CFSG.Assembly.InCatalog ↥(Sfac i) := fun i => by
    haveI : IsSimpleGroup ↥(Sfac i) := hSfacSimple i
    exact hKΓ.inCatalog_of_surjective (Sfac i) (MonoidHom.id _) Function.surjective_id
  have hSz : ∀ i, ∃ f : ℕ, CFSG.Blueprint.SuzukiModel ↥(Sfac i) 2 f := fun i => by
    haveI : IsSimpleGroup ↥(Sfac i) := hSfacSimple i
    exact CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd
      ↥(Sfac i) (hSfacNCN i) (hcat i) fun h =>
        h3Kbar (h.trans (Subgroup.card_dvd_of_le (hSfacK i)))
  haveI : IsCyclic D₃ := isCyclic_of_prime_card hD₃3
  obtain ⟨d, hd⟩ := IsCyclic.exists_generator (α := ↥D₃)
  have hd3 : (d : G) ^ 3 = 1 := by
    have h : d ^ Nat.card D₃ = 1 := pow_card_eq_one'
    rw [hD₃3] at h
    exact_mod_cast congrArg Subtype.val h
  let g0 : ↥H := ⟨(d : G), hD₃H d.2⟩
  have hg0 : g0 ^ 3 = 1 := by
    apply Subtype.ext
    change (d : G) ^ 3 = 1
    exact hd3
  let σ : MulAut (↥H ⧸ B.subgroupOf H) := MulAut.conj (π g0)
  have hσ3 : σ ^ 3 = 1 := by
    have hπg0 : (π g0) ^ 3 = 1 := by
      simpa using congrArg π hg0
    calc σ ^ 3 = MulAut.conj ((π g0) ^ 3) := by rw [← map_pow]
      _ = MulAut.conj 1 := by rw [hπg0]
      _ = 1 := map_one
        (MulAut.conj : (↥H ⧸ B.subgroupOf H) →* MulAut (↥H ⧸ B.subgroupOf H))
  have hfix : fixedSubgroupOf σ ≤ W := by
    intro x hx
    rw [mem_fixedSubgroupOf] at hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf H) x
    have hcomm : Commute (π h) (π g0) := by
      rw [commute_iff_eq]
      have hfixeq := hx
      rw [MulAut.conj_apply] at hfixeq
      calc π h * π g0 = (π g0 * π h * (π g0)⁻¹) * π g0 := by rw [hfixeq]
        _ = π g0 * π h := by group
    have hcomm' : ∀ d' : ↥D₃,
        Commute (π h) (π (⟨(d' : G), hD₃H d'.2⟩ : ↥H)) := by
      intro d'
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hd d')
      have hgk : (⟨(d' : G), hD₃H d'.2⟩ : ↥H) = g0 ^ k := by
        apply Subtype.ext
        change (d' : G) = (d : G) ^ k
        simpa using (congrArg Subtype.val hk).symm
      rw [hgk, map_zpow]
      exact hcomm.zpow_right k
    have hfixB : ∀ d' ∈ D₃,
        (h : G)⁻¹ * ((d' : G)⁻¹ * (h : G) * (d' : G)) ∈ B := by
      intro d' hd'
      let g' : ↥H := ⟨(d' : G), hD₃H hd'⟩
      have hcommd : Commute (π h) (π g') := hcomm' ⟨d', hd'⟩
      have hmemΓ : π (h⁻¹ * (g'⁻¹ * h * g')) = 1 := by
        have h1 : (π g')⁻¹ * π h = π h * (π g')⁻¹ := (hcommd.symm.inv_left).eq
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      rw [QuotientGroup.mk'_apply] at hmemΓ
      have hmem : h⁻¹ * (g'⁻¹ * h * g') ∈ B.subgroupOf H := by
        rw [← QuotientGroup.eq_one_iff]
        exact hmemΓ
      simpa [g'] using Subgroup.mem_subgroupOf.mp hmem
    have hD₃p : IsPGroup 3 D₃ := IsPGroup.of_card (n := 1) (by rw [hD₃3]; norm_num)
    have hcop : Nat.Coprime (Nat.card B) 3 :=
      Nat.coprime_comm.2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3B)
    obtain ⟨c, hc', m, hm, hcm⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S10.mem_centralizer_mul_of_coprime
        (p := 3) (D := D₃) (H := H) (M := B) hD₃p hcop hBH hBnor
        (hD₃H.trans Subgroup.le_normalizer) (hD₃H.trans hc.1.2) h.2 hfixB
    have hcH : (c : G) ∈ H := hc'.1
    have hcM : (c : G) ∈ D.M := hCD hc'.2
    have hmB : (m : G) ∈ B := hm
    have hπm : π ⟨(m : G), hBH hmB⟩ = 1 := by
      change QuotientGroup.mk' (B.subgroupOf H) ⟨(m : G), hBH hmB⟩ = 1
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (⟨(m : G), hBH hmB⟩ : ↥H)).mpr hmB
    have hsub : (⟨(h : G), h.2⟩ : ↥H) =
        ⟨(c : G), hcH⟩ * ⟨(m : G), hBH hmB⟩ := by
      apply Subtype.ext
      exact hcm
    have hπeq : π ⟨(h : G), h.2⟩ = π ⟨(c : G), hcH⟩ := by
      rw [hsub, map_mul, hπm, mul_one]
    refine Subgroup.mem_map.mpr
      ⟨⟨(c : G), hcH⟩, Subgroup.mem_subgroupOf.mpr ⟨hcH, hcM⟩, hπeq.symm⟩
  have hSylSub : CFSG.ABGLocalTools.IsSylowOf 2 (S₀.subgroupOf H) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · exact IsPGroup.of_injective hS₀.isPGroup
        (Subgroup.subgroupOfEquivOfLe hS₀.le).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hS₀.le).injective
    · rw [Subgroup.relIndex_top_right]
      simpa [Subgroup.relIndex] using (CFSG.ABGLocalTools.isSylowOf_iff.1 hS₀).2.2
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
    have h := CFSG.Quasithin.H13.NQBlock.isSylowOf_map' (p := 2) hSylSub π
    rwa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at h
  have hTW : T ≤ W := by
    apply Subgroup.map_mono
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact ⟨hS₀.le hz, hS₀M hz⟩
  have hKW : Kbar ≤ W := by
    rw [← hSfacSup]
    refine iSup_le fun i => ?_
    obtain ⟨f, hf⟩ := hSz i
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.F09.le_of_isComponent_of_fixedSubgroupOf_le
      σ hσ3 hfix hT hTW (hSfacComp i) (hSfacZ i) hf
  refine le_antisymm ?_ (sup_le inf_le_left hBA)
  intro a ha
  have haH : a ∈ H := hAH ha
  have hπa : π ⟨a, haH⟩ ∈ Kbar :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)
  obtain ⟨mH, hmW, hπm⟩ := Subgroup.mem_map.1 (hKW hπa)
  have hmHM : (mH : G) ∈ H ⊓ D.M := Subgroup.mem_subgroupOf.mp hmW
  have hmM : (mH : G) ∈ D.M := hmHM.2
  have hdiff : (mH : G)⁻¹ * a ∈ B := by
    have hmem : mH⁻¹ * (⟨a, haH⟩ : ↥H) ∈ B.subgroupOf H := by
      have h1 : π (mH⁻¹ * (⟨a, haH⟩ : ↥H)) = 1 := by
        rw [map_mul, map_inv, hπm]
        exact inv_mul_cancel _
      rw [QuotientGroup.mk'_apply] at h1
      rw [← QuotientGroup.eq_one_iff]
      exact h1
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hmA : (mH : G) ∈ A := by
    have h1 : a⁻¹ * (mH : G) ∈ A := hBA (by simpa using B.inv_mem hdiff)
    have heq : (mH : G) = a * (a⁻¹ * (mH : G)) := by group
    rw [heq]
    exact A.mul_mem ha h1
  have hmemSup1 : (mH : G) ∈ (A ⊓ D.M) ⊔ B :=
    (le_sup_left : A ⊓ D.M ≤ (A ⊓ D.M) ⊔ B) ⟨hmA, hmM⟩
  have hmemSup2 : (mH : G)⁻¹ * a ∈ (A ⊓ D.M) ⊔ B :=
    (le_sup_right : B ≤ (A ⊓ D.M) ⊔ B) hdiff
  have hprod : (mH : G) * ((mH : G)⁻¹ * a) ∈ (A ⊓ D.M) ⊔ B :=
    ((A ⊓ D.M) ⊔ B).mul_mem hmemSup1 hmemSup2
  have hmul : (mH : G) * ((mH : G)⁻¹ * a) = a := by group
  rwa [hmul] at hprod

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
