module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubConjClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c6_ker_le_center {Q B : Type} [Group Q] [Group B] [Nontrivial B]
    (hQ : CFSG.Open.IsQuasisimple Q) (f : Q →* B) (hf : Function.Surjective f)
    (hZB : Subgroup.center B = ⊥) : f.ker ≤ Subgroup.center Q := by
  haveI hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  have hZle : Subgroup.center Q ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzB : f z ∈ Subgroup.center B :=
      Subgroup.map_center_le_center hf (Subgroup.mem_map_of_mem f hz)
    rwa [hZB, Subgroup.mem_bot] at hzB
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (f.ker.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · intro x hx
    have hx' : QuotientGroup.mk' (Subgroup.center Q) x ∈
        f.ker.map (QuotientGroup.mk' (Subgroup.center Q)) := Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).1 hx'
  · exfalso
    have htop : f.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx' : QuotientGroup.mk' (Subgroup.center Q) x ∈
          f.ker.map (QuotientGroup.mk' (Subgroup.center Q)) := by rw [h]; trivial
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
      have hxy : x * y⁻¹ ∈ Subgroup.center Q := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        change (QuotientGroup.mk' (Subgroup.center Q)) x *
          ((QuotientGroup.mk' (Subgroup.center Q)) y)⁻¹ = 1
        rw [← hyx, mul_inv_cancel]
      have hxeq : x = (x * y⁻¹) * y := by group
      rw [hxeq]
      exact f.ker.mul_mem (hZle hxy) hy
    haveI : Subsingleton B := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hf a
      obtain ⟨y, rfl⟩ := hf b
      have hx1 : f x = 1 := by rw [← MonoidHom.mem_ker, htop]; trivial
      have hy1 : f y = 1 := by rw [← MonoidHom.mem_ker, htop]; trivial
      rw [hx1, hy1]⟩
    exact not_subsingleton B inferInstance

private theorem s16c6_lBar_quasisimple (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hΩ : IsOmegaMinus ↥(lBar V₀ V hV L) 6 3) :
    CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L) ∧
      Subgroup.center ↥(lBar V₀ V hV L) = ⊥ ∧ Nontrivial ↥(lBar V₀ V hV L) := by
  have hΩ' := hΩ
  obtain ⟨-, K, instK, instFin, b, c, hcard, hirr, ⟨e⟩⟩ := hΩ
  letI : Field K := instK
  letI : Finite K := instFin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 3) (by rw [Fintype.card_eq_nat_card, hcard])
  have hfacts :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (K := K) (n := 3) (Or.inr rfl) hirr
  haveI : Group.IsPerfect (StatedOmega (StatedQuadMinus 3 K b c)) :=
    Group.isPerfect_def.mpr hfacts.2.1
  haveI : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadMinus 3 K b c))) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hperf : Group.IsPerfect ↥(lBar V₀ V hV L) :=
    Group.isPerfect_def.mpr
      (CFSG.ComponentClassification.RankTwoClassical.commutator_eq_top_of_mulEquiv e
        Group.IsPerfect.commutator_eq_top)
  haveI : Group.IsPerfect ↥(lBar V₀ V hV L) := hperf
  have hU4 : IsU4 ↥(lBar V₀ V hV L) 3 := S18.isU4_of_isOmegaMinus hΩ'
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4
  haveI : IsSimpleGroup ↥(lBar V₀ V hV L) := hsimple
  haveI : Nontrivial ↥(lBar V₀ V hV L) := hsimple.toNontrivial
  have hna : ¬ ∀ x y : ↥(lBar V₀ V hV L), x * y = y * x := fun h =>
    (Group.IsPerfect.not_isMulCommutative ↥(lBar V₀ V hV L)) (IsMulCommutative.of_comm h)
  have hq := CFSG.ComponentClassification.RankTwoClassical.isQuasisimple_of_isSimpleGroup hna
  exact ⟨(CFSG.Quasithin.A3.isQuasisimple_iff_open).1 hq.1, hq.2, inferInstance⟩

private theorem s16c6_griessHopfMultiplier_subsingleton
    {X : Type} [Group X] (h : IsU4 X 3) : Subsingleton (CFSG.Open.griessHopfMultiplier X) := by
  have hmodel : CFSG.Open.StatedClassicalModel X .PSU 4 2 3 :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .PSU) (by decide)).1 h
  have hrow := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_row hmodel (by decide)
    (Or.inl (by norm_num))
  obtain ⟨-, ⟨eG⟩⟩ := hrow
  have hcard : Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 4 2 3 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 4 2 3) = 1 := by
    rw [CFSG.RankThree.PartOne.card_generic_exceptional]
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 4 2 3 = (1, 1) := by decide
    have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 3 = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      norm_num
    rw [hgen, hexc]
    norm_num
  haveI : Subsingleton (CFSG.Blueprint.Multiplier.generic .PSU 4 2 3 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 4 2 3) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  exact eG.injective.subsingleton

private theorem s16c6_bar2_simple
    (D : Data G) {V₀ V L K : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hΩ : IsOmegaMinus ↥(lBar V₀ V hV L) 6 3)
    (hKc : K ∈ calC D.M) (hbarK : barSub V₀ V hV K = lBar V₀ V hV L) :
    Subgroup.center (Bar2 K) = ⊥ := by
  obtain ⟨hLbarQ, hZLbar, hNtriv⟩ := s16c6_lBar_quasisimple D hΩ
  haveI : Group.IsPerfect (Bar2 K) := ⟨hKc.2.2.1⟩
  haveI : Nontrivial ↥(barSub V₀ V hV K) := by rw [hbarK]; exact hNtriv
  have hZLbar' : Subgroup.center ↥(barSub V₀ V hV K) = ⊥ := by rw [hbarK]; exact hZLbar
  let ψ := barSubBar2HomOfHyp125 hS.setting.hyp151.hyp125 hKc
  have hψ : Function.Surjective ψ :=
    barSubBar2HomOfHyp125_surjective hS.setting.hyp151.hyp125 hKc
  let eB : ↥(barSub V₀ V hV K) ≃* ↥(lBar V₀ V hV L) := MulEquiv.subgroupCongr hbarK
  let φ : Bar2 K →* ↥(lBar V₀ V hV L) := eB.toMonoidHom.comp ψ
  have hφ : Function.Surjective φ := eB.surjective.comp hψ
  have hkerψ : ψ.ker ≤ Subgroup.center (Bar2 K) := s16c6_ker_le_center hKc.2.2 ψ hψ hZLbar'
  have hker_eq : φ.ker = ψ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact eB.map_eq_one_iff
  have hker : φ.ker ≤ Subgroup.center (Bar2 K) := by
    rw [hker_eq]
    exact hkerψ
  have hZle : Subgroup.center (Bar2 K) ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzB : φ z ∈ Subgroup.center ↥(lBar V₀ V hV L) :=
      Subgroup.map_center_le_center hφ (Subgroup.mem_map_of_mem φ hz)
    rwa [hZLbar, Subgroup.mem_bot] at hzB
  have hcenter : Subgroup.center (Bar2 K) = φ.ker := le_antisymm hZle hker
  have hdiv : Nat.card (Subgroup.center (Bar2 K)) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) := by
    have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective φ hφ hker
    have h1 : Nat.card φ.ker ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        ↥(lBar V₀ V hV L)) := Subgroup.card_dvd_of_surjective hsurj
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      ↥(lBar V₀ V hV L)).toEquiv] at h1
    simpa [hcenter] using h1
  have htriv : Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr
      ⟨s16c6_griessHopfMultiplier_subsingleton (S18.isU4_of_isOmegaMinus hΩ), ⟨1⟩⟩
  rw [htriv, Nat.dvd_one] at hdiv
  exact Subgroup.card_eq_one.1 hdiv

private theorem s16c6_mBar_le_normalizer (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (h : s15 D.M V₀ V hV L = 1) :
    Mbar D.M V₀ V hV ≤ normalizer
      ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) : Set _) := fun φ hφ =>
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr (lBar_conj_eq_of_s15_eq_one h hφ)

theorem s16c6_exists_cover
    (D : Data G) (hstd : S168e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case163_6 D V₀ V hV L) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧ D.M ≤ normalizer (K : Set G) ∧
      barSub V₀ V hV K = lBar V₀ V hV L ∧ IsSimpleGroup (Bar2 K) := by
  have hLbar_le : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hS.setting.hyp151.le
  have hLbarN : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLbar_le).mpr
      (s16c6_mBar_le_normalizer D hc.2.2.1)
  have hB : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV) :=
    ⟨hLbar_le, CFSG.Quasithin.A3.subnormal_of_normal hLbar_le hLbarN,
      (s16c6_lBar_quasisimple D hc.1).1⟩
  obtain ⟨K, hKc, hbarK⟩ :=
    s16h_exists_cover D hstd.h127 hstd.h119 hS.setting.hyp151.hyp125 hB
  have hZ : Subgroup.center (Bar2 K) = ⊥ := s16c6_bar2_simple D hS hc.1 hKc hbarK
  haveI : IsSimpleGroup (Bar2 K) := by
    haveI : IsSimpleGroup (Bar2 K ⧸ Subgroup.center (Bar2 K)) := hKc.2.2.2
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hbarN : barSub V₀ V hV (UC22.conjClosure D.M K) = lBar V₀ V hV L := by
    rw [barSub_conjClosure_eq_iSup_of_hyp125 hS.setting.hyp151.hyp125 hKc.1.le, hbarK]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun φ => le_of_eq ?_
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (s16c6_mBar_le_normalizer D hc.2.2.1 φ.2)
    · have h1 : (lBar V₀ V hV L).map
          (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom = lBar V₀ V hV L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (s16c6_mBar_le_normalizer D hc.2.2.1 (Mbar D.M V₀ V hV).one_mem)
      calc lBar V₀ V hV L = (lBar V₀ V hV L).map
            (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom := h1.symm
        _ ≤ ⨆ φ : Mbar D.M V₀ V hV, (lBar V₀ V hV L).map
            (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom :=
          le_iSup (fun φ : Mbar D.M V₀ V hV =>
            (lBar V₀ V hV L).map
              (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom) 1
  have hs : IsSimpleGroup ↥(barSub V₀ V hV (UC22.conjClosure D.M K)) := by
    rw [hbarN]
    exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide)
      (S18.isU4_of_isOmegaMinus hc.1)
  have hKconj : UC22.conjClosure D.M K = K :=
    conjClosure_eq_self_of_isSimpleGroup_barSub hS.setting.hyp151.hyp125 hKc hs
  exact ⟨K, hKc, by simpa [hKconj] using TwelveTwentyThree.le_normalizer_conjClosure D.M K,
    hbarK, inferInstance⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
