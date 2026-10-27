module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourBlocks
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Cond
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeKer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Kernel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Sylow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ATwoConj
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.Quasithin.Background.C1GNA7
import CFSG.Quasithin.Background.FFC8A
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAAux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.Quasithin.Background.G10Local
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
import CFSG.RankThree.PartTwo.Sec15.Item158Res2ProofInner
import CFSG.RankThree.PartTwo.Sec17.Item175Proof
import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s168e3_uniqueMax_wSub_three
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2)
    {w : G} (hw : w ∈ wSub V₀ V hV L) (hw1 : w ≠ 1) (h3 : 3 ∈ D.sig) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  have hs' : Set.ncard {X : Subgroup (MulAut W) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = H.map (MulAut.conj φ).toMonoidHom} = 2 := by
    simpa [s15, H, lBar] using hs
  obtain ⟨ψ, hψMbar, hψne⟩ :=
    (c23a_two_conj (Mb := Mbar D.M V₀ V hV) (L := H) hs').1
  have hψinvMbar : ψ⁻¹ ∈ Mbar D.M V₀ V hV := (Mbar D.M V₀ V hV).inv_mem hψMbar
  obtain ⟨q, hqM, hqact⟩ := (mem_barSub V₀ V hV D.M ψ⁻¹).1 hψinvMbar
  let H₂ : Subgroup (MulAut W) := H.map (MulAut.conj ψ).toMonoidHom
  have hH₂bar : H₂ = barSub V₀ V hV (conjSubgroup L (q : G)) := by
    change H.map (MulAut.conj ψ).toMonoidHom = _
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV q.2 L, hqact]
    simp
    rfl
  have hHMbar : H ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV c.setting.hyp151.le
  have hH₂Mbar : H₂ ≤ Mbar D.M V₀ V hV := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    exact (Mbar D.M V₀ V hV).mul_mem
      ((Mbar D.M V₀ V hV).mul_mem hψMbar (hHMbar hh))
      ((Mbar D.M V₀ V hV).inv_mem hψMbar)
  have hqn : (q : G) ∉ nBar D.M V₀ V hV L := by
    intro hmem
    have hbar_eq : barSub V₀ V hV (conjSubgroup L (q : G)) = H := by
      simpa [H, lBar] using (s15_Infra_mem_nBar_iff c.setting.hyp151.hyp125 hV hqM).1 hmem
    have hH₂eqH : H₂ = H := by rw [hH₂bar, hbar_eq]
    exact hψne (by simpa [H₂] using hH₂eqH)
  have hcomm := c.setting.hyp151.commute (q : G) hqM hqn
  rw [← hH₂bar] at hcomm
  have hcent : H₂ ≤ centSub (wTil V₀ V hV L) := by
    intro x hx u hu
    exact (mem_fixV.mp ((commSub_eq_bot_iff.mp hcomm.2) hu)) x hx
  let P₂ := preBarSub D.M V₀ V hV H₂
  let X₂ := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf P₂
  have hP₂bar : barSub V₀ V hV P₂ = H₂ := by
    rw [barSub_preBarSub, inf_eq_left.mpr hH₂Mbar]
  have hP₂M : P₂ ≤ D.M := fun x hx => ((mem_preBarSub D.M V₀ V hV H₂).1 hx).1
  have hP₂stab : P₂ ≤ stabTil V₀ V := fun x hx =>
    ((mem_preBarSub D.M V₀ V hV H₂).1 hx).2.choose
  have hX₂P : X₂ ≤ P₂ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hX₂N : X₂ ≤ normalizer (V₀ : Set G) :=
    hX₂P.trans (hP₂stab.trans (stabTil_le_normalizer₀ V₀ V))
  have hX₂perf : ⁅X₂, X₂⁆ = X₂ :=
    Subgroup.isPerfect_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect P₂)
  have hV₀comm : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := by
    haveI : IsMulCommutative ↥V₀ := c.setting.hyp16.hyp125.pairFacts.elemAbelian₀.1
    intro a ha b hb
    have h := mul_comm' (⟨a, ha⟩ : V₀) ⟨b, hb⟩
    simpa using congrArg Subtype.val h
  have hX₂V0 : X₂ ≤ centralizer (V₀ : Set G) :=
    c23ne_centralizes_V₀ hX₂perf c.setting.hyp16.hyp125.pairFacts.elemAbelian₀
      c.setting.hyp16.small hX₂N
  have hX₂W : X₂ ≤ centralizer (wSub V₀ V hV L : Set G) := by
    refine ElevenNine.le_centralizer_of_perfect_of_sub hX₂perf hV₀comm hX₂V0 ?_
    intro l hl v hv
    exact (s16h_preBarSub_le_cElt_of_le_centSub hV hcent hv (hX₂P hl)).2.2
  obtain ⟨α, hrealA7⟩ := hrow
  obtain ⟨πA7, hπA7⟩ := hrealA7
  have eA7H : ↥(alternatingGroup (Fin 7)) ≃* ↥H :=
    FFC.equivOfRealizes (FFC.a7Four_faithful α) hπA7
  have eMap : ↥H ≃* ↥H₂ :=
    Subgroup.equivMapOfInjective H (MulAut.conj ψ).toMonoidHom (MulAut.conj ψ).injective
  have eH₂A7 : ↥H₂ ≃* ↥(alternatingGroup (Fin 7)) := eMap.symm.trans eA7H.symm
  let φP : ↥P₂ →* MulAut W :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hP₂stab)
  have hφrange : φP.range = H₂ := by
    change ((actTil V₀ V hV).comp (Subgroup.inclusion hP₂stab)).range = H₂
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hP₂bar
  let φH : ↥P₂ →* ↥H₂ :=
    φP.codRestrict H₂ fun x => hφrange ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hφHsurj : Function.Surjective φH := by
    intro y
    have hy : (y : MulAut W) ∈ φP.range := by
      rw [hφrange]
      exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  let φA7 : ↥P₂ →* ↥(alternatingGroup (Fin 7)) := eH₂A7.toMonoidHom.comp φH
  have hφA7surj : Function.Surjective φA7 := eH₂A7.surjective.comp hφHsurj
  haveI : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by norm_num))
  have hresSurj :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image
      φA7 hφA7surj
  let φX : ↥X₂ →* ↥(alternatingGroup (Fin 7)) :=
    φA7.comp (Subgroup.inclusion hX₂P)
  have hφXsurj : Function.Surjective φX := by
    intro y
    have hy : y ∈ Subgroup.map φA7
        (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥P₂) := by
      rw [hresSurj]
      exact Subgroup.mem_top y
    obtain ⟨x, hxperf, hxy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨(x : G), Subgroup.mem_map.mpr ⟨x, hxperf, rfl⟩⟩, ?_⟩
    change φA7 (Subgroup.inclusion hX₂P ⟨(x : G),
      Subgroup.mem_map.mpr ⟨x, hxperf, rfl⟩⟩) = y
    rw [show (Subgroup.inclusion hX₂P ⟨(x : G),
        Subgroup.mem_map.mpr ⟨x, hxperf, rfl⟩⟩ : ↥P₂) = x from Subtype.ext rfl]
    exact hxy
  have h2rank : 2 ≤ CFSG.Open.pRank 3 X₂ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p2214_two_le_pRank_of_surj φX hφXsurj
      Nat.prime_three (by norm_num) CFSG.Quasithin.C1GN.two_le_pRank_alt7
  have h2rank' : 2 ≤ CFSG.pRank 3 X₂ := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.groupPRank_eq_pRank]
    exact h2rank
  obtain ⟨E, hEX₂, hEab, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := 3) (M := X₂) (k := 2) Nat.prime_three h2rank'
  have hEnc : ¬ IsCyclic ↥E :=
    s16c7_not_isCyclic_of_elemAbelian Nat.prime_three hEab (by rw [hEcard])
  have hEle : E ≤ D.M ⊓ centralizer ({w} : Set G) := by
    intro x hx
    have hxM : x ∈ D.M := (hEX₂.trans (hX₂P.trans hP₂M)) hx
    have hxW : x ∈ centralizer (wSub V₀ V hV L : Set G) := (hEX₂.trans hX₂W) hx
    have hxw : x ∈ centralizer ({w} : Set G) :=
      (Subgroup.centralizer_le (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact hw)) hxW
    exact ⟨hxM, hxw⟩
  exact s16c34_uniqueMax_of_noncyclic D c.std.h61 h3 hEab.isPGroup hEnc hEle inf_le_left

theorem s168e3_uniqueMax_wSub_of_a7Four
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2) :
    ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  intro w hw hw1
  by_cases h3 : 3 ∈ D.sig
  · exact s168e3_uniqueMax_wSub_three c hrow hs hw hw1 h3
  · have hs2 : s15 D.M V₀ V hV L ≤ 2 := by omega
    obtain ⟨q, hq⟩ := c.std.hx.sig_nonempty
    have hqprime := (D.sig_prime q hq).1
    have hqodd := (D.sig_prime q hq).2
    have hq3 : q ≠ 3 := fun heq => h3 (heq ▸ hq)
    have hq5 : 5 ≤ q := by
      have h2 := hqprime.two_le
      by_contra h
      have hlt : q < 5 := by omega
      interval_cases q
      · exact absurd rfl hqodd
      · exact absurd rfl hq3
      · norm_num at hqprime
    have hBB := s16h_blockBound_one_of_a7Four_of_five_le_p c hrow hqprime hq5
    have h3rank : 3 ≤ CFSG.Open.pRank q D.M := by
      rw [c.std.pRank_eq_three hq]
    exact s16h_uniqueMax_of_blockBound_one_two D c.std.h61 c.std.h127 c.setting hs2 hq
      h3rank hBB w hw hw1

theorem s168e3_hyp154_of_a7Four_of_s15_eq_two
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2) :
    Hyp154 D V₀ V L := by
  have hdata := s168e3_a7Four_spaceData c hrow
  have hW := s168e3_uniqueMax_wSub_of_a7Four c hrow hs
  have h1 : ∀ w ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) :=
    s16h_unique₁_of_wSub D c.setting.hyp151 (le_of_eq hdata.v1Sub_eq) hW
  refine s16h_hyp154_of_unique₁_two D c.setting.hyp151 hs h1 ?_
  have hγ : gamma15 D.M V₀ V c.setting.hyp151.isElemAbelian L = 4 := hdata.gamma15_eq
  have hδle : delta15 D.M V₀ V c.setting.hyp151.isElemAbelian L ≤ 2 := hdata.delta15_le
  rw [hγ]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
