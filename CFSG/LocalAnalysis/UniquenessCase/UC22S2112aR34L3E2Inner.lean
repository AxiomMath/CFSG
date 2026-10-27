module

import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34FixOdd
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddLinear
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddUnitary
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddSubfield
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem fieldAutOdd_psl_of_ne_two {X : Type} [Group X] [Finite X] {n p f r : ℕ}
    (hp : p.Prime) (hadm : StatedLieAdmissible .PSL n p f) (hX : LieModel X .PSL n p f)
    (hA1 : ¬ (StatedLieTag.PSL = .PSL ∧ n = 2)) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrg : ¬ r ∣ (genericOrders .PSL n p f).1)
    (θ : MulAut X) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧ IsSimpleGroup Y ∧
      2 ≤ CFSG.pRank p Y := by
  open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
    CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
    CFSG.RankThree.PartOne in
  have hn : 3 ≤ n := by
    have hn2 := hadm.2.2.1
    have hnne : n ≠ 2 := fun h => hA1 ⟨rfl, h⟩
    omega
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have hθ' : orderOf (MulAut.congr e θ) = r := by
    exact (orderOf_injective (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, ?_⟩
    ext g
    have h := congrArg (fun α : MulAut (projectiveSL n K) => e.symm (α (e g))) hx
    simpa [MulAut.congr_apply, MulAut.conj_apply] using h
  have hcop : ¬ r ∣ Nat.gcd n (Nat.card K - 1) := by
    rw [hK]
    exact hrg
  obtain ⟨hrf, Y, hY, hs, hrank⟩ :=
    fieldAutOdd_projectiveSL hp hadm.2.1 hK hn hr hr2 hcop
      (MulAut.congr e θ) hθ' hout'
  have : IsSimpleGroup Y := hs
  let ι : Y →* X := e.symm.toMonoidHom.comp Y.subtype
  have hι : Function.Injective ι := e.symm.injective.comp Y.subtype_injective
  have hfix : ∀ y, θ (ι y) = ι y := by
    intro y
    apply e.injective
    have hy : (MulAut.congr e θ) y = y := hY y.2
    simpa [ι, MulAut.congr_apply] using hy
  exact ⟨hrf, CFSG.exists_simple_subgroup_le_fixed_of_injective ι hι θ hfix hrank⟩

theorem fieldAutOdd_psu_of_ne_two {X : Type} [Group X] [Finite X] {n p f r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : LieModel X .PSU n p f)
    (hr : r.Prime) (hr2 : r ≠ 2)
    (hrg : ¬ r ∣ (genericOrders .PSU n p f).1)
    (θ : MulAut X) (hθ : orderOf θ = r) (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧ IsSimpleGroup Y ∧
      2 ≤ CFSG.pRank p Y := by
  classical
  open Matrix CFSG.Open CFSG.Blueprint
    CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
    CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.Classical in
  open CFSG.RankThree.PartOne.KCUnitaryModel (idGram) in
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨eX⟩⟩ := hX.statedClassicalModel (by decide)
  let h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let eP : primeFormP h (idGram K n) ≃* StatedProj (StatedSU n (p ^ f) K) :=
    (Classical.choice (nonempty_primeFormP_mulEquiv h isPrimeFormGram_one)).trans
      (unitaryPSUEquiv h (by omega))
  let e := eX.trans eP.symm
  have hθ' : orderOf (MulAut.congr e θ) = r :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, ?_⟩
    ext g
    have hh := congrArg (fun α : MulAut (primeFormP h (idGram K n)) => e.symm (α (e g))) hx
    simpa [MulAut.congr_apply, MulAut.conj_apply] using hh
  obtain ⟨hrf, Y, hY, hmodel⟩ := fieldAutOdd_primeForm_subfield h hp2 hn hr hr2 hrg
    (MulAut.congr e θ) hθ' hout'
  let Y' : Subgroup X := Y.map e.symm.toMonoidHom
  have hY' : Y' ≤ signalizerFixedSubgroup θ := by
    rintro _ ⟨y, hy, rfl⟩
    change θ (e.symm y) = e.symm y
    apply e.injective
    have hh : (MulAut.congr e θ) y = y := hY hy
    simpa [MulAut.congr_apply] using hh
  have hmodel' : LieModel Y' .PSU n p (f / r) :=
    hmodel.of_mulEquiv (Y.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)
  obtain ⟨S, hS, hSs, hSr⟩ :=
    fieldAutOdd_of_classical_subfield (by decide) hp2 (fun h => by cases h.1) θ hY' hmodel'
  exact ⟨hrf, S, hS, hSs, hSr⟩

theorem uc22s2112r34_inner_of_ne_two {D : Data G} {Ch : Choice2011 G} (hKF7 : KF7Use D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {t : StatedLieTag}
    {n p f : ℕ} (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel (BarInf L) t n p f)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hpσ : p ∈ D.sig) (hMs : IsStronglyPEmbedded p D.M)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) {b : G} (hbB : b ∈ c.B0)
    (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r)
    (hrg : ¬ r ∣ (genericOrders t n p f).1) :
    inducedBarInfAutHom L ⟨b, hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
  classical
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  by_cases hθ1 : inducedBarInfAutHom L ⟨b, hb⟩ = 1
  · exact ⟨1, by rw [hθ1, map_one]⟩
  by_contra hθ
  have hord : orderOf (inducedBarInfAutHom L ⟨b, hb⟩) = r := by
    have hd := orderOf_map_dvd (inducedBarInfAutHom L) ⟨b, hb⟩
    rw [Subgroup.orderOf_mk, hbr] at hd
    rcases (Nat.dvd_prime hr).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hθ1
    · exact h1
  have hfield : r ∣ f ∧ ∃ Y : Subgroup (BarInf L),
      Y ≤ signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩) ∧
      IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
    rcases ht with rfl | rfl
    · exact fieldAutOdd_psl_of_ne_two hp hadm hX hA1 hr hr2 hrg _ hord hθ
    · exact fieldAutOdd_psu_of_ne_two hp hp2 hX hr hr2 hrg _ hord hθ
  obtain ⟨-, Y, hY, hYs, hYp⟩ := hfield
  have hYp' : 2 ≤ Open.pRank p Y := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hYp
  obtain ⟨E, hEY, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hYp'
  have hp2Y : p ^ 2 ∣ Nat.card ↥Y := hEc ▸ Subgroup.card_dvd_of_le hEY
  have hpY : p ∣ Nat.card ↥Y := (dvd_pow_self p two_ne_zero).trans hp2Y
  have hrank : 2 ≤ Open.pRank p (signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)) :=
    UC6S846.le_pRank' hp (hEY.trans hY) hEel hEc
  have := hYs
  refine uc22s2112r34_false_of_fixed_odd hKF7 hH c hL hpσ hMs hbB hb (hbr ▸ hr) (hbr ▸ hr2)
    hpN hrank hY ?_ (MonoidHom.id ↥Y) Function.surjective_id hpY ?_
  ·
    intro hsolv
    have : IsMulCommutative ↥Y := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.2 hsolv⟩⟩
    have hprime := Group.is_simple_iff_prime_card.1 hYs
    rw [← (Nat.prime_dvd_prime_iff_eq hp hprime).1 hpY] at hp2Y
    have h2 := hp.two_le
    have hle := Nat.le_of_dvd hp.pos hp2Y
    nlinarith
  ·
    rintro rfl ⟨e⟩
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [Nat.card_congr e.toEquiv, h60] at hp2Y
    norm_num at hp2Y

end CFSG.LocalAnalysis.UniquenessCase.UC22
