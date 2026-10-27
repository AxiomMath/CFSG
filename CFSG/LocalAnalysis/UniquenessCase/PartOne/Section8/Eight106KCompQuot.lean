module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106KCompBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
public import CFSG.Foundations.KCoreOpen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8106K

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {Y : Type} [Group Y] [Finite Y]

private lemma mul_inv_mem_center_of_quotient_eq {a b : Y}
    (h : QuotientGroup.mk' (center Y) a = QuotientGroup.mk' (center Y) b) :
    a * b⁻¹ ∈ center Y := by
  have h1 : QuotientGroup.mk' (center Y) (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hmem : a * b⁻¹ ∈ MonoidHom.ker (QuotientGroup.mk' (center Y)) :=
    MonoidHom.mem_ker.mpr h1
  rwa [QuotientGroup.ker_mk'] at hmem

private lemma injective_quotient_on_of_inf_center_eq_bot {K : Subgroup Y}
    (hKZ : K ⊓ center Y = ⊥) :
    Function.Injective ((QuotientGroup.mk' (center Y)).comp K.subtype) := by
  intro a b hab
  have hmem : (a : Y) * (b : Y)⁻¹ ∈ K ⊓ center Y := by
    refine ⟨K.mul_mem a.2 (K.inv_mem b.2), ?_⟩
    have hab' : QuotientGroup.mk' (center Y) (a : Y) =
        QuotientGroup.mk' (center Y) (b : Y) := hab
    exact mul_inv_mem_center_of_quotient_eq hab'
  rw [hKZ, Subgroup.mem_bot] at hmem
  exact Subtype.ext (by simpa using congrArg (fun t => t * (b : Y)) hmem)

private lemma quotient_card_map_of_le {K D : Subgroup Y} (hKZ : K ⊓ center Y = ⊥)
    (hDK : D ≤ K) : Nat.card (D.map (QuotientGroup.mk' (center Y))) = Nat.card D := by
  have hinjK := injective_quotient_on_of_inf_center_eq_bot hKZ
  have hinj : Function.Injective ((QuotientGroup.mk' (center Y)).comp D.subtype) := by
    intro a b hab
    have h : ((QuotientGroup.mk' (center Y)).comp K.subtype) ⟨(a : Y), hDK a.2⟩ =
        ((QuotientGroup.mk' (center Y)).comp K.subtype) ⟨(b : Y), hDK b.2⟩ := hab
    exact Subtype.ext (congrArg (fun t : ↥K => (t : Y)) (hinjK h))
  have hrange : ((QuotientGroup.mk' (center Y)).comp D.subtype).range =
      D.map (QuotientGroup.mk' (center Y)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eD : ↥D ≃* ↥(D.map (QuotientGroup.mk' (center Y))) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact (Nat.card_congr eD.toEquiv).symm

private lemma mem_centralizer_of_map_mem_centralizer {p : ℕ} {D₀ : Subgroup Y}
    (hp : p.Prime) (hcard : Nat.card D₀ = p) (hpZ : ¬ p ∣ Nat.card (center Y)) {y : Y}
    (hy : QuotientGroup.mk' (center Y) y ∈ Subgroup.centralizer
      ((D₀.map (QuotientGroup.mk' (center Y)) : Subgroup (Y ⧸ center Y)) :
        Set (Y ⧸ center Y))) :
    y ∈ Subgroup.centralizer (D₀ : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hcommπ : QuotientGroup.mk' (center Y) d * QuotientGroup.mk' (center Y) y =
      QuotientGroup.mk' (center Y) y * QuotientGroup.mk' (center Y) d :=
    (Subgroup.mem_centralizer_iff.mp hy) (QuotientGroup.mk' (center Y) d)
      (Subgroup.mem_map_of_mem _ hd)
  have hconj : QuotientGroup.mk' (center Y) (y * d * y⁻¹) =
      QuotientGroup.mk' (center Y) d := by
    calc QuotientGroup.mk' (center Y) (y * d * y⁻¹)
        = QuotientGroup.mk' (center Y) y * QuotientGroup.mk' (center Y) d *
            (QuotientGroup.mk' (center Y) y)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = QuotientGroup.mk' (center Y) d := by rw [hcommπ.symm]; group
  have hzmem : y * d * y⁻¹ * d⁻¹ ∈ center Y := mul_inv_mem_center_of_quotient_eq hconj
  have hdp : d ^ p = 1 := by
    have h := pow_card_eq_one' (G := ↥D₀) (x := (⟨d, hd⟩ : ↥D₀))
    rw [hcard] at h
    simpa using h
  have hconjpow : (y * d * y⁻¹) ^ p = 1 := by
    rw [show y * d * y⁻¹ = (MulAut.conj y) d from (MulAut.conj_apply y d).symm]
    rw [← map_pow, hdp, map_one]
  have hzd : y * d * y⁻¹ = (y * d * y⁻¹ * d⁻¹) * d := by group
  have hcommz : Commute (y * d * y⁻¹ * d⁻¹) d :=
    (Subgroup.mem_center_iff.mp hzmem d).symm
  have hzp : (y * d * y⁻¹ * d⁻¹) ^ p = 1 := by
    have hpow : ((y * d * y⁻¹ * d⁻¹) * d) ^ p =
        (y * d * y⁻¹ * d⁻¹) ^ p * d ^ p := hcommz.mul_pow p
    rw [← hzd, hconjpow, hdp, mul_one] at hpow
    exact hpow.symm
  have hdvd : orderOf (y * d * y⁻¹ * d⁻¹) ∣ p :=
    orderOf_dvd_iff_pow_eq_one.mpr hzp
  have hdvdZ : orderOf (y * d * y⁻¹ * d⁻¹) ∣ Nat.card (center Y) :=
    Subgroup.orderOf_dvd_natCard _ hzmem
  have hz1 : y * d * y⁻¹ * d⁻¹ = 1 := by
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h1 ▸ hdvdZ) hpZ
  have hconj2 : y * d * y⁻¹ = d := by
    have h := congrArg (fun t => t * d) hz1
    simpa [mul_assoc] using h
  have hdy : y * d = d * y := by
    have h := congrArg (fun t => t * y) hconj2
    simpa [mul_assoc] using h
  exact hdy.symm

private lemma mem_normalizer_of_mem_centralizer {p : ℕ} {K D₀ : Subgroup Y}
    (hSE : IsStronglyPEmbedded p (normalizer (K : Set Y)))
    (hD0K : D₀ ≤ K) (hcardD : Nat.card D₀ = p)
    {y : Y} (hyC : y ∈ Subgroup.centralizer (D₀ : Set Y)) :
    y ∈ normalizer (K : Set Y) := by
  by_contra hy
  have hD0H : D₀ ≤ normalizer (K : Set Y) := hD0K.trans Subgroup.le_normalizer
  have hfix : D₀ ≤ (normalizer (K : Set Y)).map (MulAut.conj y).toMonoidHom := by
    intro d hd
    rw [Subgroup.mem_map]
    refine ⟨d, hD0H hd, ?_⟩
    change (MulAut.conj y) d = d
    have hcomm : d * y = y * d := (Subgroup.mem_centralizer_iff.mp hyC) d hd
    rw [MulAut.conj_apply, hcomm.symm]
    group
  have hD0inf : D₀ ≤ normalizer (K : Set Y) ⊓
      (normalizer (K : Set Y)).map (MulAut.conj y).toMonoidHom := le_inf hD0H hfix
  have hdvd : p ∣ Nat.card (normalizer (K : Set Y) ⊓
      (normalizer (K : Set Y)).map (MulAut.conj y).toMonoidHom : Subgroup Y) := by
    have hcardEq : Nat.card ↥(D₀.subgroupOf (normalizer (K : Set Y) ⊓
        (normalizer (K : Set Y)).map (MulAut.conj y).toMonoidHom)) = Nat.card D₀ := by
      have h2 := Subgroup.card_subtype (normalizer (K : Set Y) ⊓
        (normalizer (K : Set Y)).map (MulAut.conj y).toMonoidHom)
        (D₀.subgroupOf (normalizer (K : Set Y) ⊓
          (normalizer (K : Set Y)).map (MulAut.conj y).toMonoidHom))
      rw [Subgroup.map_subgroupOf_eq_of_le hD0inf] at h2
      exact h2.symm
    have hdiv := Subgroup.card_subgroup_dvd_card (D₀.subgroupOf (normalizer (K : Set Y) ⊓
      (normalizer (K : Set Y)).map (MulAut.conj y).toMonoidHom))
    rwa [hcardEq, hcardD] at hdiv
  exact (hSE.2.2 y hy) hdvd

private lemma normalizer_eq_top_of_map_eq_top {K : Subgroup Y}
    (h : K.map (QuotientGroup.mk' (center Y)) = ⊤) :
    normalizer (K : Set Y) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hmemmap : QuotientGroup.mk' (center Y) y ∈
      K.map (QuotientGroup.mk' (center Y)) := by
    rw [h]; exact Subgroup.mem_top _
  obtain ⟨k, hkK, hk⟩ := Subgroup.mem_map.mp hmemmap
  have hmem : y * k⁻¹ ∈ center Y := mul_inv_mem_center_of_quotient_eq hk.symm
  have hz : y * k⁻¹ ∈ normalizer (K : Set Y) := Subgroup.center_le_normalizer (K : Set Y) hmem
  have hk' : k ∈ normalizer (K : Set Y) := Subgroup.le_normalizer hkK
  have hmul : (y * k⁻¹) * k ∈ normalizer (K : Set Y) := mul_mem hz hk'
  have hy : (y * k⁻¹) * k = y := by group
  rwa [hy] at hmul

private lemma pPrimeCore_three_quotient_eq_bot [IsSimpleGroup (Y ⧸ center Y)]
    (h3Ybar : 3 ∣ Nat.card (Y ⧸ center Y)) :
    CFSG.pPrimeCore 3 (Y ⧸ center Y) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases (inferInstance : (CFSG.pPrimeCore 3 (Y ⧸ center Y)).Normal).eq_bot_or_eq_top with
    hbot | htop
  · exact hbot
  · exfalso
    have hcop : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 (Y ⧸ center Y))) :=
      CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3Ybar

private lemma pRank_three_quotient_eq_one
    (hY3 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1)
    (h3Z : ¬ 3 ∣ Nat.card (center Y)) (h3Ybar : 3 ∣ Nat.card (Y ⧸ center Y)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ center Y)) = 1 := by
  let π : Y →* (Y ⧸ center Y) := QuotientGroup.mk' (center Y)
  have hsurj : Function.Surjective ⇑π := QuotientGroup.mk'_surjective (center Y)
  have h1 : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ center Y)) :=
    CFSG.one_le_pRank_of_dvd_card Nat.prime_three (by simpa using h3Ybar)
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ center Y)) ≤ 1 := by
    have hker : ¬ 3 ∣ Nat.card ↥(MonoidHom.ker π) := by
      rwa [QuotientGroup.ker_mk']
    have heq := CFSG.pRank_map_eq_of_not_dvd_card_ker π hsurj Nat.prime_three hker ⊤
    rw [Subgroup.map_top_of_surjective π hsurj] at heq
    rw [heq]
    exact hY3
  omega

private lemma normalClosure_image_eq_top [IsSimpleGroup (Y ⧸ center Y)] {K : Subgroup Y}
    (hKZ : K ⊓ center Y = ⊥) (h3K : 3 ∣ Nat.card K) :
    (⊤ : Subgroup (Y ⧸ center Y)) =
      Subgroup.normalClosure (K.map (QuotientGroup.mk' (center Y)) :
        Set (Y ⧸ center Y)) := by
  have hcard : Nat.card (K.map (QuotientGroup.mk' (center Y))) = Nat.card K :=
    quotient_card_map_of_le hKZ le_rfl
  have hnormal : (Subgroup.normalClosure (K.map (QuotientGroup.mk' (center Y)) :
      Set (Y ⧸ center Y))).Normal := Subgroup.normalClosure_normal
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · exfalso
    have hKbarBot : K.map (QuotientGroup.mk' (center Y)) = ⊥ :=
      le_bot_iff.mp ((Subgroup.le_normalClosure (H := K.map (QuotientGroup.mk' (center Y)))).trans
        (le_of_eq hbot))
    have h3Kbar : 3 ∣ Nat.card (K.map (QuotientGroup.mk' (center Y))) := by
      rw [hcard]; exact h3K
    rw [hKbarBot, Subgroup.card_bot] at h3Kbar
    omega
  · exact htop.symm

private lemma inf_centralizer_le_normalizer {K D₀ : Subgroup Y} {p : ℕ}
    (hSE : IsStronglyPEmbedded p (normalizer (K : Set Y)))
    (hKZ : K ⊓ center Y = ⊥) (hp : p.Prime) (hpZ : ¬ p ∣ Nat.card (center Y))
    (hD0K : D₀ ≤ K) (hcardD : Nat.card D₀ = p) :
    (⊤ : Subgroup (Y ⧸ center Y)) ⊓ Subgroup.centralizer
        ((D₀.map (QuotientGroup.mk' (center Y)) : Subgroup (Y ⧸ center Y)) :
          Set (Y ⧸ center Y)) ≤
      Subgroup.normalizer ((K.map (QuotientGroup.mk' (center Y)) : Subgroup (Y ⧸ center Y)) :
        Set (Y ⧸ center Y)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center Y) x
  have hx2 : QuotientGroup.mk' (center Y) y ∈ Subgroup.centralizer
      ((D₀.map (QuotientGroup.mk' (center Y)) : Subgroup (Y ⧸ center Y)) :
        Set (Y ⧸ center Y)) := (Subgroup.mem_inf.mp hx).2
  have hyC : y ∈ Subgroup.centralizer (D₀ : Set Y) :=
    mem_centralizer_of_map_mem_centralizer hp hcardD hpZ hx2
  have hyH : y ∈ normalizer (K : Set Y) :=
    mem_normalizer_of_mem_centralizer hSE hD0K hcardD hyC
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' (center Y))
    (Subgroup.mem_map_of_mem _ hyH)

private lemma top_ne_image_of_isStronglyPEmbedded {K : Subgroup Y} {p : ℕ}
    (hSE : IsStronglyPEmbedded p (normalizer (K : Set Y))) :
    (⊤ : Subgroup (Y ⧸ center Y)) ≠ K.map (QuotientGroup.mk' (center Y)) := by
  intro htop
  exact hSE.1 (normalizer_eq_top_of_map_eq_top htop.symm)

private lemma nonempty_image_equiv_of_inf_center_eq_bot {K : Subgroup Y}
    (hKZ : K ⊓ center Y = ⊥) :
    ∃ e : ↥K ≃* ↥(K.map (QuotientGroup.mk' (center Y))),
      Nat.card (K.map (QuotientGroup.mk' (center Y))) = Nat.card K := by
  have hinj := injective_quotient_on_of_inf_center_eq_bot hKZ
  have hrange : ((QuotientGroup.mk' (center Y)).comp K.subtype).range =
      K.map (QuotientGroup.mk' (center Y)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥K ≃* ↥(K.map (QuotientGroup.mk' (center Y))) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact ⟨e, (Nat.card_congr e.toEquiv).symm⟩

theorem isU3_quotient_center (hId : KU3Ident) (hYk : CFSG.Open.IsKGroup Y)
    (hYq : CFSG.Open.IsQuasisimple Y) (hZ : Odd (Nat.card (center Y)))
    (hY3 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) {n p : ℕ} (hn : 2 ≤ n) (hne : Even n)
    (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1) {K : Subgroup Y} (hK : ⁅K, K⁆ = K)
    (hL2 : IsL2 (Bar2 K) (2 * n)) (hSE : IsStronglyPEmbedded p (normalizer (K : Set Y))) :
    IsU3 (Y ⧸ center Y) (2 * n) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (Y ⧸ center Y) := hYq.2
  let π : Y →* (Y ⧸ center Y) := QuotientGroup.mk' (center Y)
  let Kbar : Subgroup (Y ⧸ center Y) := K.map π
  have hKZ : K ⊓ center Y = ⊥ := inf_center_eq_bot_of_isL2 hL2 hZ
  have h3K : 3 ∣ Nat.card K := three_dvd_card_of_isL2_bar2 hL2
  have h3Z : ¬ 3 ∣ Nat.card (center Y) := not_three_dvd_card_center hKZ h3K hY3
  have hpZ : ¬ p ∣ Nat.card (center Y) :=
    not_dvd_card_center_of_isStronglyPEmbedded hSE (Subgroup.center_le_normalizer (K : Set Y))
  obtain ⟨e, hcardKbar⟩ := nonempty_image_equiv_of_inf_center_eq_bot hKZ
  have hKbar : ⁅Kbar, Kbar⁆ = Kbar := by
    rw [show Kbar = K.map π from rfl, ← Subgroup.map_commutator K K π, hK]
  have hL2bar : IsL2 (Bar2 Kbar) (2 * n) :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.nonempty_bar2_equiv_of_mulEquiv
        e).some hL2
  obtain ⟨D₀, hD0K, hcardD⟩ := exists_card_eq_of_isL2 hp hpn hL2
  let Dbar : Subgroup (Y ⧸ center Y) := D₀.map π
  have hDbar_le : Dbar ≤ Kbar := Subgroup.map_mono hD0K
  have hDcard : Nat.card Dbar = p := by
    have h := quotient_card_map_of_le hKZ hD0K
    rw [hcardD] at h
    exact h
  have h3Ybar : 3 ∣ Nat.card (Y ⧸ center Y) := by
    have h3Kbar : 3 ∣ Nat.card Kbar := by rw [hcardKbar]; exact h3K
    exact h3Kbar.trans (Subgroup.card_subgroup_dvd_card Kbar)
  have hcore : CFSG.pPrimeCore 3 (Y ⧸ center Y) = ⊥ :=
    pPrimeCore_three_quotient_eq_bot h3Ybar
  have h6 : CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ center Y)) = 1 :=
    pRank_three_quotient_eq_one hY3 h3Z h3Ybar
  have h7 : (⊤ : Subgroup (Y ⧸ center Y)) =
      Subgroup.normalClosure (Kbar : Set (Y ⧸ center Y)) :=
    normalClosure_image_eq_top hKZ h3K
  have h8 : (⊤ : Subgroup (Y ⧸ center Y)) ⊓
      Subgroup.centralizer (Dbar : Set (Y ⧸ center Y)) ≤
      Subgroup.normalizer (Kbar : Set (Y ⧸ center Y)) :=
    inf_centralizer_le_normalizer hSE hKZ hp hpZ hD0K hcardD
  have h9 : (⊤ : Subgroup (Y ⧸ center Y)) ≠ Kbar :=
    top_ne_image_of_isStronglyPEmbedded hSE
  have hU3top : IsU3 ↥(⊤ : Subgroup (Y ⧸ center Y)) (2 * n) :=
    hId (Y ⧸ center Y) (hYk.quotient (center Y)) hcore ⊤ Kbar Dbar n p
      Subgroup.normal_top h6 h7 hKbar hL2bar hn hne hp hpn hDbar_le hDcard h8 h9
  exact CFSG.Blueprint.LieModel.of_mulEquiv Subgroup.topEquiv hU3top

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8106K
