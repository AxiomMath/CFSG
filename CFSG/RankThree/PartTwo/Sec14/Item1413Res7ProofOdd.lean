module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofXPt
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofPoints
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Proof1413Res7

variable {G : Type} [Group G] [Finite G]

theorem transOn_of_isSolvable_of_point (h142 : Item142AllS14) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y : Subgroup G}
    (hYH : Y ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hYΔ : Y = delta A (lB A) Y) (hY : Y ∈ scriptY A) (hYs : Group.IsSolvable ↥Y) :
    TransOn A (lB A) (xA A) Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := h.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  obtain ⟨hdelta, -, -⟩ := rank3II_14_5_lB hA hbot hY.2
  set R := pPrimeCoreOf 3 Y with hR
  set C' := xA A ⊓ Y with hC'
  have hDR : deltaZero A (lB A) Y ≤ R :=
    item148Solvable_of_mem_partTwoF h.toSec13Data.mem_partTwoF Y hY hYs
  have hYRC : Y ≤ C' ⊔ R := by
    calc Y = delta A (lB A) Y := hYΔ
      _ = deltaZero A (lB A) Y ⊔ C' := hdelta
      _ ≤ R ⊔ C' := sup_le_sup_right hDR _
      _ = C' ⊔ R := sup_comm _ _
  have hC'R : C' ≤ Subgroup.normalizer (R : Set G) :=
    inf_le_right.trans (le_normalizer_pPrimeCoreOf 3 Y)
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro h3
    have hdvd := h3.trans ((Subgroup.card_dvd_of_le hYRC).trans (card_sup_dvd_card_mul hC'R))
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
        (h1.trans (Subgroup.card_dvd_of_le inf_le_left))
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y) h1
  have hYQ : Y ∈ scriptQ A (lB A) := mem_scriptQ_of_point h142 h hYH hY3 hY.2
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1
  have hsyl : ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), CFSG.Open.fusionIsSylowIn 2 S Y ∧
      A ≤ Subgroup.normalizer (S : Set G) := by
    intro S hS
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
    obtain ⟨S', hS', hSS', hAS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA3 hY3 hY.2 hS.prop.1.2 hS2 hAS
    have hS'mem : S' ∈ scriptQPi A (lB A) Y (piOf 2) :=
      ⟨⟨mem_scriptQ_of_le hYQ hS'.1 hAS', hS'.1⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two S').mpr hS'.2.1⟩
    have := hS.eq_of_le hS'mem hSS'
    exact ⟨this ▸ hS', hAS⟩
  intro S hS T hT
  obtain ⟨hSs, hAS⟩ := hsyl S hS
  obtain ⟨hTs, hAT⟩ := hsyl T hT
  obtain ⟨x, hx, hxT⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three
    Nat.prime_two hA3 hY3 hY.2 hSs hTs hAS hAT
  have hCYA : Y ⊓ Subgroup.centralizer (A : Set G) ≤ xA A := by
    refine le_pPrimeCoreOf_centralizer hbot (mem_scriptQ_of_le hYQ inf_le_left ?_) inf_le_right
    exact le_normalizer_inf hY.2 (hAC.trans Subgroup.le_normalizer)
  exact ⟨x, ⟨hCYA hx, (Subgroup.mem_inf.mp hx).1⟩, hxT⟩

theorem transOn_of_fail (h142 : Item142AllS14) (hbot : Item145BotS14) {A L : Subgroup G} {c : G}
    (h' : Sec14Std G A c L) (hfail : Fail1411 A (lB A)) {Y : Subgroup G}
    (hYH : Y ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hYΔ : Y = delta A (lB A) Y) (hY : Y ∈ scriptY A) (hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥) :
    TransOn A (lB A) (xA A) Y := by
  by_cases hres : inSubgroup perfectResidual Y = ⊥
  · refine transOn_of_isSolvable_of_point h142 h' (hbot G A c L h') hYH hYΔ hY ?_
    have h0 : perfectResidual ↥Y = ⊥ := by
      rw [inSubgroup] at hres
      exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hres
    exact (perfect_residual_characterization (G := ↥Y)).2.2.2.2.2.mp h0
  · exact hfail.2 Y hYΔ hY hO2 hres

open Proof1413Res5 in
theorem not_two_dvd_xA_of_l3
    (h131 : Item131) (h142All : Item142AllS14)
    (hbot : Item145BotS14) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L) (hfail : Fail1411 A (lB A)) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ gammaA A (lB A)) {L' : Subgroup G} (hL' : L' ∈ lA A c')
    (hL3 : IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L')) : ¬ 2 ∣ Nat.card ↥(xA A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h' : Sec14Std G A c' L' := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := h'.toSec13Data
  have hA27 : IsE27 A := h'.isE27
  have hA3 : IsPGroup 3 A := hA27.isPGroup
  have hc'A : c' ∈ A := hD.mem_A
  have hbot' := hbot G A c' L' h'
  have hnotPGL := item1412NotPGLR_of h131 h142All hbot G A c L hR hfail c' hc' L' hL'
  obtain ⟨hcL, h9, hAa, hQ⟩ := Proof1413Res6.l3_point_facts h131 hD hL3 hnotPGL
  obtain ⟨hEe, hE9, htr⟩ := Proof1413Res6.hess_of_l3_point hD hcL h9 hAa hQ
  obtain ⟨p, e, hp, he, hiso⟩ := hL3
  have hXC : xA A ≤ Subgroup.centralizer ({c'} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc'A))
  have hCH : Subgroup.centralizer ({c'} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c' : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c'
  have hCN : Subgroup.centralizer ({c'} : Set G) ≤ Subgroup.normalizer (L' : Set G) :=
    centralizer_le_normalizer_of_three_dvd h' (Proof1413Res3.three_dvd_card_of_card_inf h9)
  by_cases hp2 : p = 2
  ·
    exfalso
    subst hp2
    have hL2 : ∀ V : Subgroup G, IsPGroup 2 V → V ≤ L' →
        A ≤ Subgroup.normalizer (V : Set G) → V ≤ inSubgroup (aschbacherSolvableCore 3) L' :=
      fun V hV2 hVL hAV => le_theta_of_two he hiso hEe hE9 htr hV2 hVL hAV
    obtain ⟨hZq, hZa⟩ := theta_sup_xA_mem_scriptQ h142All h'
    apply hc'.2
    rw [transOn_normalizer_iff hA27 hc'A]
    exact transOn_of_le_mem_scriptQ hA27 hbot' hZq hZa fun U hU =>
      le_theta_sup_xA h142All hbot h' hAa hL2 (isPGroup_of_mem_scriptQPi Nat.prime_two hU)
        hU.1.2 hU.1.1.1.2.2
  have hp3 : 3 < p := by
    have h2 := (Fact.out : p.Prime).two_le
    have h3' := Proof1413Res6.ne_three_of_isoLThreePi he hiso
    omega
  intro h2
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥(xA A)) 2 h2
  have hro : orderOf (r : G) = 2 := by rw [Subgroup.orderOf_coe, hr]
  have hr2 : (r : G) ^ 2 = 1 := by rw [← hro]; exact pow_orderOf_eq_one _
  have hrX : (r : G) ∈ xA A := r.2
  have hrA : (r : G) ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hrX
  have hrN : (r : G) ∈ Subgroup.normalizer (L' : Set G) := hCN (hXC hrX)
  have hAr : A ≤ Subgroup.centralizer ({(r : G)} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hrA b hb)
  have hθodd : ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) L') := fun h =>
    Proof1413Res6.not_two_dvd_centralizer_of_gamma' sporadicModels131 h142All hbot hR hfail hc'
      hL' hAa (h.trans (Subgroup.card_dvd_of_le (le_inf
        ((Sec6.theta_le L').trans (Sec6.le_centralizer_of_mem_thetaComponentsAt hL'.1))
        (Sec6.theta_le_thetaQuotCentralizer L'))))
  set Y := delta A (lB A) (Subgroup.centralizer ({c'} : Set G) ⊓
    Subgroup.centralizer ({(r : G)} : Set G)) with hYdef
  have hYle : Y ≤ Subgroup.centralizer ({c'} : Set G) ⊓ Subgroup.centralizer ({(r : G)} : Set G) :=
    delta_le _
  have hYΔ : Y = delta A (lB A) Y := (delta_delta _).symm
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hc'1 : c' ≠ 1 := by
    intro h1
    have h3 := hD.orderOf_eq
    rw [h1, orderOf_one] at h3
    omega
  have hYY : Y ∈ scriptY A := by
    refine ⟨fun hYt => ?_, hAY⟩
    apply centralizer_singleton_ne_top hD.isSimpleGroup hD.nonabelian hc'1
    exact eq_top_iff.mpr (hYt ▸ hYle.trans inf_le_left)
  have hR2 : IsPGroup 2 (Subgroup.zpowers (r : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hro, pow_one])
  have hrQ : Subgroup.zpowers (r : G) ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_point h142All h' (Subgroup.zpowers_le.mpr (hCH (hXC hrX)))
      (not_three_dvd_of_two hR2) (hAr.trans (centralizer_singleton_le_normalizer_zpowers _))
  have hrC : Subgroup.zpowers (r : G) ≤ Subgroup.centralizer ({(r : G)} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hRY : Subgroup.zpowers (r : G) ≤ Y :=
    le_delta hrQ (le_inf (Subgroup.zpowers_le.mpr (hXC hrX)) hrC)
  have hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := by
    intro hb
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRY
      ((hYle.trans inf_le_right).trans (centralizer_singleton_le_normalizer_zpowers _)) hR2
    rw [hb, le_bot_iff] at h1
    have h2 : (r : G) = 1 := by
      have := Subgroup.mem_zpowers (r : G)
      rwa [h1, Subgroup.mem_bot] at this
    rw [h2, orderOf_one] at hro
    omega
  have hYtr := transOn_of_fail h142All hbot h' hfail ((hYle.trans inf_le_left).trans hCH) hYΔ
    hYY hO2
  have hS : ∀ ab ∈ (A.subgroupOf L').map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L')),
      ab ≠ 1 → ∃ S ∈ scriptQPi A (lB A) Y (piOf 2), ∃ s : ↥L', (s : G) ∈ S ∧
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L') s ∈ Res8Hess.thetaC ab ∧
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L') s ≠ 1 := by
    intro ab hab hab1
    have hp2' : p ≠ 2 := hp2
    have hΘ2 : 2 ∣ Nat.card (thetaPre L' ab) :=
      two_dvd_card_thetaPre (exists_orderOf_two_mem_thetaC he hp2' hiso hEe hE9 htr hab hab1)
    have hrΘ : (r : G) ∈ Subgroup.normalizer (thetaPre L' ab : Set G) :=
      mem_normalizer_thetaPre hrN (Proof1413Res6.aut_fix_of_mem hrA hrN ab hab)
    obtain ⟨S, hSΘ, hS2, hAS, s, hsS, hs1⟩ := exists_sylow_thetaPre_centralizer hA3
      (le_normalizer_thetaPre hD hAa hab) hAr hr2 hrΘ hΘ2 hθodd
    have hSL : S ≤ L' := (hSΘ.trans inf_le_left).trans (thetaPre_le L' ab)
    have hSq : S ∈ scriptQ A (lB A) := mem_scriptQ_of_point h142All h'
      (hSL.trans (hD.le_centralizer.trans hCH)) (not_three_dvd_of_two hS2) hAS
    have hSY : S ≤ Y := le_delta hSq (le_inf (hSL.trans hD.le_centralizer)
      (hSΘ.trans inf_le_right))
    exact ⟨S, ⟨⟨hSq, hSY⟩, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩, s, hsS,
      (mem_thetaPre_iff.mp (hSΘ hsS).1).2, hs1⟩
  obtain ⟨a₁, ha₁, ha₁1, a₂, ha₂, ha₂n⟩ := Res8Hess.exists_pair_of_card_nine hEe hE9
  have ha₂1 : a₂ ≠ 1 := fun h => ha₂n (h ▸ Subgroup.one_mem _)
  obtain ⟨S₁, hS₁, s₁, hs₁, hs₁θ, hs₁1⟩ := hS a₁ ha₁ ha₁1
  obtain ⟨S₂, hS₂, s₂, hs₂, hs₂θ, hs₂1⟩ := hS a₂ ha₂ ha₂1
  obtain ⟨P₁, hS₁P, hP₁⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) Y (piOf 2))) hS₁
  obtain ⟨P₂, hS₂P, hP₂⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) Y (piOf 2))) hS₂
  exact not_isConjIn_of_types he hp3 hiso hEe hE9 htr hD.le_normalizer (hXC.trans hCN) ha₁ ha₁1
    ha₂ ha₂n hs₁ hs₁θ hs₁1 hs₂ hs₂θ hs₂1 hS₁P hP₂ hS₂P (hYtr P₁ hP₁ P₂ hP₂)

end Proof1413Res7

open Proof1413Res7 in
theorem item1413CL3R_of_res7
    (h131 : Item131) (h142All : Item142AllS14)
    (hbot : Item145BotS14) : Item1413CL3R := by
  intro G _ _ A c L hR hfail c' hc' L' hL' hL3 _
  exact ⟨not_two_dvd_centralizer_of_gamma_all h131 h142All hbot G A c L hR hfail c' hc' L' hL',
    not_two_dvd_xA_of_l3 h131 h142All hbot hR hfail hc' hL' hL3⟩

end CFSG.RankThree.PartTwo.Sec14
