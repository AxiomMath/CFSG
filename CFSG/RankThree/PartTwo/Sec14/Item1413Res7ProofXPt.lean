module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofLift
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofPoints
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofXPt

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Proof1413Res7

variable {G : Type} [Group G] [Finite G]

theorem not_transOn_of_l3
    (h131 : Item131) (h142 : Item142AllS14) {A L : Subgroup G}
    {a : G} (h' : Sec14Std G A a L) (hPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA a L A)) {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e) (hp3 : 3 < p)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) :
    ¬ TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h'.toSec13Data
  have hA3 : IsPGroup 3 A := h'.isE27.isPGroup
  obtain ⟨haL, h9, hAa, hQ⟩ := Proof1413Res6.l3_point_facts h131 hD ⟨p, e, ‹_›, he, hiso⟩ hPGL
  obtain ⟨hEe, hE9, htr⟩ := Proof1413Res6.hess_of_l3_point hD haL h9 hAa hQ
  have hp2 : p ≠ 2 := by omega
  have hCN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h' (Proof1413Res3.three_dvd_card_of_card_inf h9)
  have hXC : xA A ≤ Subgroup.centralizer ({a} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A))
  have hS : ∀ ab ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
      ab ≠ 1 → ∃ S ∈ scriptQPi A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2),
        ∃ s : ↥L, (s : G) ∈ S ∧
          QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s ∈ Res8Hess.thetaC ab ∧
          QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) s ≠ 1 := by
    intro ab hab hab1
    obtain ⟨z, hz, hz2⟩ := exists_orderOf_two_mem_thetaC he hp2 hiso hEe hE9 htr hab hab1
    have h2 : 2 ∣ Nat.card (Res8Hess.thetaC ab) := by
      rw [← hz2]
      exact Subgroup.orderOf_dvd_natCard _ hz
    obtain ⟨S, hSΘ, hS2, hAS, s, hsS, hs1⟩ :=
      exists_sylow_thetaPre hA3 (le_normalizer_thetaPre hD hAa hab) h2
    have hSL : S ≤ L := hSΘ.trans (thetaPre_le L ab)
    have hSq : S ∈ scriptQ A (lB A) := mem_scriptQ_of_point h142 h'
      (hSL.trans (hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers a)))
      (Proof1413Res5.not_three_dvd_of_two hS2) hAS
    exact ⟨S, ⟨⟨hSq, hSL.trans hD.le_centralizer⟩, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩,
      s, hsS, (mem_thetaPre_iff.mp (hSΘ hsS)).2, hs1⟩
  obtain ⟨a₁, ha₁, ha₁1, a₂, ha₂, ha₂n⟩ := Res8Hess.exists_pair_of_card_nine hEe hE9
  have ha₂1 : a₂ ≠ 1 := fun h => ha₂n (h ▸ Subgroup.one_mem _)
  obtain ⟨S₁, hS₁, s₁, hs₁, hs₁θ, hs₁1⟩ := hS a₁ ha₁ ha₁1
  obtain ⟨S₂, hS₂, s₂, hs₂, hs₂θ, hs₂1⟩ := hS a₂ ha₂ ha₂1
  obtain ⟨S, hS₁S, hSm⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2))) hS₁
  obtain ⟨T, hS₂T, hTm⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2))) hS₂
  intro htrans
  exact not_isConjIn_of_types he hp3 hiso hEe hE9 htr hD.le_normalizer (hXC.trans hCN) ha₁ ha₁1
    ha₂ ha₂n hs₁ hs₁θ hs₁1 hs₂ hs₂θ hs₂1 hS₁S hTm hS₂T (htrans S hSm T hTm)

theorem theta_sup_xA_mem_scriptQ (h142 : Item142AllS14) {A L : Subgroup G} {a : G}
    (h' : Sec14Std G A a L) :
    inSubgroup (aschbacherSolvableCore 3) L ⊔ xA A ∈ scriptQ A (lB A) ∧
      inSubgroup (aschbacherSolvableCore 3) L ⊔ xA A ≤ Subgroup.centralizer ({a} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h'.toSec13Data
  have hA27 : IsE27 A := h'.isE27
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h'.chosen136.2 a hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hCN : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h' h3L
  have hXC : xA A ≤ Subgroup.centralizer ({a} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A))
  have hXθ : xA A ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore 3) L : Subgroup G) : Set G) :=
    (hXC.trans hCN).trans (Sec6.normalizer_le_normalizer_theta L)
  have hZa : inSubgroup (aschbacherSolvableCore 3) L ⊔ xA A ≤
      Subgroup.centralizer ({a} : Set G) :=
    sup_le ((Sec6.theta_le L).trans hD.le_centralizer) hXC
  have hZ3 : ¬ 3 ∣ Nat.card ↥(inSubgroup (aschbacherSolvableCore 3) L ⊔ xA A) := by
    rw [sup_comm]
    exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mp
      (isPiSubgroup_piCompl_sup
        ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr (Proof1413Res5.not_three_dvd_pCoreOf _))
        ((isPiSubgroup_piCompl_iff Nat.prime_three _).mpr (Sec6.theta_solvable_and_not_dvd L).2)
        hXθ)
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA27.1.1
  have hAX : A ≤ Subgroup.normalizer (xA A : Set G) :=
    (hAC.trans Subgroup.le_normalizer).trans (normalizer_le_normalizer_pPrimeCoreOf 3 _)
  have hAθ : A ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore 3) L : Subgroup G) : Set G) :=
    hD.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta L)
  exact ⟨mem_scriptQ_of_point h142 h' (hZa.trans (centralizer_singleton_le_normalizer_zpowers a))
    hZ3 (le_normalizer_sup hAθ hAX), hZa⟩

end Proof1413Res7

open Proof1413Res7 in
theorem claim1411NonsolvXPointL3R_of_res7
    (h131 : Item131)
    (h142All : Item142AllS14) (hbot : Item145BotS14) : Claim1411NonsolvXPointL3R := by
  intro G _ _ A c L hR hfail hloc Y hYΔ hY hs h3 hBc hIH S hS T hT hDST hbig hres a haA ha1 haS
    haT ha La hLa hL3 hPGL hout
  obtain ⟨p, e, hp, he, hiso⟩ := hL3
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  have hD := h'.toSec13Data
  have hYa := hres a haA ha1 haS haT
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨haL, h9, hAa, hQ⟩ := Proof1413Res6.l3_point_facts h131 hD ⟨2, e, hp, he, hiso⟩ hPGL
    obtain ⟨hEe, hE9, htr⟩ := Proof1413Res6.hess_of_l3_point hD haL h9 hAa hQ
    have hL2 : ∀ V : Subgroup G, IsPGroup 2 V → V ≤ La →
        A ≤ Subgroup.normalizer (V : Set G) → V ≤ inSubgroup (aschbacherSolvableCore 3) La :=
      fun V hV2 hVL hAV => le_theta_of_two he hiso hEe hE9 htr hV2 hVL hAV
    obtain ⟨hZq, -⟩ := theta_sup_xA_mem_scriptQ h142All h'
    have hZYq : (inSubgroup (aschbacherSolvableCore 3) La ⊔ xA A) ⊓ Y ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hZq inf_le_left (le_normalizer_inf hZq.1.2.2 hY.2)
    have hle : ∀ U ∈ scriptQPiStar A (lB A) Y (piOf 2),
        U ≤ (inSubgroup (aschbacherSolvableCore 3) La ⊔ xA A) ⊓ Y := fun U hU =>
      le_inf (le_theta_sup_xA h142All hbot h' hAa hL2
        (isPGroup_of_mem_scriptQPi Nat.prime_two hU.prop) (hU.prop.1.2.trans hYa)
        hU.prop.1.1.1.2.2) hU.prop.1.2
    exact Proof1413Res5.isConjIn_of_le_mem_scriptQ h'.isE27 (hbot G A a La h') hZYq inf_le_right
      hS hT (hle S hS) (hle T hT)
  · have hp3 : 3 < p := by
      have h2 := (Fact.out : p.Prime).two_le
      have h3' := Proof1413Res6.ne_three_of_isoLThreePi he hiso
      omega
    exact absurd (hloc a ha) (not_transOn_of_l3 h131 h142All h' hPGL he hp3 hiso)

end CFSG.RankThree.PartTwo.Sec14
