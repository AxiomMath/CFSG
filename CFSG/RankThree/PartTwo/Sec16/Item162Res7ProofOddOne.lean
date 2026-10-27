module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofOdd
public import CFSG.RankThree.PartTwo.Sec16.Item166Res4ProofOmg
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofXPt
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS

theorem step162UJOddOne_of_item148R
    (h148 : Item148R) (h131 : Item131)
    (h142All : Item142AllS14) (hbot : Item145BotS14) : Step162UJOddOne := by
  intro G _ _ A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J₀ hJ₀ hJ₀K hty hcov hside I hI hJI
    e Le he hLe hm hI1 hL1 hΩ hbar hM12 hna
  exfalso
  obtain ⟨n, hn, hiso⟩ := hty
  have hAab : IsMulCommutative A := h.isElemAbelian.1
  have hJΔ : J₀ = deltaZero A (lB A) J₀ :=
    rank3II_15_1_lB h.toSec14Std.isE27 (hbot G A c L h.toSec14Std) hJ₀.1
  refine Proof166Res4.false_of_isoLThreePi_two (h148 G A c L h) hAab h.chosen136
    (fun c' L' hc' hL' hL3 => ?_) hJ₀.1 hJΔ hn hiso
  obtain ⟨k, hk, hk'⟩ := hL3
  have hce : Subgroup.zpowers c' = Subgroup.zpowers e := by
    rw [hΩ] at hc'
    exact hc'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h' : Sec14Std G A c' L' := Proof1413.sec14Std_at h.toSec14Std hc' hL'
  apply hna
  rw [← KFacts.KS14.centralizer_eq_of_zpowers_eq hce]
  by_cases hPGL : Sec8.IsZ3PGLThreePi (lBarA c' L' A)
  ·
    have hc'A : c' ∈ A := (zpowers_mem_omegaA_iff.mp hc').1
    refine Proof1413Res5.transOn_of_pgl_point h131 h142All hbot h hc' hL' hPGL ?_ le_rfl
    exact ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc'A))).trans
        Subgroup.le_normalizer
  ·
    obtain ⟨haL, h9, hAa, hQ⟩ :=
      Proof1413Res6.l3_point_facts h131 h'.toSec13Data ⟨2, k, inferInstance, hk, hk'⟩ hPGL
    obtain ⟨hEe, hE9, htr⟩ := Proof1413Res6.hess_of_l3_point h'.toSec13Data haL h9 hAa hQ
    have hL2 : ∀ V : Subgroup G, IsPGroup 2 V → V ≤ L' →
        A ≤ Subgroup.normalizer (V : Set G) → V ≤ inSubgroup (aschbacherSolvableCore 3) L' :=
      fun V hV2 hVL hAV => Proof1413Res7.le_theta_of_two hk hk' hEe hE9 htr hV2 hVL hAV
    obtain ⟨hZq, hZa⟩ := Proof1413Res7.theta_sup_xA_mem_scriptQ h142All h'
    exact Proof1413Res5.transOn_of_le_mem_scriptQ h'.isE27
      (hbot G A c' L' h') hZq hZa fun U hU =>
        Proof1413Res7.le_theta_sup_xA h142All hbot h' hAa hL2
          (isPGroup_of_mem_scriptQPi Nat.prime_two hU) hU.1.2 hU.1.1.1.2.2

end CFSG.RankThree.PartTwo.Sec16
