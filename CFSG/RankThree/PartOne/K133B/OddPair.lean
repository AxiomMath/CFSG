module

public import CFSG.RankThree.PartOne.K133B.Heavy
public import CFSG.RankThree.PartOne.PAIR22.LiftAll
public import CFSG.RankThree.PartOne.K133.OddRow8

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320X
  CFSG.RankThree.PartOne.PAIR22 CFSG.RankThree.PartOne.Q1327T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kf1322Odd_of_lifts_pair (hS : SchreierFor InCatalog) (hRe : Sec13Reinst)
    (h133 : KF133Two) (hT8 : KF132Types 8) (hSLB : N143.SectionListBound)
    (hInsp : Row8U3Inspection) (hOdd : Row8OddInspection) (hNC : Row8NotCentral5)
    (hLift : PairLiftAll) : N1322.KF1322Odd := by
  intro G _ _ p A c L E h hF hF13 hT hEA _ t ht s hs hodd
  have hp := h.prime
  by_cases hcomm : t * s = s * t
  ·
    left
    have h2 : (t * s) ^ 2 = 1 := by
      calc (t * s) ^ 2 = t * (s * t) * s := by rw [pow_two]; group
        _ = t * (t * s) * s := by rw [← hcomm]
        _ = (t * t) * (s * s) := by group
        _ = 1 := by rw [RefFacts.mul_self_eq_one ht.1, RefFacts.mul_self_eq_one hs.1, one_mul]
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
    · exact h1
    · rw [h2'] at hodd
      exact absurd hodd (by decide)
  ·
    obtain ⟨hrt, X, hX, htX⟩ := ht
    have ht' : t ∈ reflectionSet p E := ⟨hrt, X, hX, htX⟩
    obtain ⟨B, c', hB, hc'B, hc'1, hX12, hXF, hX13, hXT⟩ := hRe G p A c L E h hF13 hT X hX
    obtain ⟨Kt, hKt, hqt⟩ := hLift G p A c L E h hF hF13 hT hEA t ht'
    obtain ⟨Ks, hKs, hqs⟩ := hLift G p A c L E h hF hF13 hT hEA s hs
    have hKtIs : IsKt p E t Kt := hKt.1
    have hKt0 := hKt
    have hKs0 := hKs
    have hw1 : (1 : G) ∈ Subgroup.normalizer (E : Set G) := Subgroup.one_mem _
    have hconj1 : conjAut E 1 hw1 * t * (conjAut E 1 hw1)⁻¹ = t := by
      have : conjAut E 1 hw1 = 1 := map_one _
      rw [this]; group
    have htX' : conjAut E 1 hw1 * t * (conjAut E 1 hw1)⁻¹ ∈ torusImage E X := by
      rw [hconj1]; exact htX
    rcases pair_dich hS h133 hX12 hXF hX13 hXT ht' hs hw1 htX' hKt hqt hKs hqs with
      ⟨e, I₁, I₂, heE, -, -, -, hI₁, hI₂, hne, hK₁, hK₂⟩ |
        ⟨e, I, heE, he1, hetE, hesE, hI, hKtI, hKsI, hcase⟩
    · exfalso
      apply hcomm
      obtain ⟨-, -, -, -, kt, hkt, hktK, hkt_eq⟩ := hKt
      obtain ⟨-, -, -, -, ks, hks, hksK, hks_eq⟩ := hKs
      have := commute_of_distinct_components hp h.E_elem heE hI₁ hI₂ hne (hK₁ hktK) (hK₂ hksK)
        hkt hks
      rw [hkt_eq, hks_eq] at this
      exact this
    · obtain ⟨-, -, -, -, kt, hkt, hktK, hkt_eq⟩ := hKt
      obtain ⟨-, -, -, -, ks, hks, hksK, hks_eq⟩ := hKs
      rcases hcase with ⟨hEB, f, hf1, hpf, hmod4⟩ | ⟨J, hJ, hKtJ, hKsJ⟩
      ·
        have htI : t ∈ torusImage E I :=
          Sec12Three.mem_torusImage_iff.mpr ⟨kt, hKtI hktK, hkt, hkt_eq⟩
        have hsI : s ∈ torusImage E I :=
          Sec12Three.mem_torusImage_iff.mpr ⟨ks, hKsI hksK, hks, hks_eq⟩
        have hrow : RowModel p X 8 := ⟨f, hf1, hpf, hmod4⟩
        have hdatum : OddOrderOneOrThree ↥(torusImage E I) := by
          obtain ⟨f', hRM, hKR, hmov⟩ := hT8 G p B c' X E hX12 hXF hX13 hXT hrow (fun _ => hEB)
            (fun h9 => absurd h9 (by norm_num)) t ht' htX Kt hKtIs
          obtain ⟨hf1', hpf', -⟩ := hRM
          rcases hKR with hKR | hKR
          · exact oddDatum_of_pair hSLB hInsp hOdd hNC hX12 hX13 hEB ht' hs hcomm hKt0 hKs0 hKR
              hpf' he1 hetE hI hKtI hKsI
          · have hp2 : p ≠ 2 := by have := hX12.three_lt; omega
            have hdvd : p ∣ 2 ^ (2 * f') - 1 := by
              refine hpf'.trans ⟨2 ^ f' - 1, ?_⟩
              have h2f : 2 ^ (2 * f') = (2 ^ f') ^ 2 := pow_mul' 2 2 f'
              have hpos : 1 ≤ 2 ^ f' := Nat.one_le_two_pow
              rw [h2f]
              zify [hpos, Nat.one_le_pow 2 (2 ^ f') (by omega)]
              ring
            exact K133.oddOrderOneOrThree_of_split hS hX12 hX13 hEB ht' hKtIs
              (K133.splitType_of_psl_two hp hp2 hKR hdvd) (hmov le_rfl) hetE he1 hI hKtI
        have hmul : t * s ∈ torusImage E I := (torusImage E I).mul_mem htI hsI
        have := hdatum ⟨t * s, hmul⟩ (by rwa [Subgroup.orderOf_mk])
        rwa [Subgroup.orderOf_mk] at this
      ·
        have htJ : t ∈ torusImage E J :=
          Sec12Three.mem_torusImage_iff.mpr ⟨kt, hKtJ hktK, hkt, hkt_eq⟩
        have hsJ : s ∈ torusImage E J :=
          Sec12Three.mem_torusImage_iff.mpr ⟨ks, hKsJ hksK, hks, hks_eq⟩
        have hmul : t * s ∈ torusImage E J := (torusImage E J).mul_mem htJ hsJ
        have := K133.oddOrderOneOrThree_of_zeroStar h hF13 hEA hJ ⟨t * s, hmul⟩
          (by rwa [Subgroup.orderOf_mk])
        rwa [Subgroup.orderOf_mk] at this

section Heavy

theorem kf1322Odd_of_heavy (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (h133 : KF133Two)
    (hSLB : N143.SectionListBound) (hInsp : Row8U3Inspection) (hHeavy : Row8OddHeavy) :
    N1322.KF1322Odd :=
  kf1322Odd_of_lifts_pair hS hRe h133 (kf132Types_row8 hGA) hSLB hInsp
    (row8OddInspection_of_heavy hHeavy) hHeavy.2.2.2.2
    (pairLiftAll_of_rows hRe (pairLiftRows_holds hGA))

end Heavy

end CFSG.RankThree.PartOne.K133B
