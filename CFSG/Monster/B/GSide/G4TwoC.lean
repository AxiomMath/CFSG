module

public import CFSG.Monster.B.GSide.G4Exclusions
public import CFSG.Monster.B.GSide.TwoCCentralizer
public import CFSG.Monster.B.GSide.TriangleData
public import CFSG.Monster.B.CTIB.DistThreeProductFinal
public import CFSG.Monster.B.CTIB.Rank2168Final
public import CFSG.Monster.B.TwoA.Amalgam.TypeFourDistFinal
public import CFSG.Monster.B.Generic.RankFourSpectral
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3013
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3023
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3044
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3059
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3121
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate3176
public import Certificates.Certificate6007
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate16042
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open MulOpposite CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam CFSG.LocalAnalysis.ComponentInitial
open CFSG.Monster.Generated (Gmat)
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup mem_betaGroup_iff)
open CFSG.Monster.B.E6.StdF4 (rootClass)
open CFSG.Monster.Existence (xGmat)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

section Lift

variable {K : Type*} [Group K] [Finite K]

theorem prime_dvd_natCard_centralizer_of_quot {N : Subgroup K} [N.Normal]
    (hN : ∀ n ∈ N, n * n = 1) (hNc : N ≤ Subgroup.center K) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (x : K)
    (h : p ∣ Nat.card (Subgroup.centralizer {(x : K ⧸ N)})) :
    p ∣ Nat.card (Subgroup.centralizer {x}) := by
  obtain ⟨g', hg'⟩ := exists_prime_orderOf_dvd_card' p h
  rw [← Subgroup.orderOf_coe] at hg'
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (g' : K ⧸ N)
  have hcomm : (g : K ⧸ N) * (x : K ⧸ N) = (x : K ⧸ N) * (g : K ⧸ N) := by
    rw [hg]
    exact Subgroup.mem_centralizer_singleton_iff.1 g'.2
  have hcen : ∀ n ∈ N, ∀ y : K, n * y = y * n := fun n hn y =>
    (Subgroup.mem_center_iff.1 (hNc hn) y).symm
  have hodd : ¬ p ∣ 2 := by
    intro h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2)
  set k := g ^ 2 with hk
  have hgp : g ^ p ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hg, ← hg', pow_orderOf_eq_one]
  have hkp : k ^ p = 1 := by
    rw [hk, ← pow_mul, mul_comm, pow_mul, sq, hN _ hgp]
  have hk1 : (k : K ⧸ N) ≠ 1 := by
    intro h1
    rw [hk, QuotientGroup.mk_pow, hg] at h1
    exact hodd (hg' ▸ orderOf_dvd_of_pow_eq_one h1)
  have hok : orderOf k = p := orderOf_eq_prime hkp fun h1 => hk1 (by rw [h1, QuotientGroup.mk_one])
  have hkx : k * x * k⁻¹ * x⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hk, QuotientGroup.mk_pow]
    have hc2 : (g : K ⧸ N) ^ 2 * (x : K ⧸ N) = (x : K ⧸ N) * (g : K ⧸ N) ^ 2 := by
      rw [sq, mul_assoc, hcomm, ← mul_assoc, hcomm, mul_assoc]
    rw [hc2]
    group
  set n := k * x * k⁻¹ * x⁻¹ with hn
  have hkxe : k * x * k⁻¹ = n * x := by rw [hn]; group
  have hjx : k ^ 2 * x = x * k ^ 2 := by
    have e : k ^ 2 * x * (k ^ 2)⁻¹ = x := by
      calc k ^ 2 * x * (k ^ 2)⁻¹ = k * (k * x * k⁻¹) * k⁻¹ := by rw [sq]; group
        _ = k * (n * x) * k⁻¹ := by rw [hkxe]
        _ = n * (k * x * k⁻¹) := by rw [← mul_assoc k n x, ← hcen n hkx k]; group
        _ = n * (n * x) := by rw [hkxe]
        _ = x := by rw [← mul_assoc, hN n hkx, one_mul]
    calc k ^ 2 * x = k ^ 2 * x * (k ^ 2)⁻¹ * k ^ 2 := by group
      _ = x * k ^ 2 := by rw [e]
  have hoj : orderOf (k ^ 2) = p := by
    rw [orderOf_pow' k two_ne_zero, hok, Nat.Coprime.gcd_eq_one
      ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2), Nat.div_one]
  let j : Subgroup.centralizer ({x} : Set K) :=
    ⟨k ^ 2, Subgroup.mem_centralizer_singleton_iff.2 hjx⟩
  have hoj' : orderOf j = p := by
    rw [← Subgroup.orderOf_coe]
    exact hoj
  exact hoj' ▸ orderOf_dvd_natCard j

end Lift

theorem not_dvd_17_natCard_Gvis :
    ¬ 17 ∣ Nat.card CFSG.Monster.Visible.Gvis := by
  rw [CFSG.Monster.Existence.natCard_Gvis, CFSG.Monster.Existence.twoBCentralizerOrder]
  decide

theorem not_dvd_17_natCard_centralizer_octadT :
    ¬ 17 ∣ Nat.card (Subgroup.centralizer {octadT} : Subgroup octadD) := by
  intro h
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hN : ∀ n ∈ selfZpowers hGmat, n * n = 1 := by
    intro n hn
    rcases (mem_selfZpowers_iff orderOf_hGmat).1 hn with rfl | h1
    · rw [mul_one]
    · apply Subtype.ext
      rw [Subgroup.coe_mul, h1, Subgroup.coe_one, ← sq, ← orderOf_hGmat, pow_orderOf_eq_one]
  have h1 := prime_dvd_natCard_centralizer_of_quot hN (selfZpowers_le_center hGmat)
    (p := 17) (by norm_num) ⟨xGmat, xGmat_mem_centralizer_hGmat⟩ h
  have e : (Subgroup.centralizer {(⟨xGmat, xGmat_mem_centralizer_hGmat⟩ :
      Subgroup.centralizer ({hGmat} : Set Gmat))}).map
        (Subgroup.centralizer ({hGmat} : Set Gmat)).subtype =
      Subgroup.centralizer ({hGmat, xGmat} : Set Gmat) := by
    ext g
    rw [mem_centralizer_pair_iff]
    constructor
    · rintro ⟨g', hg', rfl⟩
      refine ⟨(Subgroup.mem_centralizer_singleton_iff.1 g'.2).symm, ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg').symm
    · rintro ⟨h1, h2⟩
      refine ⟨⟨g, Subgroup.mem_centralizer_singleton_iff.2 h1.symm⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext h2.symm), rfl⟩
  rw [← Subgroup.card_map_of_injective
    (Subgroup.centralizer ({hGmat} : Set Gmat)).subtype_injective, e,
    Nat.card_congr centPairEquiv] at h1
  exact not_dvd_17_natCard_Gvis (h1.trans (Subgroup.card_subgroup_dvd_card _))

theorem not_dvd_17_natCard_centralizer_octadV :
    ¬ 17 ∣ Nat.card (Subgroup.centralizer {octadV} : Subgroup Dfull) := by
  rw [← Nat.card_congr centOctadVEquiv.toEquiv]
  exact not_dvd_17_natCard_centralizer_octadT

theorem exists_rank_2168_not_dvd_17 :
    ∃ w : Sbp, orderOf w = 2 ∧ ((βr w) - 1).rank = 2168 ∧
    ¬ 17 ∣ Nat.card (Subgroup.centralizer {w}) := by
  obtain ⟨s, ⟨g, hg⟩, hsS, ⟨R, hRT, hRn, hR2, hcen⟩, -, hcard⟩ :=
    sylow_containing_subgroup_local_normal_two_transfer exists_sylow_le_Shat orderOf_octadV
      isCharacteristicP_octadV
  have hs2 : orderOf s = 2 := by
    have e := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) octadV
    rw [MulAut.conj_apply, inv_inv] at e
    exact (congrArg orderOf hg).trans (e.trans orderOf_octadV)
  have hw : sEquiv (sEquiv.symm ⟨s, hsS⟩) = ⟨s, hsS⟩ := sEquiv.apply_symm_apply _
  let e : Subgroup.centralizer {sEquiv.symm ⟨s, hsS⟩} ≃*
      (Shat ⊓ Subgroup.centralizer {s} : Subgroup Dfull) :=
    ((centralizerEquiv sEquiv _).trans (MulEquiv.subgroupCongr
      (congrArg (fun y : Shat => Subgroup.centralizer {y}) hw))).trans (centShatEquiv ⟨s, hsS⟩)
  have hw2 : orderOf (sEquiv.symm ⟨s, hsS⟩) = 2 :=
    (MulEquiv.orderOf_eq sEquiv.symm _).trans
      ((Subgroup.orderOf_coe (⟨s, hsS⟩ : Shat)).symm.trans hs2)
  have hrank := rank_of_local_witness native_rank_2158_distance_three_product_final.2.1 hw2
    (exists_selfCent_of_le e hRT hRn hR2 hcen)
    (ordProj_le_of_mulEquiv e.symm (hcard.trans_le ordProj_octadV_le))
  refine ⟨_, hw2, hrank, fun h17 => ?_⟩
  rw [Nat.card_congr e.toEquiv] at h17
  have hsub : Nat.card (Shat ⊓ Subgroup.centralizer {s} : Subgroup Dfull) ∣
      Nat.card (Subgroup.centralizer {s} : Subgroup Dfull) :=
    Subgroup.card_dvd_of_le inf_le_right
  have hconj : g⁻¹ * octadV * g⁻¹⁻¹ = s := by rw [inv_inv, hg]
  rw [← Nat.card_congr (centConjEquiv g⁻¹ hconj).toEquiv] at hsub
  exact not_dvd_17_natCard_centralizer_octadV (h17.trans hsub)

theorem not_dvd_17_natCard_centralizer_of_rank_2168
    {y : Sbp} (hy : orderOf y = 2)
    (hr : ((βr y) - 1).rank = 2168) : ¬ 17 ∣ Nat.card (Subgroup.centralizer {y}) := by
  obtain ⟨w, hw, hwr, hw17⟩ := exists_rank_2168_not_dvd_17
  have hc : IsConj y w :=
    (isConj_rs_three_of_rank hy hr).trans (isConj_rs_three_of_rank hw hwr).symm
  obtain ⟨c, hc'⟩ := isConj_iff.1 hc
  rw [Nat.card_congr (centConjEquiv c hc').toEquiv]
  exact hw17

section BoseMesner

open Matrix

@[expose] def nbrQ : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0, 3968055, 0, 0, 0; 1, 46134, 2097152, 1824768, 0; 0, 3510, 837135, 3127410, 0;
    0, 648, 663552, 3295791, 8064; 0, 0, 0, 3898440, 69615]

theorem cast_rankFiveMatrix (i j : Fin 5) : (rankFiveMatrix i j : ℚ) = nbrQ i j := by
  fin_cases i <;> fin_cases j <;> norm_num [rankFiveMatrix, nbrQ]

@[expose] noncomputable def rkCell
    (x y : CVert) : Fin 5 :=
  (native_rank_five_exact_neighbor_matrix.1 x y).exists.choose

theorem mem_rkCell
    (x y : CVert) : y ∈ rankFiveOrbit x (rkCell x y) :=
  (native_rank_five_exact_neighbor_matrix.1 x y).exists.choose_spec

theorem rkCell_eq_iff
    {x y : CVert} {i : Fin 5} : rkCell x y = i ↔ y ∈ rankFiveOrbit x i := by
  constructor
  · rintro rfl
    exact mem_rkCell x y
  · intro h
    exact (native_rank_five_exact_neighbor_matrix.1 x y).unique (mem_rkCell x y) h

theorem rkCell_eq_zero_iff
    {x y : CVert} : rkCell x y = 0 ↔ y = x :=
  rkCell_eq_iff.trans Iff.rfl

theorem rkCell_eq_four_iff
    {x y : CVert} : rkCell x y = 4 ↔ y ∈ sphereDistThree x :=
  rkCell_eq_iff.trans Iff.rfl

theorem card_filter_adj_rkCell
    [Fintype CVert] [DecidableRel cgraph.Adj] (x y : CVert)
    (j : Fin 5) :
    ((Finset.univ.filter fun z => cgraph.Adj y z ∧ rkCell x z = j).card : ℚ) =
      nbrQ (rkCell x y) j := by
  have h : (cgraph.neighborSet y ∩ rankFiveOrbit x j).ncard = rankFiveMatrix (rkCell x y) j :=
    native_rank_five_exact_neighbor_matrix.2.2 x (rkCell x y) j y (mem_rkCell x y)
  rw [← cast_rankFiveMatrix, ← h, ← Set.ncard_coe_finset]
  congr 2
  ext z
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Set.mem_inter_iff,
    SimpleGraph.mem_neighborSet, rkCell_eq_iff]

@[expose] def krylovW : Fin 5 → Fin 5 → ℚ :=
  ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![3968055, 46134, 3510, 648, 0],
    ![183062249370, 10675767195, 5126835870, 4494634920, 2526189120],
    ![42362031396955725, 19446118978164300, 18385891884044100, 18242588599038000,
      17697925213113600]]

@[expose] def krylovU : Fin 5 → Fin 5 → ℚ :=
  ![![0, 0, 0, 0, 1], ![0, 0, 0, 8064, 69615],
    ![0, 14714929152, 25219434240, 27138633984, 36283268385],
    ![58389648196239360, 103089556354498560, 106037355791727360, 106479795215928960,
      108324195997206735],
    ![409065029540249783500800, 421433367712419505766400, 422135402539760362252800,
      422236778613853186368000, 422646081765931641679425]]

@[expose] def krylovC : Fin 5 → ℚ :=
  ![-208805604608289557334375, -1148833342527570238500, 66491913010103550, -318249959220, 76049]

theorem nbrQ_pow_mulVec_krylovW (k : Fin 5) : nbrQ ^ (k : ℕ) *ᵥ krylovW 0 = krylovW k := by
  have h : ∀ k : Fin 4, nbrQ *ᵥ krylovW k.castSucc = krylovW k.succ := by
    intro k
    fin_cases k <;> ext i <;> fin_cases i <;>
      norm_num [nbrQ, krylovW, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  have h0 : nbrQ *ᵥ krylovW 0 = krylovW 1 := h 0
  have h1 : nbrQ *ᵥ krylovW 1 = krylovW 2 := h 1
  have h2 : nbrQ *ᵥ krylovW 2 = krylovW 3 := h 2
  have h3 : nbrQ *ᵥ krylovW 3 = krylovW 4 := h 3
  fin_cases k
  · simp
  · simpa using h0
  · show nbrQ ^ 2 *ᵥ krylovW 0 = krylovW 2
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_one, h0, h1]
  · show nbrQ ^ 3 *ᵥ krylovW 0 = krylovW 3
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ', ← Matrix.mulVec_mulVec, pow_one, h0, h1,
      h2]
  · show nbrQ ^ 4 *ᵥ krylovW 0 = krylovW 4
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ', ← Matrix.mulVec_mulVec, pow_succ',
      ← Matrix.mulVec_mulVec, pow_one, h0, h1, h2, h3]

theorem nbrQ_pow_mulVec_krylovU (k : Fin 5) : nbrQ ^ (k : ℕ) *ᵥ krylovU 0 = krylovU k := by
  have h : ∀ k : Fin 4, nbrQ *ᵥ krylovU k.castSucc = krylovU k.succ := by
    intro k
    fin_cases k <;> ext i <;> fin_cases i <;>
      norm_num [nbrQ, krylovU, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  have h0 : nbrQ *ᵥ krylovU 0 = krylovU 1 := h 0
  have h1 : nbrQ *ᵥ krylovU 1 = krylovU 2 := h 1
  have h2 : nbrQ *ᵥ krylovU 2 = krylovU 3 := h 2
  have h3 : nbrQ *ᵥ krylovU 3 = krylovU 4 := h 3
  fin_cases k
  · simp
  · simpa using h0
  · show nbrQ ^ 2 *ᵥ krylovU 0 = krylovU 2
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_one, h0, h1]
  · show nbrQ ^ 3 *ᵥ krylovU 0 = krylovU 3
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ', ← Matrix.mulVec_mulVec, pow_one, h0, h1,
      h2]
  · show nbrQ ^ 4 *ᵥ krylovU 0 = krylovU 4
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ', ← Matrix.mulVec_mulVec, pow_succ',
      ← Matrix.mulVec_mulVec, pow_one, h0, h1, h2, h3]

theorem sum_krylovC_smul_krylovW :
    ∑ k, krylovC k • krylovW k = (541949930110068480000 : ℚ) • krylovU 0 := by
  ext i
  fin_cases i <;> norm_num [krylovC, krylovW, krylovU, Fin.sum_univ_five]

theorem sum_krylovC_mul_krylovU : ∑ k, krylovC k * krylovU k 4 = 0 := by
  norm_num [krylovC, krylovU, Fin.sum_univ_five]

theorem krylovU_zero_nonneg (i : Fin 5) : 0 ≤ krylovU 0 i := by
  fin_cases i <;> norm_num [krylovU]

theorem sphereDistThree_inter_eq_empty
    {p q : CVert} (hpq : cgraph.dist p q = 3) :
    sphereDistThree p ∩ sphereDistThree q = ∅ := by
  classical
  have : Finite CVert := short_F4_involution_coset_graph_data.1
  have : Fintype CVert := Fintype.ofFinite CVert
  set A := cgraph.adjMatrix ℚ with hA
  have hpow : ∀ (x : CVert) (k : ℕ) (c : Fin 5 → ℚ),
      (A ^ k) *ᵥ (c ∘ rkCell x) = (nbrQ ^ k *ᵥ c) ∘ rkCell x := fun x k c =>
    Generic.pow_adjMatrix_mulVec_comp cgraph nbrQ (rkCell x) (card_filter_adj_rkCell x) k c
  have hsymm : ∀ (k : ℕ) (f g : CVert → ℚ), (A ^ k *ᵥ f) ⬝ᵥ g = f ⬝ᵥ (A ^ k *ᵥ g) := by
    intro k f g
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, transpose_pow, hA,
      SimpleGraph.transpose_adjMatrix, dotProduct_comm]
  have hδ : krylovW 0 ∘ rkCell p = Pi.single p 1 := by
    funext y
    simp only [Function.comp_apply]
    by_cases hy : y = p
    · subst hy
      rw [(rkCell_eq_zero_iff (x := y) (y := y)).2 rfl, Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne hy]
      have h0 : rkCell p y ≠ 0 := fun h => hy (rkCell_eq_zero_iff.1 h)
      revert h0
      generalize rkCell p y = i
      intro h0
      fin_cases i
      · exact absurd rfl h0
      all_goals rfl
  have hqp : rkCell q p = 4 := rkCell_eq_four_iff.2 (mem_sphereDistThree.2 (by
    rw [SimpleGraph.dist_comm]
    exact hpq))
  have hD : (541949930110068480000 : ℚ) * ((krylovU 0 ∘ rkCell p) ⬝ᵥ (krylovU 0 ∘ rkCell q)) =
      0 := by
    have e1 : (541949930110068480000 : ℚ) • (krylovU 0 ∘ rkCell p) =
        ∑ k : Fin 5, krylovC k • (A ^ (k : ℕ) *ᵥ (krylovW 0 ∘ rkCell p)) := by
      funext y
      have := congrFun sum_krylovC_smul_krylovW (rkCell p y)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hpow, nbrQ_pow_mulVec_krylovW,
        Function.comp_apply]
      rw [this]
    rw [← smul_eq_mul, ← smul_dotProduct, e1, sum_dotProduct]
    simp only [smul_dotProduct, hsymm, hδ, single_dotProduct, one_mul, hpow,
      nbrQ_pow_mulVec_krylovU, Function.comp_apply, hqp, smul_eq_mul]
    exact sum_krylovC_mul_krylovU
  have h0 : (krylovU 0 ∘ rkCell p) ⬝ᵥ (krylovU 0 ∘ rkCell q) = 0 := by
    rcases mul_eq_zero.1 hD with h | h
    · norm_num at h
    · exact h
  ext v
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hvp hvq
  have hterm : ∀ y ∈ Finset.univ, 0 ≤ (krylovU 0 ∘ rkCell p) y * (krylovU 0 ∘ rkCell q) y :=
    fun y _ => mul_nonneg (krylovU_zero_nonneg _) (krylovU_zero_nonneg _)
  have hv := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 h0 v (Finset.mem_univ v)
  simp only [Function.comp_apply, rkCell_eq_four_iff.2 hvp, rkCell_eq_four_iff.2 hvq] at hv
  norm_num [krylovU] at hv

end BoseMesner

theorem right_eq_one_of_mem_commutator
    {ρ : vStab cv0 →* GStar}
    {y : vStab cv0} (hy : y ∈ commutator (vStab cv0)) : (ρ y).right = 1 := by
  set φ : vStab cv0 →* betaGroup := (SemidirectProduct.rightHom).comp ρ with hφ
  have hle : commutator (vStab cv0) ≤ φ.ker := by
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    rcases mem_betaGroup_iff.1 (φ a).2 with h | h <;>
      rcases mem_betaGroup_iff.1 (φ b).2 with h' | h'
    all_goals
      apply Subtype.ext
      simp only [Subgroup.coe_mul, h, h', one_mul, mul_one]
  have h := hle hy
  rw [MonoidHom.mem_ker] at h
  exact h

theorem right_cV0
    {ρ : vStab cv0 →* GStar} {iv : cgraph.neighborSet cv0 ≃ rootClass}
    (hρ : IsCompatLocal cv0 ρ iv) : (ρ cV0).right = 1 := by
  have h : ρ cV0 = 1 := (hρ.2.1 cV0).2 (by
    rw [coe_cV0, coe_clabelS]
    exact Subgroup.mem_zpowers _)
  rw [h, SemidirectProduct.one_right]

theorem right_clabelS_of_adj
    {ρ : vStab cv0 →* GStar} {iv : cgraph.neighborSet cv0 ≃ rootClass}
    (hρ : IsCompatLocal cv0 ρ iv) {z : CVert} (hz : cgraph.Adj cv0 z) :
    (ρ ⟨clabelS z, clabelS_mem_vStab_cv0_of_adj hz⟩).right = 1 := by
  rw [hρ.2.2.2.2 ⟨z, hz⟩ _ rfl, SemidirectProduct.right_inl]

theorem right_clabelS_of_dist_three
    {ρ : vStab cv0 →* GStar}
    {iv : cgraph.neighborSet cv0 ≃ rootClass} (hρ : IsCompatLocal cv0 ρ iv) {u : CVert}
    (hu : cgraph.dist cv0 u = 3) :
    (ρ ⟨clabelS u, clabelS_mem_vStab_cv0_of_dist_three (mem_sphereDistThree.2 hu)⟩).right ≠ 1 :=
  outerInput_of_ambient ambientRootOrbitsHyp cv0 u hu ρ iv hρ _ rfl

theorem rankS_one :
    rankS (1 : Shat) = 0 := by
  rw [rankS, map_one]
  exact rank_beta_one

theorem exists_eq_clabelS_mul_of_rank_2158
    {y : Shat} (hyo : orderOf y = 2)
    (hr : rankS y = 2158) :
    ∃ p q : CVert, cgraph.dist p q = 3 ∧ y = clabelS p * clabelS q := by
  obtain ⟨u₃, hu₃⟩ := sphereDistThree_nonempty_of_ambient ambientRootOrbitsHyp cv0
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_rankS_eq (orderOf_cV0_mul_clabelS hu₃) hyo
    ((rankS_cV0_mul_clabelS hu₃).trans hr.symm))
  refine ⟨cvMul cv0 g⁻¹, cvMul u₃ g⁻¹, ?_, ?_⟩
  · rw [dist_cvMul]
    exact mem_sphereDistThree.1 hu₃
  · rw [clabelS_cvMul, clabelS_cvMul, inv_inv, ← hg, coe_cV0]
    group

theorem not_swap_of_rank_2158
    {p q : CVert} (hpq : cgraph.dist p q = 3)
    (hr : rankS (clabelS p * clabelS q) = 2158)
    (h1 : clabelS cv0 * clabelS p * clabelS cv0 = clabelS q) : False := by
  have hpp : clabelS p * clabelS p = 1 := clabelS_mul_self' p
  have hqq : clabelS q * clabelS q = 1 := clabelS_mul_self' q
  have hcomm : Commute (clabelS p) (clabelS q) :=
    ((labelsInput_of_ambient ambientRootOrbitsHyp) p q hpq).2.2.2.symm
  have hsq : (clabelS cv0 * clabelS p) ^ 2 = clabelS p * clabelS q := by
    rw [sq, hcomm.eq]
    calc clabelS cv0 * clabelS p * (clabelS cv0 * clabelS p) =
        clabelS cv0 * clabelS p * clabelS cv0 * clabelS p := by group
      _ = clabelS q * clabelS p := by rw [h1]
  have hy1 : clabelS p * clabelS q ≠ 1 := by
    intro h
    have hpq' : p = q := clabelS_injective (eq_inv_of_mul_eq_one_left h |>.trans
      (inv_eq_of_mul_eq_one_right hqq))
    rw [hpq', SimpleGraph.dist_self] at hpq
    exact absurd hpq (by decide)
  have hyy : clabelS p * clabelS q * (clabelS p * clabelS q) = 1 := by
    calc clabelS p * clabelS q * (clabelS p * clabelS q) =
        clabelS p * (clabelS q * clabelS p) * clabelS q := by group
      _ = clabelS p * (clabelS p * clabelS q) * clabelS q := by rw [hcomm.eq]
      _ = 1 := by
        rw [← mul_assoc, hpp, one_mul, hqq]
  have h4 : orderOf (clabelS cv0 * clabelS p) = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := clabelS cv0 * clabelS p)
      (by rw [pow_one, hsq]; exact hy1)
      (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hsq, sq, hyy])
    rw [h]
    norm_num
  have hr2 : rankS ((clabelS cv0 * clabelS p) ^ 2) = 2048 := rankS_sq_of_orderOf_four h4
  rw [hsq] at hr2
  omega

theorem position_of_rank_2158
    {p q : CVert} (hpq : cgraph.dist p q = 3)
    (hr : rankS (clabelS p * clabelS q) = 2158)
    (hc : Commute (clabelS p * clabelS q) (clabelS cv0)) :
    cv0 = p ∨ cv0 = q ∨ (cgraph.Adj cv0 p ∧ cgraph.dist cv0 q = 3) ∨
      (cgraph.Adj cv0 q ∧ cgraph.dist cv0 p = 3) := by
  obtain ⟨hCiff, -⟩ := distance_three_product_full_centralizer_final hpq rfl rfl rfl
  have hcC : clabelS cv0 ∈ Subgroup.centralizer {clabelS p * clabelS q} :=
    Subgroup.mem_centralizer_singleton_iff.2 hc.eq.symm
  have hpqne : p ≠ q := by
    rintro rfl
    rw [SimpleGraph.dist_self] at hpq
    exact absurd hpq (by decide)
  have hne : clabelS p ≠ clabelS q := fun h => hpqne (clabelS_injective h)
  have hcc : clabelS cv0 * clabelS cv0 = 1 := clabelS_mul_self' cv0
  have hcinv : (clabelS cv0)⁻¹ = clabelS cv0 := inv_eq_of_mul_eq_one_right hcc
  rcases (image_conj_pair_eq_iff hne).1 ((hCiff _).1 hcC) with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rw [hcinv] at h1 h2
    have hcp : Commute (clabelS cv0) (clabelS p) := by
      show clabelS cv0 * clabelS p = clabelS p * clabelS cv0
      calc clabelS cv0 * clabelS p = clabelS cv0 * clabelS p * clabelS cv0 * clabelS cv0 := by
            rw [mul_assoc _ (clabelS cv0), hcc, mul_one]
        _ = clabelS p * clabelS cv0 := by rw [h1]
    have hcq : Commute (clabelS cv0) (clabelS q) := by
      show clabelS cv0 * clabelS q = clabelS q * clabelS cv0
      calc clabelS cv0 * clabelS q = clabelS cv0 * clabelS q * clabelS cv0 * clabelS cv0 := by
            rw [mul_assoc _ (clabelS cv0), hcc, mul_one]
        _ = clabelS q * clabelS cv0 := by rw [h2]
    by_cases hp0 : cv0 = p
    · exact Or.inl hp0
    by_cases hq0 : cv0 = q
    · exact Or.inr (Or.inl hq0)
    have hdiam := (diameter_three_rank_five_of_ambient ambientRootOrbitsHyp).1
    rcases adj_or_dist_three_of_commute hdiam hp0 hcp with hap | hdp <;>
      rcases adj_or_dist_three_of_commute hdiam hq0 hcq with haq | hdq
    · exfalso
      have h := dist_le_two_of_adj_adj hap.symm haq
      omega
    · exact Or.inr (Or.inr (Or.inl ⟨hap, hdq⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨haq, hdp⟩))
    · exfalso
      have hmem : cv0 ∈ sphereDistThree p ∩ sphereDistThree q :=
        ⟨mem_sphereDistThree.2 (by rw [SimpleGraph.dist_comm]; exact hdp),
          mem_sphereDistThree.2 (by rw [SimpleGraph.dist_comm]; exact hdq)⟩
      rw [sphereDistThree_inter_eq_empty hpq] at hmem
      exact hmem
  · rw [hcinv] at h1
    exact (not_swap_of_rank_2158 hpq hr h1).elim

theorem orderOf_coe_of_rank_2158
    {y : vStab cv0} (hy2 : y * y = 1)
    (hr : rankS (y : Shat) = 2158) : orderOf (y : Shat) = 2 := by
  have hy1 : (y : Shat) ≠ 1 := by
    intro h
    rw [h, rankS_one] at hr
    exact absurd hr (by decide)
  exact orderOf_eq_prime (by rw [sq, ← Subgroup.coe_mul, hy2, Subgroup.coe_one]) hy1

theorem right_ne_one_of_rank_2158
    {ρ : vStab cv0 →* GStar}
    {iv : cgraph.neighborSet cv0 ≃ rootClass} (hρ : IsCompatLocal cv0 ρ iv) {y : vStab cv0}
    (hy2 : y * y = 1) (hr : rankS (y : Shat) = 2158) : (ρ y).right ≠ 1 := by
  obtain ⟨p, q, hpq, hyl⟩ := exists_eq_clabelS_mul_of_rank_2158 (orderOf_coe_of_rank_2158 hy2 hr) hr
  have hcom : Commute (clabelS p * clabelS q) (clabelS cv0) := by
    rw [← hyl]
    exact (commute_clabelS_iff_mem cv0 _).2 y.2
  rcases position_of_rank_2158 hpq (hyl ▸ hr) hcom with rfl | rfl | ⟨hap, hdq⟩ | ⟨haq, hdp⟩
  · have e : y = cV0 * ⟨clabelS q, clabelS_mem_vStab_cv0_of_dist_three
        (mem_sphereDistThree.2 hpq)⟩ := Subtype.ext hyl
    rw [e, map_mul, SemidirectProduct.mul_right, right_cV0 hρ, one_mul]
    exact right_clabelS_of_dist_three hρ hpq
  · have hpq' : cgraph.dist cv0 p = 3 := by rw [SimpleGraph.dist_comm]; exact hpq
    have e : y = ⟨clabelS p, clabelS_mem_vStab_cv0_of_dist_three
        (mem_sphereDistThree.2 hpq')⟩ * cV0 := Subtype.ext hyl
    rw [e, map_mul, SemidirectProduct.mul_right, right_cV0 hρ, mul_one]
    exact right_clabelS_of_dist_three hρ hpq'
  · have e : y = ⟨clabelS p, clabelS_mem_vStab_cv0_of_adj hap⟩ *
        ⟨clabelS q, clabelS_mem_vStab_cv0_of_dist_three (mem_sphereDistThree.2 hdq)⟩ :=
      Subtype.ext hyl
    rw [e, map_mul, SemidirectProduct.mul_right, right_clabelS_of_adj hρ hap, one_mul]
    exact right_clabelS_of_dist_three hρ hdq
  · have e : y = ⟨clabelS p, clabelS_mem_vStab_cv0_of_dist_three (mem_sphereDistThree.2 hdp)⟩ *
        ⟨clabelS q, clabelS_mem_vStab_cv0_of_adj haq⟩ := Subtype.ext hyl
    rw [e, map_mul, SemidirectProduct.mul_right, right_clabelS_of_adj hρ haq, mul_one]
    exact right_clabelS_of_dist_three hρ hdp

theorem cV0_mul_self_vStab :
    cV0 * cV0 = 1 := (orderOf_two_iff.1 orderOf_cV0).1

theorem not_mem_commutator_of_rank_2158
    {y : vStab cv0} (hy2 : y * y = 1)
    (hr : rkH y = 2158 ∨ rkH (cV0 * y) = 2158) : y ∉ commutator (vStab cv0) := by
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal cv0
  intro hy
  have h1 := right_eq_one_of_mem_commutator (ρ := ρ) hy
  rcases hr with hr | hr
  · exact right_ne_one_of_rank_2158 hρ hy2 hr h1
  · have hcy2 : cV0 * y * (cV0 * y) = 1 := by
      calc cV0 * y * (cV0 * y) = cV0 * (y * cV0) * y := by group
        _ = cV0 * (cV0 * y) * y := by rw [← commute_cV0 y]
        _ = 1 := by rw [← mul_assoc, cV0_mul_self_vStab, one_mul, hy2]
    apply right_ne_one_of_rank_2158 hρ hcy2 hr
    rw [map_mul, SemidirectProduct.mul_right, right_cV0 hρ, h1, one_mul]

theorem commutator_mem_of_card_eq_two_mul {G : Type*} [Group G] [Finite G] {C N : Subgroup G}
    (hNC : N ≤ C) (hcard : Nat.card C = 2 * Nat.card N) {a b : G} (ha : a ∈ C) (hb : b ∈ C) :
    a * b * a⁻¹ * b⁻¹ ∈ N := by
  have hN : Nat.card (N.subgroupOf C) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
  have hidx : (N.subgroupOf C).index = 2 := by
    have h := (N.subgroupOf C).card_mul_index
    rw [hN, hcard] at h
    have hpos : 0 < Nat.card N := Nat.card_pos
    nlinarith
  have key : (⟨a, ha⟩ : C) * ⟨b, hb⟩ * (⟨a, ha⟩ : C)⁻¹ * (⟨b, hb⟩ : C)⁻¹ ∈ N.subgroupOf C := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
    tauto
  exact Subgroup.mem_subgroupOf.1 key

theorem false_of_mixed_rank_2158
    {y : vStab cv0} {p q : CVert} (hpq : cgraph.dist p q = 3)
    (hyl : (y : Shat) = clabelS p * clabelS q) (hap : cgraph.Adj cv0 p)
    (hcard : Nat.card (Subgroup.centralizer {y}) = 13244506413465600) : False := by
  obtain ⟨-, hRv, hRC, -, -, hCcard, -, -, hFcard, -⟩ :=
    distance_three_product_full_centralizer_final hpq
      (R := Subgroup.centralizer {clabelS p, clabelS q})
      (F := ⁅Subgroup.centralizer {clabelS p, clabelS q},
        Subgroup.centralizer {clabelS p, clabelS q}⁆)
      (C := Subgroup.centralizer {clabelS p * clabelS q}) rfl rfl rfl
  set C := Subgroup.centralizer ({clabelS p * clabelS q} : Set Shat) with hC
  set R := Subgroup.centralizer ({clabelS p, clabelS q} : Set Shat) with hR
  have hNcard : Nat.card (Subgroup.centralizer {(cV0 : Shat)} ⊓ C : Subgroup Shat) =
      13244506413465600 := by
    rw [natCard_centralizer_eq_inf, hyl, ← centralizer_cV0, inf_comm] at hcard
    exact hcard
  have hcomm : ∀ a ∈ C, ∀ b ∈ C,
      a * b * a⁻¹ * b⁻¹ ∈ (Subgroup.centralizer {(cV0 : Shat)} ⊓ C) :=
    fun a ha b hb => commutator_mem_of_card_eq_two_mul inf_le_right
      (by rw [hCcard, hNcard]) ha hb
  have hF : ⁅R, R⁆ ≤ vStab cv0 ⊓ vStab p := by
    intro f hf
    have hfN : f ∈ Subgroup.centralizer {(cV0 : Shat)} ⊓ C :=
      (Subgroup.commutator_le.2 fun a ha b hb => hcomm a (hRC ha) b (hRC hb)) hf
    have hfR : f ∈ R := commutator_self_le R hf
    rw [hRv] at hfR
    refine ⟨?_, hfR.1⟩
    rw [← centralizer_cV0]
    exact hfN.1
  have hdvd := Subgroup.card_dvd_of_le hF
  rw [hFcard, natCard_vStab_inf_of_adj hap] at hdvd
  norm_num at hdvd

theorem rankS_clabelS
    (v : CVert) : rankS (clabelS v) = 1860 := rank_clabelS v

theorem h2C_rank_1860
    {y : vStab cv0} (hy : orderOf y = 2)
    (hcard : Nat.card (Subgroup.centralizer {y}) = 13244506413465600)
    (hr : rankS (y : Shat) = 1860) (hc : rankS (y : Shat) = rankS ((cV0 : Shat) * y)) : False := by
  have hyo : orderOf (y : Shat) = 2 := by rw [Subgroup.orderOf_coe, hy]
  obtain ⟨u, hu⟩ := (rankS_eq_1860_iff_label hyo).1 hr
  have hcu : Commute (clabelS cv0) (clabelS u) := by
    rw [← hu]
    exact ((commute_clabelS_iff_mem cv0 _).2 y.2).symm
  by_cases h0 : cv0 = u
  · subst h0
    rw [hu, coe_cV0, clabelS_mul_self', rankS_one] at hc
    rw [hu] at hr
    omega
  have hdiam := (diameter_three_rank_five_of_ambient ambientRootOrbitsHyp).1
  rcases adj_or_dist_three_of_commute hdiam h0 hcu with hadj | h3
  · rw [natCard_centralizer_eq_inf] at hcard
    have e : Subgroup.centralizer {(y : Shat)} ⊓ vStab cv0 = vStab cv0 ⊓ vStab u := by
      rw [inf_comm]
      congr 1
      ext s
      rw [hu, Subgroup.mem_centralizer_singleton_iff, ← commute_clabelS_iff_mem u s]
      exact Iff.rfl
    rw [e, natCard_vStab_inf_of_adj hadj] at hcard
    norm_num at hcard
  · have h3' := rankS_cV0_mul_clabelS (mem_sphereDistThree.2 h3)
    rw [hu] at hc hr
    rw [h3'] at hc
    omega

theorem h2C_rank_2048
    {y : vStab cv0} (hy : orderOf y = 2) (hr : rankS (y : Shat) = 2048)
    (hc : rankS (y : Shat) = rankS ((cV0 : Shat) * y)) : False := by
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  rcases natCard_centralizer_of_rkH_2048 hy2 hr with ⟨h1, -⟩ | ⟨h1, -⟩
  · have h1' : rankS ((cV0 : Shat) * y) = 1860 := h1
    omega
  · have h1' : rankS ((cV0 : Shat) * y) = 2168 := h1
    omega

theorem h2C_rank_2158
    {y : vStab cv0} (hy : orderOf y = 2)
    (hcard : Nat.card (Subgroup.centralizer {y}) = 13244506413465600)
    (hr : rankS (y : Shat) = 2158) (hc : rankS (y : Shat) = rankS ((cV0 : Shat) * y)) : False := by
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  obtain ⟨p, q, hpq, hyl⟩ := exists_eq_clabelS_mul_of_rank_2158 (orderOf_coe_of_rank_2158 hy2 hr) hr
  have hcom : Commute (clabelS p * clabelS q) (clabelS cv0) := by
    rw [← hyl]
    exact (commute_clabelS_iff_mem cv0 _).2 y.2
  have hcomm : Commute (clabelS p) (clabelS q) :=
    ((labelsInput_of_ambient ambientRootOrbitsHyp) p q hpq).2.2.2.symm
  rcases position_of_rank_2158 hpq (hyl ▸ hr) hcom with rfl | rfl | ⟨hap, -⟩ | ⟨haq, -⟩
  · have e : (cV0 : Shat) * y = clabelS q := by
      rw [hyl, coe_cV0, ← mul_assoc, clabelS_mul_self', one_mul]
    rw [e, rankS_clabelS] at hc
    omega
  · have e : (cV0 : Shat) * y = clabelS p := by
      rw [hyl, coe_cV0, hcomm.eq, ← mul_assoc, clabelS_mul_self', one_mul]
    rw [e, rankS_clabelS] at hc
    omega
  · exact false_of_mixed_rank_2158 hpq hyl hap hcard
  · have hpq' : cgraph.dist q p = 3 := by rw [SimpleGraph.dist_comm]; exact hpq
    exact false_of_mixed_rank_2158 hpq' (hyl.trans hcomm.eq) haq hcard

theorem h2C_rank_2168
    {y : vStab cv0} (hy : orderOf y = 2)
    (hcard : Nat.card (Subgroup.centralizer {y}) = 13244506413465600)
    (hr : rankS (y : Shat) = 2168) : False := by
  have hyo : orderOf (sEquiv.symm (y : Shat)) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy]
  apply not_dvd_17_natCard_centralizer_of_rank_2168 hyo hr
  have e : Nat.card (Subgroup.centralizer {sEquiv.symm (y : Shat)}) =
      Nat.card (Subgroup.centralizer {(y : Shat)}) := by
    rw [Nat.card_congr (centralizerEquiv sEquiv (sEquiv.symm (y : Shat))).toEquiv,
      MulEquiv.apply_symm_apply]
  rw [e]
  have h1 : Nat.card (Subgroup.centralizer {y}) ∣ Nat.card (Subgroup.centralizer {(y : Shat)}) := by
    rw [natCard_centralizer_eq_inf]
    exact Subgroup.card_dvd_of_le inf_le_left
  rw [hcard] at h1
  exact (show 17 ∣ 13244506413465600 by norm_num).trans h1

theorem h2C_native :
    ∀ y : vStab cv0, orderOf y = 2 →
    Nat.card (Subgroup.centralizer {y}) = 13244506413465600 → ¬ IsConj y (cV0 * y) := by
  intro y hy hcard hconj
  have hyo : orderOf (y : Shat) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hc : rankS (y : Shat) = rankS ((cV0 : Shat) * y) := by
    have h := rankS_conj ((vStab cv0).subtype.map_isConj hconj)
    simpa using h
  rcases rankS_mem_of_orderOf hyo with h | h | h | h
  · exact h2C_rank_1860 hy hcard h hc
  · exact h2C_rank_2048 hy h hc
  · exact h2C_rank_2158 hy hcard h hc
  · exact h2C_rank_2168 hy hcard h

theorem conjugatesOf_inter_range_native
    {G : Type*} [Group G] {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a) :
    conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d :=
  conjugatesOf_inter_range_of_psi hd ψ hψ Φ hΦ h2C_native

end CFSG.Monster.B.GSide
