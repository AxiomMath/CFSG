module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryFix
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.FrameRoute.UnitaryModel

open CFSG.Assembly CFSG.SeitzReduction.UnitaryPilot CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K] {d : ℕ}

private lemma suBlock_eq_map (hK : Nat.card K = 4) {I : Finset (Fin d)} (hd1 : 1 ≤ d) :
    suBlock hK I = (blockSU (⟨Nat.prime_two, le_rfl, hK⟩ : UnitaryFieldData 2 1 K) I).map
      (unitaryPSUEquiv ⟨Nat.prime_two, le_rfl, hK⟩ hd1).toMonoidHom := by
  rw [suBlock, blockSU, Subgroup.map_map]
  congr 1

private noncomputable def suBlockEquiv (hK : Nat.card K = 4) {I : Finset (Fin d)}
    (hId : I.card < d) :
    ↥(blockSU (⟨Nat.prime_two, le_rfl, hK⟩ : UnitaryFieldData 2 1 K) I) ≃* ↥(suBlock hK I) := by
  have hd1 : 1 ≤ d := by omega
  exact (Subgroup.equivMapOfInjective (blockSU _ I) (unitaryPSUEquiv _ hd1).toMonoidHom
    (unitaryPSUEquiv _ hd1).injective).trans
      (MulEquiv.subgroupCongr (suBlock_eq_map hK hd1).symm)

theorem isQuasisimple_suBlock (hK : Nat.card K = 4) {I : Finset (Fin d)} (h4 : 4 ≤ I.card)
    (hId : I.card < d) : CFSG.IsQuasisimple ↥(suBlock hK I) := by
  exact CFSG.IsQuasisimple.of_mulEquiv (suBlockEquiv hK hId).symm
    (isQuasisimple_blockSU (⟨Nat.prime_two, le_rfl, hK⟩ : UnitaryFieldData 2 1 K) h4 hId)

private noncomputable def suBlockCenterQuotEquiv (hK : Nat.card K = 4) {I : Finset (Fin d)}
    (h1 : 1 ≤ I.card) (hId : I.card < d) :
    ↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin I.card) K 2) := by
  let h' : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, hK⟩
  have hd1 : 1 ≤ d := by omega
  let e := suBlockEquiv hK hId
  let eQ := QuotientGroup.congr _ _ e.symm
    (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e.symm)
  exact eQ.trans ((blockSUQuotientCenterEquiv h' hId).trans (unitaryPSUEquiv h' h1))

theorem nonempty_centerQuot_suBlock (hK : Nat.card K = 4) {I : Finset (Fin d)}
    (h1 : 1 ≤ I.card) (hId : I.card < d) :
    Nonempty (↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin I.card) K 2)) := by
  exact ⟨suBlockCenterQuotEquiv hK h1 hId⟩

theorem largeEvenMarking_suBlock (hK : Nat.card K = 4) {I : Finset (Fin d)} {m : ℕ}
    (hm : I.card = m + 1) (h3 : 3 ≤ m) (hId : I.card < d) :
    CFSG.StandardType.LargeEvenMarking ↥(suBlock hK I)
      fun lab _ _ _ _ _ => lab = ⟨.twA, m, 1⟩ := by
  have h4 : 4 ≤ I.card := by omega
  have h1 : 1 ≤ I.card := by omega
  have hQ := isQuasisimple_suBlock hK h4 hId
  have hComm : commutator ↥(suBlock hK I) = ⊤ := hQ.1.commutator_eq_top
  refine ⟨hComm, ⟨⟨.twA, m, 1⟩, ?_, ?_⟩⟩
  · simp [LargeEvenInLambda2]
    omega
  · simp only [LargeEvenRawDatumLegacy]
    refine ⟨K, inferInstance, ?_, ?_, ?_⟩
    · exact Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    · simpa using hK
    · have hNonempty : Nonempty (↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I) ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K 2)) := by
        rw [← hm]
        exact nonempty_centerQuot_suBlock hK h1 hId
      obtain ⟨θ⟩ := hNonempty
      have hSimple : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K 2)) := by
        let : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
        let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 hK (m + 1)
          (by omega)
          (by intro h; have := congrArg Prod.fst h; simp at this; omega)
      refine ⟨hSimple, ?hNoncomm, ?hTheta⟩
      ·
        have hPerfQuot : Group.IsPerfect
            (↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I)) := by
          let : Group.IsPerfect ↥(suBlock hK I) := hQ.1
          exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _)
            (QuotientGroup.mk'_surjective _)
        have hPerfR : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K 2)) := by
          let : Group.IsPerfect (↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I)) := hPerfQuot
          exact Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective
        have hnc : ¬ IsMulCommutative
            (LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K 2)) := by
          let : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K 2)) := hPerfR
          let : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K 2)) := hSimple
          let : Nontrivial (LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K 2)) :=
            IsSimpleGroup.toNontrivial
          exact Group.IsPerfect.not_isMulCommutative
            (G := LargeEvenProj (LargeEvenSUGroup (Fin (m + 1)) K 2))
        rw [isMulCommutative_iff] at hnc
        push Not at hnc
        exact hnc
      ·
        exact ⟨θ, trivial⟩

private def orderPSU (n : ℕ) : ℕ :=
  2 ^ (n * (n - 1) / 2) *
    ((Finset.Icc 2 n).prod fun i => ((2 : ℤ) ^ i - (-1) ^ i).toNat) / Nat.gcd n 3

private lemma f_two : ((2 : ℤ) ^ 2 - (-1) ^ 2).toNat = 3 := by norm_num

private lemma f_three : ((2 : ℤ) ^ 3 - (-1) ^ 3).toNat = 9 := by norm_num

private lemma f_four : ((2 : ℤ) ^ 4 - (-1) ^ 4).toNat = 15 := by norm_num

private lemma f_five : ((2 : ℤ) ^ 5 - (-1) ^ 5).toNat = 33 := by norm_num

private lemma f_pos {i : ℕ} (hi : 2 ≤ i) :
    0 < ((2 : ℤ) ^ i - (-1) ^ i).toNat := by
  rw [← Int.pos_iff_toNat_pos]
  have h2 : (4 : ℤ) ≤ (2 : ℤ) ^ i := by
    calc (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
      _ ≤ (2 : ℤ) ^ i := pow_le_pow_right₀ (by norm_num) hi
  have h1 : (-1 : ℤ) ^ i ≤ 1 := by
    rcases neg_one_pow_eq_or ℤ i with h | h
    · norm_num [h]
    · norm_num [h]
  linarith

private lemma P_pos (k : ℕ) :
    0 < ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat :=
  Finset.prod_pos fun i hi => f_pos (i := i) (Finset.mem_Icc.mp hi).1

private lemma dvd_P_two {k : ℕ} (hk : 2 ≤ k) :
    3 ∣ ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat := by
  have hsub : ({2} : Finset ℕ) ⊆ Finset.Icc 2 k := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
  have h := Finset.prod_dvd_prod_of_subset ({2} : Finset ℕ) (Finset.Icc 2 k)
    (fun i => ((2 : ℤ) ^ i - (-1) ^ i).toNat) hsub
  have hsmall : (∏ i ∈ ({2} : Finset ℕ), ((2 : ℤ) ^ i - (-1) ^ i).toNat) = 3 := by
    simp
  rwa [hsmall] at h

private lemma dvd_P_three {k : ℕ} (hk : 3 ≤ k) :
    (27 : ℕ) ∣ ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat := by
  have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 k := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    · exact Finset.mem_Icc.mpr ⟨by norm_num, hk⟩
  have h := Finset.prod_dvd_prod_of_subset ({2, 3} : Finset ℕ) (Finset.Icc 2 k)
    (fun i => ((2 : ℤ) ^ i - (-1) ^ i).toNat) hsub
  have hsmall : (∏ i ∈ ({2, 3} : Finset ℕ),
      ((2 : ℤ) ^ i - (-1) ^ i).toNat) = 27 := by
    rw [Finset.prod_insert (by norm_num : (2 : ℕ) ∉ ({3} : Finset ℕ)),
      Finset.prod_singleton, f_two, f_three]
    norm_num
  rwa [hsmall] at h

private lemma dvd_P_five {k : ℕ} (hk : 5 ≤ k) :
    (13365 : ℕ) ∣ ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat := by
  have hsub : ({2, 3, 4, 5} : Finset ℕ) ⊆ Finset.Icc 2 k := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    · exact Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩
    · exact Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩
    · exact Finset.mem_Icc.mpr ⟨by norm_num, hk⟩
  have h := Finset.prod_dvd_prod_of_subset ({2, 3, 4, 5} : Finset ℕ) (Finset.Icc 2 k)
    (fun i => ((2 : ℤ) ^ i - (-1) ^ i).toNat) hsub
  have hsmall : (∏ i ∈ ({2, 3, 4, 5} : Finset ℕ),
      ((2 : ℤ) ^ i - (-1) ^ i).toNat) = 13365 := by
    rw [Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num),
      Finset.prod_insert (by norm_num), Finset.prod_singleton,
      f_two, f_three, f_four, f_five]
    norm_num
  rwa [hsmall] at h

private lemma lt_orderPSU {k : ℕ} (hk : 5 ≤ k) : 25920 < orderPSU k := by
  have hgpos : 0 < Nat.gcd k 3 := Nat.gcd_pos_of_pos_right k (by norm_num)
  have hgle : Nat.gcd k 3 ≤ 3 := Nat.gcd_le_right k (by norm_num)
  have h10 : 10 ≤ k * (k - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have hmul : 20 ≤ k * (k - 1) := by
      have h := Nat.mul_le_mul hk (show 4 ≤ k - 1 by omega)
      simpa using h
    simpa using hmul
  have hpow : 2 ^ 10 ≤ 2 ^ (k * (k - 1) / 2) :=
    Nat.pow_le_pow_right (by norm_num) h10
  have hPpos : 0 < ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat :=
    P_pos k
  have hP : (13365 : ℕ) ≤
      ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat :=
    Nat.le_of_dvd hPpos (dvd_P_five hk)
  have hN : 25921 * Nat.gcd k 3 ≤
      2 ^ (k * (k - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat := by
    calc 25921 * Nat.gcd k 3 ≤ 25921 * 3 := Nat.mul_le_mul_left 25921 hgle
      _ ≤ 2 ^ (k * (k - 1) / 2) *
          ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat := by
        have h1 : 25921 * 3 ≤ 2 ^ 10 * 13365 := by norm_num
        exact le_trans h1 (Nat.mul_le_mul hpow hP)
  unfold orderPSU
  have hle : 25921 ≤
      (2 ^ (k * (k - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat) / Nat.gcd k 3 :=
    (Nat.le_div_iff_mul_le hgpos).mpr hN
  exact lt_of_lt_of_le (by norm_num) hle

private lemma three_dvd_orderPSU {k : ℕ} (hk : 2 ≤ k) : 3 ∣ orderPSU k := by
  have hN : Nat.gcd k 3 * 3 ∣
      2 ^ (k * (k - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat := by
    rcases eq_or_lt_of_le hk with hk2 | hk3
    · obtain rfl : k = 2 := hk2.symm
      have hP : (3 : ℕ) ∣ ∏ i ∈ Finset.Icc 2 2,
          ((2 : ℤ) ^ i - (-1) ^ i).toNat := dvd_P_two le_rfl
      have hPN : (∏ i ∈ Finset.Icc 2 2, ((2 : ℤ) ^ i - (-1) ^ i).toNat) ∣
          2 ^ 1 * ∏ i ∈ Finset.Icc 2 2, ((2 : ℤ) ^ i - (-1) ^ i).toNat :=
        Nat.dvd_mul_left _ _
      have hg : Nat.gcd 2 3 = 1 := by norm_num
      have hexp : 2 * (2 - 1) / 2 = 1 := by norm_num
      rw [hg, hexp]
      exact dvd_trans hP hPN
    · have h3 : 3 ≤ k := hk3
      have h9 : Nat.gcd k 3 * 3 ∣ 9 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_right k 3) with hg | hg
        · norm_num [hg]
        · norm_num [hg]
      have h9P : (9 : ℕ) ∣
          ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat :=
        dvd_trans (by norm_num : (9 : ℕ) ∣ 27) (dvd_P_three h3)
      have h9N : (9 : ℕ) ∣ 2 ^ (k * (k - 1) / 2) *
          ∏ i ∈ Finset.Icc 2 k, ((2 : ℤ) ^ i - (-1) ^ i).toNat :=
        dvd_trans h9P (Nat.dvd_mul_left _ _)
      exact dvd_trans h9 h9N
  unfold orderPSU
  exact Nat.dvd_div_of_mul_dvd hN

private lemma card_centerQuot_suBlock_eq (hK : Nat.card K = 4) {I : Finset (Fin d)}
    (h2 : 2 ≤ I.card) (hId : I.card < d) :
    Nat.card (↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I)) = orderPSU I.card := by
  rw [Nat.card_congr (suBlockCenterQuotEquiv hK (by omega) hId).toEquiv,
    largeEvenProj_eq_statedProj, largeEvenSUGroup_eq_statedSU, show (2 : ℕ) = 2 ^ 1 by norm_num,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl hK h2]
  simp only [pow_one, Nat.reduceAdd]
  rfl

theorem lt_card_centerQuot_suBlock (hK : Nat.card K = 4) {I : Finset (Fin d)} (h5 : 5 ≤ I.card)
    (hId : I.card < d) : 25920 < Nat.card (↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I)) := by
  rw [card_centerQuot_suBlock_eq hK (by omega) hId]
  exact lt_orderPSU h5

theorem three_dvd_card_centerQuot_suBlock (hK : Nat.card K = 4) {I : Finset (Fin d)}
    (h2 : 2 ≤ I.card) (hId : I.card < d) :
    3 ∣ Nat.card (↥(suBlock hK I) ⧸ Subgroup.center ↥(suBlock hK I)) := by
  rw [card_centerQuot_suBlock_eq hK h2 hId]
  exact three_dvd_orderPSU h2

end CFSG.StandardType.FrameRoute.UnitaryModel
