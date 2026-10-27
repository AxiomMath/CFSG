module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Timmesfeld.Orders.Classical
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcClOrth
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverBridge
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.ClassicalGroups.Orthogonal.Models
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem w1369_sixteen_dvd_of_pow {a : ℕ} (ha : 4 ≤ a) : 16 ∣ 2 ^ a := by
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
  exact Nat.pow_dvd_pow 2 ha

private theorem w1369_ne_168_of_sixteen_dvd {N : ℕ} (h : 16 ∣ N) : N ≠ 168 := by
  intro hN
  rw [hN] at h
  norm_num at h

private theorem w1369_card_statedProj_statedOmega_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] (Q : (ι → K) → K) :
    Nat.card (StatedProj (StatedOmega Q)) ≤ Nat.card (CFSG.MatrixModel.isometryCore Q) := by
  have h1 : Nat.card (StatedProj (StatedOmega Q)) ≤ Nat.card (StatedOmega Q) := by
    unfold StatedProj
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have h2 : Nat.card (StatedOmega Q) ≤ Nat.card (CFSG.MatrixModel.isometryCore Q) :=
    Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_dvd_of_le (Subgroup.commutator_le_self (CFSG.MatrixModel.isometryCore Q)))
  exact le_trans h1 h2

private theorem w1369_card_statedSL_ne_168 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : m ≠ 3) : Nat.card (StatedSL m K) ≠ 168 := by
  rcases lt_or_gt_of_ne hm with hm3 | hm3
  · interval_cases m
    · have h1 : Nat.card (StatedSL 0 K) = 1 :=
        Nat.card_eq_one_iff_exists.mpr ⟨1, fun y => Subsingleton.elim y 1⟩
      rw [h1]; norm_num
    · have h1 : Nat.card (StatedSL 1 K) = 1 := by
        letI := Fintype.ofFinite K
        rw [CFSG.Open.StatedAPI.card_statedSL, Matrix.card_SL_field]
        have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
        rw [hq, show (2 : ℕ) - 1 = 1 by norm_num, Nat.div_one]
        simp
      rw [h1]; norm_num
    · rw [CFSG.Open.StatedAPI.card_statedSL_two, hK]; norm_num
  · have hm4 : 4 ≤ m := hm3
    have hprod : 2 ^ (m * (m - 1)) ≤ ∏ i : Fin m, (2 ^ m - 2 ^ (i : ℕ)) := by
      have h1 : ∀ i : Fin m, 2 ^ (m - 1) ≤ 2 ^ m - 2 ^ (i : ℕ) := by
        intro i
        have hi : (i : ℕ) ≤ m - 1 := Nat.le_sub_one_of_lt i.2
        have hpow : 2 ^ (i : ℕ) ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) hi
        have hsplit : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
          have h2 : 2 ^ m = 2 ^ (m - 1) * 2 := by
            rw [← pow_succ]
            congr 1
            omega
          rw [h2, Nat.mul_two]
        have hsum : 2 ^ (m - 1) + 2 ^ (i : ℕ) ≤ 2 ^ m := by
          rw [hsplit]
          exact Nat.add_le_add_left hpow _
        omega
      have := Finset.pow_card_le_prod (Finset.univ : Finset (Fin m))
        (fun i : Fin m => 2 ^ m - 2 ^ (i : ℕ)) (2 ^ (m - 1)) (fun i _ => h1 i)
      simpa [Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm] using this
    have hcard : Nat.card (StatedSL m K) = ∏ i : Fin m, (2 ^ m - 2 ^ (i : ℕ)) := by
      rw [CFSG.Open.StatedAPI.card_statedSL]
      letI := Fintype.ofFinite K
      haveI : NeZero m := ⟨by omega⟩
      rw [Matrix.card_SL_field]
      have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
      rw [hq, show (2 : ℕ) - 1 = 1 by norm_num, Nat.div_one]
    rw [hcard]
    have h12 : 168 < 2 ^ (m * (m - 1)) := by
      have hm12 : 12 ≤ m * (m - 1) := by
        calc 12 = 4 * 3 := by norm_num
          _ ≤ m * (m - 1) := Nat.mul_le_mul hm4 (by omega)
      calc 168 < 2 ^ 12 := by norm_num
        _ ≤ 2 ^ (m * (m - 1)) := Nat.pow_le_pow_right (by norm_num) hm12
    exact ne_of_gt (lt_of_lt_of_le h12 hprod)

private theorem w1369_card_statedSp_ne_168 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (k : ℕ) : Nat.card (StatedSp k K) ≠ 168 := by
  rcases k with _ | _ | k
  · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
    simp
  · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
    norm_num
  · apply w1369_ne_168_of_sixteen_dvd
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
    have h4 : 4 ≤ (k + 2) ^ 2 := by
      calc 4 = 2 * 2 := by norm_num
        _ ≤ (k + 2) * (k + 2) := Nat.mul_le_mul (by omega) (by omega)
        _ = (k + 2) ^ 2 := by rw [pow_two]
    exact (w1369_sixteen_dvd_of_pow h4).trans (dvd_mul_right _ _)

private theorem w1369_card_alternatingGroup_ne_168 (n : ℕ) :
    Nat.card (alternatingGroup (Fin n)) ≠ 168 := by
  rcases n with _ | _ | n
  · have h1 : Nat.card (alternatingGroup (Fin 0)) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨1, fun y => Subsingleton.elim y 1⟩
    rw [h1]; norm_num
  · have h1 : Nat.card (alternatingGroup (Fin 1)) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨1, fun y => Subsingleton.elim y 1⟩
    rw [h1]; norm_num
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    intro h
    have h2 : (n + 2).factorial = 336 := by
      have h3 : 2 * ((n + 2).factorial / 2) = (n + 2).factorial :=
        Nat.mul_div_cancel' (Nat.dvd_factorial (by omega) (by omega))
      rw [h] at h3
      omega
    rcases le_or_gt (n + 2) 5 with hn | hn
    · have hle : (n + 2).factorial ≤ 120 := by
        have := Nat.factorial_le hn
        norm_num at this
        exact this
      omega
    · have hge : 720 ≤ (n + 2).factorial := by
        have := Nat.factorial_le (show 6 ≤ n + 2 by omega)
        norm_num at this
        exact this
      omega

private theorem w1369_quadMinus_one_ne_168 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (StatedProj (StatedOmega (StatedQuadMinus 1 K b c))) ≠ 168 := by
  haveI hchar : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by rw [hK, pow_one])
  have hle : Nat.card (StatedProj (StatedOmega (StatedQuadMinus 1 K b c))) ≤
      Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadMinus 1 K b c)) :=
    w1369_card_statedProj_statedOmega_le (StatedQuadMinus 1 K b c)
  have hcard : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadMinus 1 K b c)) = 6 := by
    have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (0 + 1) K b c)) : ℤ) =
        2 * (Nat.card K : ℤ) ^ (0 * (0 + 1)) * ((Nat.card K : ℤ) ^ (0 + 1) + 1) *
          ∏ i ∈ Finset.Icc 1 0, ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
      (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := K) 0 hirr).2
    have h := CFSG.LocalAnalysis.RankFourTheoremC.crossExcCl_card_isoMinus (K := K)
      (b := b) (c := c) (m := 0) hO
    rw [hK] at h
    norm_num at h
    simpa using h
  exact ne_of_lt (lt_of_le_of_lt (hle.trans (le_of_eq hcard)) (by norm_num))

private theorem w1369_card_statedProj_statedOmega_quadPlus_ne_168 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (k : ℕ) :
    Nat.card (StatedProj (StatedOmega (StatedQuadPlus k K))) ≠ 168 := by
  haveI hchar : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by rw [hK, pow_one])
  rcases k with _ | _ | _ | k
  · have h1 : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 0 K))) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨1, fun y => Subsingleton.elim y 1⟩
    rw [h1]; norm_num
  · have hle : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 1 K))) ≤
        Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 1 K)) :=
      w1369_card_statedProj_statedOmega_le (StatedQuadPlus 1 K)
    have hcard : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 1 K)) = 2 := by
      have h := CFSG.LocalAnalysis.RankFourTheoremC.crossExcCl_card_isoPlus (K := K) 0
      rw [hK] at h
      norm_num at h
      simpa using h
    exact ne_of_lt (lt_of_le_of_lt (hle.trans (le_of_eq hcard)) (by norm_num))
  · have hle : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 2 K))) ≤
        Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)) :=
      w1369_card_statedProj_statedOmega_le (StatedQuadPlus 2 K)
    have hcard : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)) = 72 := by
      have h := CFSG.LocalAnalysis.RankFourTheoremC.crossExcCl_card_isoPlus (K := K) 1
      rw [hK] at h
      norm_num at h
      simpa using h
    exact ne_of_lt (lt_of_le_of_lt (hle.trans (le_of_eq hcard)) (by norm_num))
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hv : ∃ v : Fin 3 ⊕ Fin 3 → K,
          CFSG.LieType.Universal.Spin.quadPlus 3 K v ≠ 0 := by
        refine ⟨(CFSG.ClassicalGroups.Orthogonal.plusPair K (⟨0, by norm_num⟩ : Fin 3)).e +
          (CFSG.ClassicalGroups.Orthogonal.plusPair K (⟨0, by norm_num⟩ : Fin 3)).f, ?_⟩
        rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair]
        exact one_ne_zero
      have h3 : Nat.card (StatedProj (StatedOmega (StatedQuadPlus 3 K))) = 20160 := by
        rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
          (CFSG.LieType.Universal.Spin.coe_quadPlus 3 K) hv]
        letI := Fintype.ofFinite K
        have hcardF : Fintype.card K = Fintype.card (ZMod 2) := by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK]; norm_num
        let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcardF
        rw [Nat.card_congr (CFSG.SeitzReduction.OmegaPilot.statedOmegaPlusCongr φ 3).toEquiv]
        exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.card_statedOmega_quadPlus_three
      rw [h3]; norm_num
    · apply w1369_ne_168_of_sixteen_dvd
      have hformula := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus
        (K := K) (n := k + 3) (by omega)
      rw [hK] at hformula
      have he : 4 ≤ (k + 3) * ((k + 3) - 1) := by
        calc 4 = 2 * 2 := by norm_num
          _ ≤ (k + 3) * ((k + 3) - 1) := Nat.mul_le_mul (by omega) (by omega)
      have hdvdZ : (16 : ℤ) ∣ (Nat.card
          (StatedProj (StatedOmega (StatedQuadPlus (k + 3) K))) : ℤ) := by
        rw [hformula, show (16 : ℤ) = 2 ^ 4 by norm_num]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow 2 he) _) _
      exact Int.ofNat_dvd.mp hdvdZ

private theorem w1369_card_statedProj_statedOmega_quadMinus_ne_168 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ) :
    Nat.card (StatedProj (StatedOmega (StatedQuadMinus k K b c))) ≠ 168 := by
  haveI hchar : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by rw [hK, pow_one])
  rcases k with _ | _ | _ | _ | k
  · change Nat.card (StatedProj (StatedOmega (StatedQuadMinus 1 K b c))) ≠ 168
    exact w1369_quadMinus_one_ne_168 hK hirr
  · exact w1369_quadMinus_one_ne_168 hK hirr
  · have hle : Nat.card (StatedProj (StatedOmega (StatedQuadMinus 2 K b c))) ≤
        Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) :=
      w1369_card_statedProj_statedOmega_le (StatedQuadMinus 2 K b c)
    have hcard : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) = 120 := by
      have hO := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := K) 1 hirr).2
      have h := CFSG.LocalAnalysis.RankFourTheoremC.crossExcCl_card_isoMinus (K := K)
        (b := b) (c := c) (m := 1) hO
      rw [hK] at h
      norm_num at h
      simpa using h
    exact ne_of_lt (lt_of_le_of_lt (hle.trans (le_of_eq hcard)) (by norm_num))
  · apply w1369_ne_168_of_sixteen_dvd
    have hv : ∃ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
        CFSG.LieType.Universal.Spin.quadMinus 3 K b c v ≠ 0 := by
      refine ⟨(CFSG.ClassicalGroups.Orthogonal.minusPair K b c
        (⟨0, by norm_num⟩ : Fin (3 - 1))).e +
        (CFSG.ClassicalGroups.Orthogonal.minusPair K b c
          (⟨0, by norm_num⟩ : Fin (3 - 1))).f, ?_⟩
      rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair]
      exact one_ne_zero
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
      (CFSG.LieType.Universal.Spin.coe_quadMinus 3 K b c) hv]
    obtain ⟨F, hFfield, hFfinite, hFcard, ⟨eF⟩⟩ :=
      CFSG.RankThree.GF2n.Stroth80.exists_statedOmega_quadMinus_three_mulEquiv
        (K := K) (b := b) (c := c) (f := 1) (by rw [hK]; norm_num) hirr
    letI := hFfield
    letI := hFfinite
    rw [Nat.card_congr eF.toEquiv]
    have hdvd : Nat.card (StatedProj (StatedSU 4 (2 ^ 1) F)) ∣
        Nat.card (StatedSU 4 (2 ^ 1) F) :=
      Subgroup.card_quotient_dvd_card _
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl
      hFcard (by norm_num : 2 ≤ 4)] at hdvd
    norm_num at hdvd
    exact (by norm_num : (16 : ℕ) ∣ 25920).trans hdvd
  · apply w1369_ne_168_of_sixteen_dvd
    have hformula := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus
      (K := K) (n := k + 4) (by omega) (b := b) (c := c) hirr
    rw [hK] at hformula
    have he : 4 ≤ (k + 4) * ((k + 4) - 1) := by
      calc 4 = 2 * 2 := by norm_num
        _ ≤ (k + 4) * ((k + 4) - 1) := Nat.mul_le_mul (by omega) (by omega)
    have hdvdZ : (16 : ℤ) ∣ (Nat.card
        (StatedProj (StatedOmega (StatedQuadMinus (k + 4) K b c))) : ℤ) := by
      rw [hformula, show (16 : ℤ) = 2 ^ 4 by norm_num]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow 2 he) _) _
    exact Int.ofNat_dvd.mp hdvdZ

theorem w1369_card_sl_eq_168 {X : Type} [Group X] {m : ℕ} (h : IsSLn X m 1)
    (hX : Nat.card X = 168) : m = 3 := by
  unfold IsSLn at h
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI := hKfield
  letI := hKfinite
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have hcard : Nat.card (StatedSL m K) = 168 :=
    (Nat.card_congr e.toEquiv).symm.trans hX
  by_contra hm
  exact w1369_card_statedSL_ne_168 hK2 hm hcard

theorem w1369_card_sp_ne_168 {X : Type} [Group X] {n : ℕ} (h : IsSpn X n 1) :
    Nat.card X ≠ 168 := by
  unfold IsSpn at h
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI := hKfield
  letI := hKfinite
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  rw [Nat.card_congr e.toEquiv]
  exact w1369_card_statedSp_ne_168 hK2 (n / 2)

theorem w1369_card_omegaPlus_ne_168 {X : Type} [Group X] {n : ℕ} (h : IsOmegaPlus X n 1) :
    Nat.card X ≠ 168 := by
  unfold IsOmegaPlus at h
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  letI := hKfield
  letI := hKfinite
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  rw [Nat.card_congr e.toEquiv]
  exact w1369_card_statedProj_statedOmega_quadPlus_ne_168 hK2 (n / 2)

theorem w1369_card_omegaMinus_ne_168 {X : Type} [Group X] {n : ℕ} (h : IsOmegaMinus X n 1) :
    Nat.card X ≠ 168 := by
  unfold IsOmegaMinus at h
  obtain ⟨-, K, hKfield, hKfinite, b, c, hKcard, hirr, ⟨e⟩⟩ := h
  letI := hKfield
  letI := hKfinite
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  rw [Nat.card_congr e.toEquiv]
  exact w1369_card_statedProj_statedOmega_quadMinus_ne_168 hK2 hirr (n / 2)

theorem w1369_card_alt_ne_168 {X : Type} [Group X] {n : ℕ} (h : IsAlt X n) :
    Nat.card X ≠ 168 := by
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt at h
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact w1369_card_alternatingGroup_ne_168 n

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
