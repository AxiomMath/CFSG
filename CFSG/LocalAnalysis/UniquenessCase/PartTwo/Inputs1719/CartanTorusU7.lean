module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U7KFacts
import CFSG.ClassicalGroups.UnitaryFlag.SplitTorus
import CFSG.GroupTheory.TwoPowOrderFactorization
import CFSG.HardMathSupport.Timmesfeld.LinearRank.GLValuation
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcULevi
import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.UnitaryBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Curtis.UnitaryLevi
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem card_hypSU_three_one {f : ℕ} {L : Type} [Field L] (h : UnitaryFieldData 2 f L) :
    Nat.card (hypSU h 3 1) = (2 ^ f) ^ 21 *
      (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1) *
        (((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 5 + 1) * ((2 ^ f) ^ 7 + 1))) := by
  haveI : Finite L := h.finite
  rw [CFSG.LocalAnalysis.RankFourTheoremC.CrossExcU.crossExcU_card_hypSU_nat h
    (ε := 1) (by norm_num) (by norm_num)]
  have hIcc : Finset.Icc 2 7 = {2, 3, 4, 5, 6, 7} := by decide
  unfold CFSG.LocalAnalysis.RankFourTheoremC.CrossExcU.crossExcUOddProd
  rw [hIcc]
  have h3 : Finset.range 3 = {0, 1, 2} := by decide
  rw [h3]
  norm_num
  ring

private theorem factorization_pow_sub_one_u7 {f r j : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hq1 : 1 < 2 ^ f) (hrd : r ∣ 2 ^ f - 1) (hj : j ≠ 0) (hnj : ¬ r ∣ j) :
    ((2 ^ f) ^ j - 1).factorization r = (2 ^ f - 1).factorization r := by
  rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hr hr2 hq1 hrd hj,
    Nat.factorization_eq_zero_of_not_dvd hnj, add_zero]

private theorem factorization_card_hypSU_three_one {f : ℕ} {L : Type} [Field L]
    (h : UnitaryFieldData 2 f L) {r : ℕ} (hr : r.Prime) (hq : 1 < 2 ^ f)
    (hrd : r ∣ 2 ^ f - 1) (hr5 : 5 ≤ r) :
    (Nat.card (hypSU h 3 1)).factorization r = 3 * (2 ^ f - 1).factorization r := by
  have hr2 : r ≠ 2 := by omega
  have hq0 : 2 ^ f ≠ 0 := by omega
  have hmod : 2 ^ f ≡ 1 [MOD r] := by
    have h1 : 2 ^ f % r = 1 := by
      have hqeq : 2 ^ f = (2 ^ f - 1) + 1 := by omega
      rw [hqeq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hrd]
      simp [Nat.mod_eq_of_lt hr.one_lt]
    rw [Nat.ModEq, h1, Nat.mod_eq_of_lt hr.one_lt]
  have hqfac : (2 ^ f).factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (CFSG.GroupTheory.not_dvd_of_modEq_one_of_prime hr hmod)
  have hnot : ∀ j ∈ ({2, 4, 6} : Finset ℕ), ¬ r ∣ j := by
    intro j hj hdvd
    have := Nat.le_of_dvd (by simp at hj; omega) hdvd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · omega
    · omega
    · have h6 : r ∣ 2 * 3 := by simpa using hdvd
      rcases (Nat.Prime.dvd_mul hr).1 h6 with h' | h'
      · exact absurd (Nat.le_of_dvd (by norm_num) h') (by omega)
      · exact absurd (Nat.le_of_dvd (by norm_num) h') (by omega)
  have hsub : ∀ j : ℕ, j ≠ 0 → (2 ^ f) ^ j - 1 ≠ 0 := fun j hj => by
    have := Nat.one_lt_pow hj hq
    omega
  have h2 := factorization_pow_sub_one_u7 hr hr2 hq hrd (j := 2) (by norm_num)
    (hnot 2 (by simp))
  have h4 := factorization_pow_sub_one_u7 hr hr2 hq hrd (j := 4) (by norm_num)
    (hnot 4 (by simp))
  have h6 := factorization_pow_sub_one_u7 hr hr2 hq hrd (j := 6) (by norm_num)
    (hnot 6 (by simp))
  have ho3 := CFSG.GroupTheory.factorization_pow_add_one_eq_zero (k := 3) hr hr2 hmod
  have ho5 := CFSG.GroupTheory.factorization_pow_add_one_eq_zero (k := 5) hr hr2 hmod
  have ho7 := CFSG.GroupTheory.factorization_pow_add_one_eq_zero (k := 7) hr hr2 hmod
  have hq21 : ((2 ^ f) ^ 21).factorization r = 0 := by
    rw [Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul, hqfac, mul_zero]
  rw [card_hypSU_three_one h]
  have n2 := hsub 2 (by norm_num)
  have n4 := hsub 4 (by norm_num)
  have n6 := hsub 6 (by norm_num)
  have p3 : (2 ^ f) ^ 3 + 1 ≠ 0 := by positivity
  have p5 : (2 ^ f) ^ 5 + 1 ≠ 0 := by positivity
  have p7 : (2 ^ f) ^ 7 + 1 ≠ 0 := by positivity
  simp only [Nat.factorization_mul, Nat.factorization_mul (pow_ne_zero _ hq0)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero n2 n4) n6) (mul_ne_zero (mul_ne_zero p3 p5) p7)),
    Nat.factorization_mul (mul_ne_zero (mul_ne_zero n2 n4) n6)
      (mul_ne_zero (mul_ne_zero p3 p5) p7),
    Nat.factorization_mul (mul_ne_zero n2 n4) n6, Nat.factorization_mul n2 n4,
    Nat.factorization_mul (mul_ne_zero p3 p5) p7, Nat.factorization_mul p3 p5,
    Finsupp.add_apply, hq21, h2, h4, h6, ho3, ho5, ho7]
  ring

private theorem factorization_card_cover_u7 {f : ℕ} {L : Type} [Field L] [Finite L]
    (h : UnitaryFieldData 2 f L) {K : Type} [Group K] [Finite K]
    {r : ℕ} (hr : r.Prime) (hq1 : 1 < 2 ^ f) (hrd : r ∣ 2 ^ f - 1) (hr5 : 5 ≤ r)
    (α : hypSU h 3 1 →* K) (hα : Function.Surjective α)
    (hker : ∀ s, α s = 1 → s ∈ hypScalars h 3 1) :
    (Nat.card K).factorization r = 3 * (2 ^ f - 1).factorization r := by
  have hfacS := factorization_card_hypSU_three_one (L := L) h hr hq1 hrd hr5
  have hZcard : Nat.card (hypScalars h 3 1) = Nat.gcd 7 (2 ^ f + 1) := by
    have := card_hypScalars (p := 2) (f := f) (K := L) (r := 3) (ε := 1) h (by norm_num)
    simpa using this
  have hkerdvd : Nat.card α.ker ∣ Nat.card (hypScalars h 3 1) := Subgroup.card_dvd_of_le hker
  have hrker : ¬ r ∣ Nat.card α.ker := by
    intro hd
    have hd7 : r ∣ Nat.gcd 7 (2 ^ f + 1) := by
      rw [← hZcard]
      exact dvd_trans hd hkerdvd
    have hrq : r ∣ 2 ^ f + 1 := (Nat.dvd_gcd_iff.mp hd7).2
    have h2 : r ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hrq hrd
    rw [show (2 ^ f + 1) - (2 ^ f - 1) = 2 by omega] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hmul := Subgroup.card_ker_mul_card_of_surjective hα
  have hkerfac : (Nat.card α.ker).factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hrker
  have hmain := congrArg (fun n : ℕ => n.factorization r) hmul
  have hk0 : Nat.card α.ker ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_mul hk0 hK0, Finsupp.add_apply, hkerfac, zero_add] at hmain
  rw [hmain, hfacS]

private theorem exists_split_torus_u7 {f r : ℕ} {L : Type} [Field L] [Finite L]
    (h : UnitaryFieldData 2 f L) (hf1 : 1 ≤ f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrd : r ∣ 2 ^ f - 1) :
    ∃ (μ : Subgroup Lˣ) (hμ : SplitInv h μ),
      Nat.card μ = r ^ (2 ^ f - 1).factorization r ∧ Odd (Nat.card μ) := by
  have hr2 : r ≠ 2 := by omega
  have hq1 : 1 < 2 ^ f := by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hqsub : 2 ^ f - 1 ≠ 0 := by omega
  set a : ℕ := (2 ^ f - 1).factorization r with ha
  have hdvd : r ^ a ∣ 2 ^ f - 1 := by
    rw [ha]
    exact (hr.pow_dvd_iff_le_factorization hqsub).2 le_rfl
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact (hr.dvd_iff_one_le_factorization hqsub).1 hrd
  have hdvdq : r ^ a ∣ Nat.card L - 1 := by
    rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq (2 ^ f) 1, one_pow]
    rw [hsq]
    exact dvd_mul_of_dvd_left hdvd _
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (L := L) hdvdq
  refine ⟨Subgroup.zpowers ζ, ?_, ?_, ?_⟩
  · exact splitInv_zpowers h (d := r ^ a) (Nat.one_lt_pow (by omega) hr.one_lt)
      (by rw [← hζ]; exact pow_orderOf_eq_one ζ) hdvd
  · rw [Nat.card_zpowers, hζ]
  · rw [Nat.card_zpowers, hζ]
    exact (hr.odd_of_ne_two hr2).pow

private theorem exists_comm_subgroup_u7
    {K : Type} [Group K] [Finite K] {f r : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible .PSU 7 2 f)
    (hL : LieModel (K ⧸ Subgroup.center K) .PSU 7 2 f)
    (hqs : CFSG.Open.IsQuasisimple K) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrd : r ∣ 2 ^ f - 1) :
    ∃ H : Subgroup K, IsMulCommutative H ∧
      Nat.card H = r ^ (Nat.card K).factorization r := by
  have hf1 : 1 ≤ f := hadm.2.1
  have hf2 : 2 ≤ f := by
    rcases Nat.lt_or_ge f 2 with h | h
    · have hf1' : f = 1 := by omega
      rw [hf1'] at hrd
      norm_num at hrd
      exact absurd hrd hr.ne_one
    · exact h
  obtain ⟨L, hFld, hFin, h, ⟨e⟩⟩ :=
    uc22pwliu_exists_hypPSU (Y := K ⧸ Subgroup.center K) (n := f) (r := 3) (ε := 1)
      (by omega) (by norm_num) hL
  letI : Field L := hFld
  letI : Finite L := hFin
  haveI : CharP L 2 := h.charP
  obtain ⟨α, hα, hker, -⟩ :=
    uc22pwliu_exists_cover (K := L) h (r := 3) (ε := 1) (by norm_num) (by norm_num) hf2 hqs e
  obtain ⟨μ, hμ, hcardμ, hoddμ⟩ := exists_split_torus_u7 h hf1 hr hr5 hrd
  let D : Subgroup (hypSU h 3 1) := (splitTorusHom h 3 1 μ hμ).range
  have hDab : IsMulCommutative D := splitTorusHom_range_comm hμ
  have hcardDmap : Nat.card (D.map α) = r ^ (3 * (2 ^ f - 1).factorization r) := by
    have hcardmap := splitTorusHom_range_map_card (r := 3) (ε := 1) hμ hoddμ α hker
    change Nat.card ((splitTorusHom h 3 1 μ hμ).range.map α) =
      r ^ (3 * (2 ^ f - 1).factorization r)
    rw [hcardmap, hcardμ, ← pow_mul]
    congr 1
    ring
  have hq1 : 1 < 2 ^ f := by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hfacK : (Nat.card K).factorization r = 3 * (2 ^ f - 1).factorization r :=
    factorization_card_cover_u7 (L := L) h hr hq1 hrd hr5 α hα hker
  refine ⟨D.map α, ?_, ?_⟩
  · haveI : IsMulCommutative D := hDab
    exact Subgroup.map_isMulCommutative (H := D) (f := α)
  · rw [hcardDmap, hfacK]

theorem k_U7CartanSylowAbelian_holds :
    K_U7CartanSylowAbelian := by
  intro K _ _ f r hadm hL hqs _ hr hr7 hrd P
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨H, hHab, hHcard⟩ := exists_comm_subgroup_u7 hadm hL hqs hr (by omega) hrd
  let P0 : Sylow r K := Sylow.ofCard H hHcard
  have hP0 : (P0 : Subgroup K) = H := Sylow.coe_ofCard _ _
  haveI : Finite (Sylow r K) :=
    Finite.of_injective (fun Q : Sylow r K => (Q : Subgroup K)) (fun Q R h => Sylow.ext h)
  haveI : MulAction.IsPretransitive K (Sylow r K) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P0 P
  rw [← hg, Sylow.coe_subgroup_smul, hP0]
  change IsMulCommutative (H.map (MulAut.conj g).toMonoidHom)
  haveI : IsMulCommutative H := hHab
  exact Subgroup.map_isMulCommutative (H := H) (f := (MulAut.conj g).toMonoidHom)

variable {f : ℕ} {L : Type} [Field L]

open Matrix

private def u7θ : HypIndex 1 0 → HypIndex 3 1 :=
  hypMap (fun _ : Fin 1 => (2 : Fin 3)) (fun k : Fin 0 => k.elim0)

private theorem u7θ_injective : Function.Injective u7θ :=
  hypMap_injective (fun _ _ _ => Subsingleton.elim _ _) (fun k => k.elim0)

private theorem u7θ_partner (x : HypIndex 1 0) :
    u7θ (hypPartner x) = hypPartner (u7θ x) :=
  hypMap_partner _ _ x

private noncomputable def u7D (h : UnitaryFieldData 2 f L) : Lˣ →* hypSU h 3 1 :=
  torusHomOfRatio h 3 1 (invPairParams (0 : Fin 3) (1 : Fin 3))
    (fun t => torusRatio_invPairParams h (i := 0) (j := 1) (by decide) t)

private theorem coe_u7D (h : UnitaryFieldData 2 f L) (t : Lˣ) :
    (((u7D h t : hypSU h 3 1) : GL (HypIndex 3 1) L) :
      Matrix (HypIndex 3 1) (HypIndex 3 1) L) =
      diagonal (torusEntries h (invPairParams (0 : Fin 3) (1 : Fin 3) t)
        (1 : Fin 1 → Lˣ)) :=
  coe_torusHomOfRatio t

private noncomputable def u7E (h : UnitaryFieldData 2 f L) (μ : Subgroup Lˣ)
    (hμ : SplitInv h μ) : (Fin 2 → μ) →* hypSU h 3 1 :=
  (splitTorusHom h 3 1 μ hμ).comp
    (Function.ExtendByOne.hom μ (Fin.castSucc : Fin 2 → Fin 3))

private theorem coe_u7E (h : UnitaryFieldData 2 f L) {μ : Subgroup Lˣ}
    (hμ : SplitInv h μ) (x : Fin 2 → μ) :
    (((u7E h μ hμ x : hypSU h 3 1) : GL (HypIndex 3 1) L) :
      Matrix (HypIndex 3 1) (HypIndex 3 1) L) =
      diagonal (torusEntries h
        (fun i => ((Function.ExtendByOne.hom μ (Fin.castSucc : Fin 2 → Fin 3)) x i : Lˣ))
        (1 : Fin 1 → Lˣ)) := by
  rw [u7E]
  exact coe_splitTorusHom hμ _

private theorem u7E_extend_apply_last {μ : Subgroup Lˣ} (x : Fin 2 → μ) :
    Function.ExtendByOne.hom μ (Fin.castSucc : Fin 2 → Fin 3) x 2 = 1 := by
  rw [show Function.ExtendByOne.hom μ (Fin.castSucc : Fin 2 → Fin 3) x 2 =
      Function.extend (Fin.castSucc : Fin 2 → Fin 3) x 1 2 from rfl]
  exact Function.extend_apply' _ _ _ (by
    rintro ⟨i, hi⟩
    have h := congrArg Fin.val hi
    simp at h
    omega)

private theorem u7E_entries_eq_one (h : UnitaryFieldData 2 f L) {μ : Subgroup Lˣ}
    (x : Fin 2 → μ) :
    ∀ k : HypIndex 1 0,
      torusEntries h
        (fun i => ((Function.ExtendByOne.hom μ (Fin.castSucc : Fin 2 → Fin 3)) x i : Lˣ))
        (1 : Fin 1 → Lˣ) (u7θ k) = 1 := by
  intro k
  rcases k with i | k | i
  · change torusEntries h
      (fun i => ((Function.ExtendByOne.hom μ (Fin.castSucc : Fin 2 → Fin 3)) x i : Lˣ))
      (1 : Fin 1 → Lˣ) (Sum.inl (2 : Fin 3)) = 1
    simp [torusEntries, u7E_extend_apply_last]
  · exact k.elim0
  · change torusEntries h
      (fun i => ((Function.ExtendByOne.hom μ (Fin.castSucc : Fin 2 → Fin 3)) x i : Lˣ))
      (1 : Fin 1 → Lˣ) (Sum.inr (Sum.inr (2 : Fin 3))) = 1
    simp [torusEntries, u7E_extend_apply_last]

private theorem u7D_entries_eq_one (h : UnitaryFieldData 2 f L) (t : Lˣ) :
    ∀ k : HypIndex 1 0,
      torusEntries h (invPairParams (0 : Fin 3) (1 : Fin 3) t) (1 : Fin 1 → Lˣ)
        (u7θ k) = 1 := by
  intro k
  rcases k with i | k | i
  · change torusEntries h (invPairParams (0 : Fin 3) (1 : Fin 3) t) (1 : Fin 1 → Lˣ)
      (Sum.inl (2 : Fin 3)) = 1
    simp [torusEntries, invPairParams_apply_of_ne (i := (0 : Fin 3)) (j := (1 : Fin 3))
      (k := (2 : Fin 3)) (by decide) (by decide)]
  · exact k.elim0
  · change torusEntries h (invPairParams (0 : Fin 3) (1 : Fin 3) t) (1 : Fin 1 → Lˣ)
      (Sum.inr (Sum.inr (2 : Fin 3))) = 1
    simp [torusEntries, invPairParams_apply_of_ne (i := (0 : Fin 3)) (j := (1 : Fin 3))
      (k := (2 : Fin 3)) (by decide) (by decide)]

private noncomputable def u7X (h : UnitaryFieldData 2 f L) : hypSU h 1 0 →* hypSU h 3 1 :=
  extHyp h u7θ u7θ_injective u7θ_partner

private theorem coe_u7X (h : UnitaryFieldData 2 f L) (y : hypSU h 1 0) :
    (((u7X h y : hypSU h 3 1) : GL (HypIndex 3 1) L) :
      Matrix (HypIndex 3 1) (HypIndex 3 1) L) =
      extId u7θ u7θ_injective
        ((y : GL (HypIndex 1 0) L) : Matrix (HypIndex 1 0) (HypIndex 1 0) L) :=
  coe_extHyp ..

private theorem commute_u7E_u7D (h : UnitaryFieldData 2 f L) {μ : Subgroup Lˣ}
    (hμ : SplitInv h μ) (x : Fin 2 → μ) (t : Lˣ) :
    Commute (u7E h μ hμ x) (u7D h t) := by
  apply hypSU_commute_of_matrix_comm
  rw [coe_u7E, coe_u7D, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

private theorem commute_u7E_u7X (h : UnitaryFieldData 2 f L) {μ : Subgroup Lˣ}
    (hμ : SplitInv h μ) (x : Fin 2 → μ) (y : hypSU h 1 0) :
    Commute (u7E h μ hμ x) (u7X h y) := by
  apply hypSU_commute_of_matrix_comm
  rw [coe_u7E, coe_u7X]
  exact (extId_mul_diagonal_of_eq_one_on_range u7θ u7θ_injective _ _
    (u7E_entries_eq_one h x)).symm

private theorem commute_u7D_u7X (h : UnitaryFieldData 2 f L) (t : Lˣ)
    (y : hypSU h 1 0) : Commute (u7D h t) (u7X h y) := by
  apply hypSU_commute_of_matrix_comm
  rw [coe_u7D, coe_u7X]
  exact (extId_mul_diagonal_of_eq_one_on_range u7θ u7θ_injective _ _
    (u7D_entries_eq_one h t)).symm

private noncomputable def u7β (h : UnitaryFieldData 2 f L) :
    (Lˣ × hypSU h 1 0) →* hypSU h 3 1 :=
  MonoidHom.noncommCoprod (u7D h) (u7X h) fun t y => commute_u7D_u7X h t y

@[simp] private theorem u7β_apply (h : UnitaryFieldData 2 f L)
    (x : Lˣ × hypSU h 1 0) : u7β h x = u7D h x.1 * u7X h x.2 :=
  MonoidHom.noncommCoprod_apply ..

private theorem commute_u7D_mul_u7X_u7E (h : UnitaryFieldData 2 f L) {μ : Subgroup Lˣ}
    (hμ : SplitInv h μ) (t : Lˣ) (y : hypSU h 1 0) (x : Fin 2 → μ) :
    Commute (u7D h t * u7X h y) (u7E h μ hμ x) := by
  have h1 : Commute (u7D h t) (u7E h μ hμ x) := (commute_u7E_u7D h hμ x t).symm
  have h2 : Commute (u7X h y) (u7E h μ hμ x) := (commute_u7E_u7X h hμ x y).symm
  exact h1.mul_left h2

private theorem u7θ_not_mem_inl {n : Fin 3} (hn : n ≠ 2) :
    (Sum.inl n : HypIndex 3 1) ∉ Set.range u7θ := by
  rintro ⟨i, hi⟩
  rcases i with i | k | i
  · have h : (2 : Fin 3) = n := by simpa [u7θ, hypMap] using hi
    exact hn h.symm
  · exact k.elim0
  · simp [u7θ, hypMap] at hi

private theorem u7D_mul_u7X_apply_inl_zero (h : UnitaryFieldData 2 f L) (t : Lˣ)
    (y : hypSU h 1 0) :
    (((u7D h t * u7X h y : hypSU h 3 1) : GL (HypIndex 3 1) L) :
      Matrix (HypIndex 3 1) (HypIndex 3 1) L) (Sum.inl (0 : Fin 3)) (Sum.inl 0) = (t : L) := by
  rw [Subgroup.coe_mul, Units.val_mul, coe_u7D, coe_u7X, Matrix.diagonal_mul,
    extId_apply_of_not_left u7θ u7θ_injective _ (u7θ_not_mem_inl (by decide))
      (Sum.inl (0 : Fin 3))]
  simp [torusEntries, invPairParams_apply_left (i := (0 : Fin 3)) (j := (1 : Fin 3))
    (by decide)]

private theorem u7D_mul_u7X_apply_inl_one (h : UnitaryFieldData 2 f L) (t : Lˣ)
    (y : hypSU h 1 0) :
    (((u7D h t * u7X h y : hypSU h 3 1) : GL (HypIndex 3 1) L) :
      Matrix (HypIndex 3 1) (HypIndex 3 1) L) (Sum.inl (1 : Fin 3)) (Sum.inl 1) =
        ((t⁻¹ : Lˣ) : L) := by
  rw [Subgroup.coe_mul, Units.val_mul, coe_u7D, coe_u7X, Matrix.diagonal_mul,
    extId_apply_of_not_left u7θ u7θ_injective _ (u7θ_not_mem_inl (by decide))
      (Sum.inl (1 : Fin 3))]
  simp [torusEntries, invPairParams_apply_right (i := (0 : Fin 3)) (j := (1 : Fin 3))
    (by decide)]

private theorem u7_torus_eq_inv_of_scalar (h : UnitaryFieldData 2 f L) (t : Lˣ)
    (y : hypSU h 1 0) {c : L}
    (hc : (((u7D h t * u7X h y : hypSU h 3 1) : GL (HypIndex 3 1) L) :
      Matrix (HypIndex 3 1) (HypIndex 3 1) L) = Matrix.scalar (HypIndex 3 1) c) :
    t = t⁻¹ ∧ (t : L) = c := by
  have h1 : (t : L) = c := by
    calc (t : L)
        = (((u7D h t * u7X h y : hypSU h 3 1) : GL (HypIndex 3 1) L) :
            Matrix (HypIndex 3 1) (HypIndex 3 1) L) (Sum.inl 0) (Sum.inl 0) :=
          (u7D_mul_u7X_apply_inl_zero h t y).symm
      _ = c := by rw [hc]; simp [Matrix.scalar_apply]
  have h2 : ((t⁻¹ : Lˣ) : L) = c := by
    calc ((t⁻¹ : Lˣ) : L)
        = (((u7D h t * u7X h y : hypSU h 3 1) : GL (HypIndex 3 1) L) :
            Matrix (HypIndex 3 1) (HypIndex 3 1) L) (Sum.inl 1) (Sum.inl 1) :=
          (u7D_mul_u7X_apply_inl_one h t y).symm
      _ = c := by rw [hc]; simp [Matrix.scalar_apply]
  exact ⟨Units.ext (h1.trans h2.symm), h1⟩

private theorem u7_injective_on_A (h : UnitaryFieldData 2 f L) {K : Type} [Group K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (α : hypSU h 3 1 →* K) (hker : ∀ s, α s = 1 → s ∈ hypScalars h 3 1)
    {t₀ : Lˣ} {y₀ : hypSU h 1 0} (ht₀ : orderOf t₀ = p) :
    Function.Injective ((α.comp (u7β h)).comp
      ((Subgroup.zpowers t₀).prod (Subgroup.zpowers y₀)).subtype) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have htmem : (a : Lˣ × hypSU h 1 0).1 ∈ Subgroup.zpowers t₀ :=
    (Subgroup.mem_prod.mp a.2).1
  have hα1 : α (u7D h a.1.1 * u7X h a.1.2) = 1 := by
    rw [← u7β_apply h]
    exact ha
  have hscal : u7D h a.1.1 * u7X h a.1.2 ∈ hypScalars h 3 1 := hker _ hα1
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hscal
  have hmat : (((u7D h a.1.1 * u7X h a.1.2 : hypSU h 3 1) : GL (HypIndex 3 1) L) :
      Matrix (HypIndex 3 1) (HypIndex 3 1) L) = Matrix.scalar (HypIndex 3 1) (c : L) := by
    have := congrArg (fun g : GL (HypIndex 3 1) L =>
      ((g : Matrix (HypIndex 3 1) (HypIndex 3 1) L))) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using this
  obtain ⟨ht_eq, htval⟩ := u7_torus_eq_inv_of_scalar h a.1.1 a.1.2 hmat
  have ht2 : (a : Lˣ × hypSU h 1 0).1 ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [ht_eq]
    exact mul_inv_cancel _
  have hordp : orderOf ((a : Lˣ × hypSU h 1 0).1) ∣ p :=
    (orderOf_dvd_of_mem_zpowers htmem).trans (by rw [ht₀])
  have hord2 : orderOf ((a : Lˣ × hypSU h 1 0).1) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one ht2
  have hoddp : Odd p := hp.odd_of_ne_two hp2
  have hgcd : Nat.gcd p 2 = 1 := by
    have h2dvd : Nat.gcd p 2 ∣ 2 := Nat.gcd_dvd_right p 2
    rcases (Nat.dvd_prime Nat.prime_two).1 h2dvd with hg | hg
    · exact hg
    · exact absurd (by rw [← hg]; exact Nat.gcd_dvd_left p 2) hoddp.not_two_dvd_nat
  have htone : (a : Lˣ × hypSU h 1 0).1 = 1 := by
    have hdvd : orderOf ((a : Lˣ × hypSU h 1 0).1) ∣ Nat.gcd p 2 := Nat.dvd_gcd hordp hord2
    rw [hgcd] at hdvd
    rw [← orderOf_eq_one_iff]
    exact Nat.dvd_one.1 hdvd
  have hc1 : (c : L) = 1 := by rw [← htval, htone]; rfl
  have hprod : u7D h a.1.1 * u7X h a.1.2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_one, Units.val_one, hmat, hc1, Matrix.scalar_apply, Matrix.diagonal_one]
  have hX : u7X h a.1.2 = 1 := by
    have hD : u7D h a.1.1 = 1 := by rw [htone, map_one]
    calc u7X h a.1.2 = 1 * u7X h a.1.2 := (one_mul _).symm
      _ = u7D h a.1.1 * u7X h a.1.2 := by rw [hD]
      _ = 1 := hprod
  have hyone : (a : Lˣ × hypSU h 1 0).2 = 1 :=
    extHyp_injective h u7θ u7θ_injective u7θ_partner (by simpa [u7X] using hX)
  exact Subtype.ext (Prod.ext htone hyone)

private theorem u7_exists_E (h : UnitaryFieldData 2 f L) {μ : Subgroup Lˣ}
    (hμ : SplitInv h μ) {K : Type} [Group K] {r : ℕ}
    (hoddμ : Odd (Nat.card μ)) (hcardμ : Nat.card μ = r)
    (α : hypSU h 3 1 →* K) (hker : ∀ s, α s = 1 → s ∈ hypScalars h 3 1) :
    IsElemAbelian r ((α.comp (u7E h μ hμ)).range) ∧
      Nat.card ((α.comp (u7E h μ hμ)).range) = r ^ 2 := by
  have hinj : Function.Injective (α.comp (u7E h μ hμ)) := by
    have h1 : Function.Injective (α.comp (splitTorusHom h 3 1 μ hμ)) :=
      splitTorusHom_comp_injective hμ hoddμ α hker
    exact h1.comp (Function.extend_injective (Fin.castSucc_injective 2) 1)
  refine ⟨⟨IsMulCommutative.of_comm ?_, ?_⟩, ?_⟩
  · intro a b
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    exact mul_comm' x y
  · intro z hz
    obtain ⟨x, rfl⟩ := hz
    have hx : x ^ r = 1 := by
      funext i
      rw [Pi.pow_apply, ← hcardμ]
      exact pow_card_eq_one'
    rw [← map_pow, hx, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun, hcardμ]
    norm_num

private theorem exists_order_p_elements_u7 (h : UnitaryFieldData 2 f L) [Finite L]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpdvd : p ∣ 2 ^ f + 1) :
    ∃ (t₀ : Lˣ) (y₀ : hypSU h 1 0), orderOf t₀ = p ∧ orderOf y₀ = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpunits : p ∣ Nat.card Lˣ := by
    rw [Nat.card_units, h.card, show 2 * f = f * 2 by ring, pow_mul]
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq (2 ^ f) 1, one_pow]
    rw [hsq]
    exact dvd_mul_of_dvd_right hpdvd _
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := Lˣ) p hpunits
  have hpy : p ∣ Nat.card (hypSU h 1 0) := by
    rw [CFSG.LocalAnalysis.RankFourTheoremC.CrossExcU.crossExcU_card_hypSU_nat h
      (r := 1) (ε := 0) (by norm_num) (by norm_num)]
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq (2 ^ f) 1, one_pow]
    have hoddprod : CFSG.LocalAnalysis.RankFourTheoremC.CrossExcU.crossExcUOddProd
        (2 ^ f) 2 = 1 := by
      simp [CFSG.LocalAnalysis.RankFourTheoremC.CrossExcU.crossExcUOddProd]
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, Finset.range_one,
      Finset.prod_singleton, pow_one, mul_one]
    rw [hoddprod, mul_one, hsq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpdvd _) _
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := hypSU h 1 0) p hpy
  exact ⟨t₀, y₀, ht₀, hy₀⟩

private theorem card_comm_pow_prod_zpowers_u7 {h : UnitaryFieldData 2 f L} {p : ℕ}
    {t₀ : Lˣ} {y₀ : hypSU h 1 0} (ht₀ : orderOf t₀ = p) (hy₀ : orderOf y₀ = p) :
    Nat.card ((Subgroup.zpowers t₀).prod (Subgroup.zpowers y₀)) = p ^ 2 ∧
      (∀ a b : (Subgroup.zpowers t₀).prod (Subgroup.zpowers y₀), a * b = b * a) ∧
      ∀ a : (Subgroup.zpowers t₀).prod (Subgroup.zpowers y₀), a ^ p = 1 := by
  have hcard : Nat.card ((Subgroup.zpowers t₀).prod (Subgroup.zpowers y₀)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.prodEquiv (Subgroup.zpowers t₀)
      (Subgroup.zpowers y₀)).toEquiv, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers,
      ht₀, hy₀, pow_two]
  have hcomm : ∀ a b : (Subgroup.zpowers t₀).prod (Subgroup.zpowers y₀), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Prod.ext
    · change (a : Lˣ × hypSU h 1 0).1 * (b : Lˣ × hypSU h 1 0).1 =
        (b : Lˣ × hypSU h 1 0).1 * (a : Lˣ × hypSU h 1 0).1
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_prod.mp a.2).1
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_prod.mp b.2).1
      rw [← hm, ← hn, zpow_mul_comm]
    · change (a : Lˣ × hypSU h 1 0).2 * (b : Lˣ × hypSU h 1 0).2 =
        (b : Lˣ × hypSU h 1 0).2 * (a : Lˣ × hypSU h 1 0).2
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_prod.mp a.2).2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_prod.mp b.2).2
      rw [← hm, ← hn, zpow_mul_comm]
  have hpow : ∀ a : (Subgroup.zpowers t₀).prod (Subgroup.zpowers y₀), a ^ p = 1 := by
    intro a
    apply Subtype.ext
    apply Prod.ext
    · change (a : Lˣ × hypSU h 1 0).1 ^ p = (1 : Lˣ)
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact (orderOf_dvd_of_mem_zpowers (Subgroup.mem_prod.mp a.2).1).trans (by rw [ht₀])
    · change (a : Lˣ × hypSU h 1 0).2 ^ p = (1 : hypSU h 1 0)
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact (orderOf_dvd_of_mem_zpowers (Subgroup.mem_prod.mp a.2).2).trans (by rw [hy₀])
  exact ⟨hcard, hcomm, hpow⟩

private theorem u7_pRank_centralizer (h : UnitaryFieldData 2 f L) [Finite L]
    {μ : Subgroup Lˣ} (hμ : SplitInv h μ) {K : Type} [Group K] [Finite K]
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpdvd : p ∣ 2 ^ f + 1)
    (α : hypSU h 3 1 →* K) (hker : ∀ s, α s = 1 → s ∈ hypScalars h 3 1)
    (hcardμ : Nat.card μ = r) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Subgroup.centralizer
      (((α.comp (u7E h μ hμ)).range : Subgroup K) : Set K))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t₀, y₀, ht₀, hy₀⟩ := exists_order_p_elements_u7 h hp hp2 hpdvd
  let A : Subgroup (Lˣ × hypSU h 1 0) := (Subgroup.zpowers t₀).prod (Subgroup.zpowers y₀)
  have hA := card_comm_pow_prod_zpowers_u7 (h := h) ht₀ hy₀
  let F : A →* Subgroup.centralizer
      (((α.comp (u7E h μ hμ)).range : Subgroup K) : Set K) :=
    MonoidHom.codRestrict ((α.comp (u7β h)).comp A.subtype) _
      fun a => by
        rw [Subgroup.mem_centralizer_iff]
        rintro z ⟨x, rfl⟩
        have hc := (commute_u7D_mul_u7X_u7E h hμ a.1.1 a.1.2 x).map α
        change (α.comp (u7E h μ hμ)) x * (α.comp (u7β h)) (a : Lˣ × hypSU h 1 0) =
          (α.comp (u7β h)) (a : Lˣ × hypSU h 1 0) * (α.comp (u7E h μ hμ)) x
        simp only [MonoidHom.comp_apply, u7β_apply]
        exact hc.eq.symm
  have hFinj : Function.Injective F := fun a b hab =>
    u7_injective_on_A h hp hp2 α hker ht₀ (Subtype.ext_iff.mp hab)
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt hA.2.1 hA.2.2 hA.1 F hFinj le_top

theorem k_U7CentTorus_holds :
    K_U7CentTorus := by
  intro K _ _ f p r hadm hL hqs _ hp hp2 hpdvd hr hr7 hrd
  have hf1 : 1 ≤ f := hadm.2.1
  have hf2 : 2 ≤ f := by
    rcases Nat.lt_or_ge f 2 with h | h
    · have hf1' : f = 1 := by omega
      rw [hf1'] at hrd
      norm_num at hrd
      exact absurd hrd hr.ne_one
    · exact h
  obtain ⟨L, hFld, hFin, h, ⟨e⟩⟩ :=
    uc22pwliu_exists_hypPSU (Y := K ⧸ Subgroup.center K) (n := f) (r := 3) (ε := 1)
      (by omega) (by norm_num) hL
  letI : Field L := hFld
  letI : Finite L := hFin
  haveI : CharP L 2 := h.charP
  obtain ⟨α, -, hker, -⟩ :=
    uc22pwliu_exists_cover (K := L) h (r := 3) (ε := 1) (by norm_num) (by norm_num) hf2 hqs e
  have hdvdq : r ∣ Nat.card L - 1 := by
    rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
    have hsq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq (2 ^ f) 1, one_pow]
    rw [hsq]
    exact dvd_mul_of_dvd_left hrd _
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (L := L) hdvdq
  let μ : Subgroup Lˣ := Subgroup.zpowers ζ
  have hcardμ : Nat.card μ = r := by
    rw [show μ = Subgroup.zpowers ζ from rfl, Nat.card_zpowers, hζ]
  have hoddμ : Odd (Nat.card μ) := by
    rw [hcardμ]
    exact hr.odd_of_ne_two (by omega : r ≠ 2)
  have hsplit : SplitInv h μ := by
    rw [show μ = Subgroup.zpowers ζ from rfl]
    exact splitInv_zpowers h (d := r) hr.one_lt
      (by rw [← hζ]; exact pow_orderOf_eq_one ζ) hrd
  obtain ⟨hEA, hcardE⟩ := u7_exists_E h hsplit hoddμ hcardμ α hker
  exact ⟨(α.comp (u7E h μ hsplit)).range, hEA, hcardE,
    u7_pRank_centralizer h hsplit hp hp2 hpdvd α hker hcardμ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
