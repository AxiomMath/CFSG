module

public import CFSG.RankThree.PartOne.F106.NoQD32NADegForm
public import CFSG.RankThree.PartOne.F106.NoQD32NADispLift
public import CFSG.RankThree.PartOne.F106.QD32Class
public import CFSG.RankThree.PartOne.N143.Weyl613Small
public import CFSG.RankThree.PartOne.N143.Statements

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.N143
  CFSG.RankThree.PartOne.N143X
open scoped commutatorElement

theorem seven_le_of_prime_ne {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq5 : q ≠ 5) :
    7 ≤ q := by
  have h2 := hq.two_le
  by_contra hlt
  interval_cases q <;> first | omega | (exfalso; norm_num at hq)

theorem not_pow_five_dvd_card_gl_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {n : ℕ} (hn : n = 6 ∨ n = 7) : ¬ 3 ^ 5 ∣ Nat.card (GL (Fin n) K) := by
  have : Fintype K := Fintype.ofFinite K
  have h2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [Matrix.card_GL_field, h2]
  rcases hn with rfl | rfl
  · rw [Fin.prod_univ_six]
    decide
  · rw [Fin.prod_univ_seven]
    decide

theorem false_psl_nonab {T : Type} [Group T] {n f : ℕ}
    (hn : n ≤ 5 ∨ ((n = 6 ∨ n = 7) ∧ f = 1)) (hmod : StatedClassicalModel T .PSL n 2 f) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5) (h33 : ¬ (q = 3 ∧ n = 3)) {Y : Subgroup T}
    (hexp : ∀ y ∈ Y, y ^ q = 1) (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card hK
  have hqK : (q : K) ≠ 0 := natCast_ne_zero_of_prime_ne_two hq hq2
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  rcases hn with hn5 | ⟨hn67, rfl⟩
  · obtain ⟨F, -, hF1, hF2, hFc⟩ := exists_lift_nonab (StatedSL n K) e hq (d := n)
      (fun c hc => pow_eq_one_of_scalar_det (det_eq_one_of_mem_statedSL' hc))
      (not_dvd_small hq hq2 hq5 h33 hn2 hn5) hexp hcl
    have := na_deg hq hq2 hqK F hF1 hF2 (by rw [hFc]; exact h4)
    simp only [Fintype.card_fin] at this
    omega
  · have hK2 : Nat.card K = 2 := by simpa using hK
    obtain ⟨F, -, hF1, hF2, hFc⟩ := exists_lift_nonab (StatedSL n K) e hq (d := 1)
      (scalar_pow_one_of_card_two hK2 _) hq.not_dvd_one hexp hcl
    by_cases hq3' : q = 3
    · subst hq3'
      have hF1' : ∀ x : ↥F, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hF1 x x.2)
      have h5 := pow_five_dvd_card hq hF1' (by rw [hFc]; exact h4)
      exact not_pow_five_dvd_card_gl_two hK2 hn67 (h5.trans (Subgroup.card_subgroup_dvd_card F))
    · have h7 := seven_le_of_prime_ne hq hq2 hq3' hq5
      have := na_deg hq hq2 hqK F hF1 hF2 (by rw [hFc]; exact h4)
      simp only [Fintype.card_fin] at this
      omega

theorem false_psu_nonab {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 5 ∨ (n = 6 ∧ f = 1))
    (hmod : StatedClassicalModel T .PSU n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq5 : q ≠ 5) (h33 : ¬ (q = 3 ∧ (n = 3 ∨ n = 6))) {Y : Subgroup T}
    (hexp : ∀ y ∈ Y, y ^ q = 1) (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn3 : 3 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card (g := 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  have hqK : (q : K) ≠ 0 := natCast_ne_zero_of_prime_ne_two hq hq2
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  rcases hn with hn5 | ⟨rfl, rfl⟩
  · obtain ⟨F, -, hF1, hF2, hFc⟩ := exists_lift_nonab (StatedSU n (2 ^ f) K) e hq (d := n)
      (fun c hc => pow_eq_one_of_scalar_det (det_eq_one_of_mem_statedSU' hc))
      (not_dvd_small hq hq2 hq5 (fun h3 => h33 ⟨h3.1, Or.inl h3.2⟩) (by omega) hn5) hexp hcl
    have := na_deg hq hq2 hqK F hF1 hF2 (by rw [hFc]; exact h4)
    simp only [Fintype.card_fin] at this
    omega
  · have hq6 : ¬ q ∣ 6 := by
      intro hdvd
      have hle : q ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      have h2 := hq.two_le
      interval_cases q <;> first | omega | (exfalso; norm_num at hq)
    obtain ⟨F, -, hF1, hF2, hFc⟩ := exists_lift_nonab (StatedSU 6 (2 ^ 1) K) e hq (d := 6)
      (fun c hc => pow_eq_one_of_scalar_det (det_eq_one_of_mem_statedSU' hc)) hq6 hexp hcl
    have := na_deg hq hq2 hqK F hF1 hF2 (by rw [hFc]; exact h4)
    simp only [Fintype.card_fin] at this
    omega

theorem false_psp_nonab {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .PSp n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card hK
  have hqK : (q : K) ≠ 0 := natCast_ne_zero_of_prime_ne_two hq hq2
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n K →
      c ^ 2 = 1 := by
    intro c hc
    have hJ := statedSp_le_isoGroup n K hc
    rw [mem_isoGroup] at hJ
    have h := congrFun (congrFun hJ (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
    simpa [symJ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.fromBlocks, Fintype.sum_sum_type] using h
  obtain ⟨F, hFM, hF1, hF2, hFc⟩ := exists_lift_nonab (StatedSp n K) e hq hd
    (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)) hexp hcl
  have := na_deg_form hq hq2 hqK F hF1 hF2 (by rw [hFc]; exact h4) (symJ n K)
    (symJ_det_ne_zero n K) (fun y hy => mem_isoGroup.1 (statedSp_le_isoGroup n K (hFM hy)))
  simp only [Fintype.card_sum, Fintype.card_fin] at this
  omega

theorem false_pomegaPlus_nonab {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .POmegaPlus n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn4 : 4 ≤ n := hadm.2.2
  have : CharP K 2 := charP_two_of_card hK
  have hqK : (q : K) ≠ 0 := natCast_ne_zero_of_prime_ne_two hq hq2
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈
      StatedOmega (StatedQuadPlus n K) → c ^ 2 = 1 := fun c hc =>
    sq_eq_one_of_scalar_mem_isoQ (quadPlus_smul n) (quadPlus_one n (by omega))
      (statedOmega_le_isoQ _ hc)
  obtain ⟨F, hFM, hF1, hF2, hFc⟩ := exists_lift_nonab (StatedOmega (StatedQuadPlus n K)) e hq hd
    (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)) hexp hcl
  have := na_deg_form hq hq2 hqK F hF1 hF2 (by rw [hFc]; exact h4) (plusJ n K)
    (plusJ_det_ne_zero n) (fun y hy => transpose_mul_eq_of_isoQ (quadPlus_polar n)
      (statedOmega_le_isoQ _ (hFM hy)))
  simp only [Fintype.card_sum, Fintype.card_fin] at this
  omega

theorem false_pomegaMinus_nonab {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .POmegaMinus n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hmod
  have hn4 : 4 ≤ n := hadm.2.2
  have hchar : CharP K 2 := charP_two_of_card hK
  have hqK : (q : K) ≠ 0 := natCast_ne_zero_of_prime_ne_two hq hq2
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
    apply hbc s
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [hb0, hs]
    linear_combination (s * s) * h2
  have hd : ∀ d : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) d ∈
      StatedOmega (StatedQuadMinus n K b c) → d ^ 2 = 1 := fun d hd =>
    sq_eq_one_of_scalar_mem_isoQ (quadMinus_smul n b c) (quadMinus_one n b c (by omega))
      (statedOmega_le_isoQ _ hd)
  obtain ⟨F, hFM, hF1, hF2, hFc⟩ := exists_lift_nonab (StatedOmega (StatedQuadMinus n K b c)) e hq
    hd (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)) hexp hcl
  have := na_deg_form hq hq2 hqK F hF1 hF2 (by rw [hFc]; exact h4) (quadMinusJ n b)
    (quadMinusJ_det_ne_zero n hb) (fun y hy => transpose_mul_eq_of_isoQ (quadMinus_polar n b c)
      (statedOmega_le_isoQ _ (hFM hy)))
  simp only [Fintype.card_sum, Fintype.card_fin] at this
  omega

theorem false_suzuki_nonab {T : Type} [Group T] {f : ℕ} (hmod : SuzukiModel T 2 f) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {Y : Subgroup T} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hmod
  have : CharP K 2 := charP_two_of_card hK
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  let ψ : T →* GL (Fin 4) K := (suzukiGroup a K).subtype.comp e.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.injective
  obtain ⟨F, hF1, hF2, hFc⟩ := exists_embed_nonab ψ hψ hexp hcl
  have := na_deg hq hq2 (natCast_ne_zero_of_prime_ne_two hq hq2) F hF1 hF2 (by rw [hFc]; exact h4)
  simp only [Fintype.card_fin] at this
  omega

theorem false_classical_nonab_ne3 {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (_hadm : StatedLieAdmissible t n 2 f) (hLie : LieModel X t n 2 f)
    (hsmall : SmallEvenParams t n f)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .twistedB2)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5)
    (hexc : ¬ (q = 3 ∧ ((t = .PSL ∧ n = 3) ∨ (t = .PSU ∧ (n = 3 ∨ n = 6)))))
    {Y : Subgroup X} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hLie with ⟨-, hmod⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact false_psl_nonab hsmall hmod hq hq2 hq5 (fun h => hexc ⟨h.1, Or.inl ⟨rfl, h.2⟩⟩)
        hexp hcl h4
    all_goals exact absurd ht' (by decide)
  · rcases hLie with ⟨-, hmod⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact false_psu_nonab hsmall hmod hq hq2 hq5 (fun h => hexc ⟨h.1, Or.inr ⟨rfl, h.2⟩⟩)
        hexp hcl h4
    all_goals exact absurd ht' (by decide)
  · rcases hLie with ⟨-, hmod⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact false_psp_nonab hsmall hmod hq hq2 hexp hcl h4
    all_goals exact absurd ht' (by decide)
  · rcases hLie with ⟨-, hmod⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact false_pomegaPlus_nonab hsmall hmod hq hq2 hexp hcl h4
    all_goals exact absurd ht' (by decide)
  · rcases hLie with ⟨-, hmod⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact false_pomegaMinus_nonab hsmall hmod hq hq2 hexp hcl h4
    all_goals exact absurd ht' (by decide)
  · rcases hLie with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, hmod⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact false_suzuki_nonab hmod hq hq2 hexp hcl h4

end CFSG.RankThree.PartOne.F106
