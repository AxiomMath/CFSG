module

public import CFSG.LocalAnalysis.StandardType.GGTorsionExcDefs
public import CFSG.LocalAnalysis.StandardType.GGTorsionTwF4Card
public import CFSG.LocalAnalysis.StandardType.GGTorsionClassical
public import CFSG.LocalAnalysis.StandardType.GGTorsionOrders
import CFSG.LocalAnalysis.StandardType.GGExclNoIso

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionE67Basic

private theorem e67_shift_le (k : ℕ) {q : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) :
    q ^ (k - 1) ≤ q ^ k - 1 := by
  have h1 : 1 ≤ q ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
  have hqk : q ^ k = q ^ (k - 1) * q := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  have h2 : 2 * q ^ (k - 1) ≤ q ^ (k - 1) * q := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hq
  rw [hqk]
  omega

private theorem e67_not_three_dvd_two_pow (n : ℕ) : ¬ 3 ∣ 2 ^ n := by
  intro h
  have h2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
  norm_num at h2

private theorem e67_two_le_two_pow {n : ℕ} (hn : 1 ≤ n) : 2 ≤ 2 ^ n := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

private theorem e67_three_dvd_sq_sub_one {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun h => hq (h ▸ dvd_zero 3)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq1), Nat.cast_pow,
    Nat.cast_one, sub_eq_zero]
  have h0 : ((q : ℕ) : ZMod 3) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q 3).1 h)
  generalize ((q : ℕ) : ZMod 3) = z at h0 ⊢
  revert z
  decide

private theorem e67_three_dvd_ordE6 {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ CFSG.Open.ordE6 q := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun h => hq (h ▸ dvd_zero 3)
  have h2 : 3 ∣ q ^ 2 - 1 := e67_three_dvd_sq_sub_one hq
  have h6 : 3 ∣ q ^ 6 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 3
    rw [one_pow, ← pow_mul] at h
    exact h2.trans h
  have hnum : 9 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) := by
    have h9 : (9 : ℕ) = 3 * 3 := by norm_num
    rw [h9]
    exact Nat.mul_dvd_mul (Dvd.dvd.mul_right (Dvd.dvd.mul_left h6 _) _) h2
  have hg : Nat.gcd 3 (q - 1) = 1 ∨ Nat.gcd 3 (q - 1) = 3 :=
    (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three) _ (Nat.gcd_dvd_left 3 (q - 1))
  unfold CFSG.Open.ordE6
  obtain ⟨m, hm⟩ := hnum
  rw [hm]
  rcases hg with h | h
  · rw [h, Nat.div_one]
    exact Dvd.intro (3 * m) (by ring)
  · rw [h, show 9 * m = 3 * (3 * m) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact Dvd.intro m rfl

private theorem e67_three_dvd_ordTwistedE6 {q : ℕ} (hq : ¬ 3 ∣ q) :
    3 ∣ CFSG.Open.ordTwistedE6 q := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun h => hq (h ▸ dvd_zero 3)
  have h2 : 3 ∣ q ^ 2 - 1 := e67_three_dvd_sq_sub_one hq
  have h6 : 3 ∣ q ^ 6 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 3
    rw [one_pow, ← pow_mul] at h
    exact h2.trans h
  have hnum : 9 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) := by
    have h9 : (9 : ℕ) = 3 * 3 := by norm_num
    rw [h9]
    exact Nat.mul_dvd_mul (Dvd.dvd.mul_right (Dvd.dvd.mul_left h6 _) _) h2
  have hg : Nat.gcd 3 (q + 1) = 1 ∨ Nat.gcd 3 (q + 1) = 3 :=
    (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three) _ (Nat.gcd_dvd_left 3 (q + 1))
  unfold CFSG.Open.ordTwistedE6
  obtain ⟨m, hm⟩ := hnum
  rw [hm]
  rcases hg with h | h
  · rw [h, Nat.div_one]
    exact Dvd.intro (3 * m) (by ring)
  · rw [h, show 9 * m = 3 * (3 * m) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact Dvd.intro m rfl

private theorem e67_three_dvd_ordE7 {q : ℕ} (hq2 : 2 ∣ q) (hq3 : ¬ 3 ∣ q) :
    3 ∣ CFSG.Open.ordE7 q := by
  have h2 : 3 ∣ q ^ 2 - 1 := e67_three_dvd_sq_sub_one hq3
  have hF : 3 ∣ (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) :=
    h2.trans (dvd_mul_of_dvd_right (dvd_refl (q ^ 2 - 1))
      ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1)))
  have hnum : 3 ∣ q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) :=
    dvd_mul_of_dvd_right hF (q ^ 63)
  have h2q63 : 2 ∣ q ^ 63 := dvd_trans hq2 (dvd_pow_self q (by norm_num : 63 ≠ 0))
  have h2num : 2 ∣ q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) :=
    dvd_mul_of_dvd_left h2q63 _
  have hg : Nat.gcd 2 (q - 1) = 1 ∨ Nat.gcd 2 (q - 1) = 2 :=
    (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two) _ (Nat.gcd_dvd_left 2 (q - 1))
  unfold CFSG.Open.ordE7
  rw [show q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1) =
      q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1)) by ring]
  rcases hg with hg | hg
  · rw [hg, Nat.div_one]
    exact hnum
  · rw [hg]
    apply Nat.dvd_div_of_mul_dvd
    rw [show 2 * 3 = 6 by norm_num]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2num hnum

private theorem e67_pow70_le_ordE6 {q : ℕ} (hq : 2 ≤ q) : q ^ 70 ≤ CFSG.Open.ordE6 q := by
  have hq2 : 3 ≤ q ^ 2 := by
    calc 3 ≤ 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h12 : q ^ 11 ≤ q ^ 12 - 1 := e67_shift_le 12 hq (by norm_num)
  have h9 : q ^ 8 ≤ q ^ 9 - 1 := e67_shift_le 9 hq (by norm_num)
  have h8 : q ^ 7 ≤ q ^ 8 - 1 := e67_shift_le 8 hq (by norm_num)
  have h6 : q ^ 5 ≤ q ^ 6 - 1 := e67_shift_le 6 hq (by norm_num)
  have h5 : q ^ 4 ≤ q ^ 5 - 1 := e67_shift_le 5 hq (by norm_num)
  have h2 : q ^ 1 ≤ q ^ 2 - 1 := e67_shift_le 2 hq (by norm_num)
  have hF : q ^ 36 ≤ (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
      (Nat.mul_le_mul h12 h9) h8) h6) h5) h2
    calc q ^ 36 = q ^ 11 * q ^ 8 * q ^ 7 * q ^ 5 * q ^ 4 * q ^ 1 := by ring
      _ ≤ _ := h
  have h3F : 3 * q ^ 34 ≤ (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) := by
    refine le_trans ?_ hF
    calc 3 * q ^ 34 ≤ q ^ 2 * q ^ 34 := Nat.mul_le_mul_right _ hq2
      _ = q ^ 36 := by ring
  have hgpos : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [CFSG.Open.ordE6, Nat.le_div_iff_mul_le hgpos]
  rw [show q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
        (q ^ 2 - 1) =
      q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
        (q ^ 2 - 1)) by ring]
  calc q ^ 70 * Nat.gcd 3 (q - 1) ≤ q ^ 70 * 3 :=
        Nat.mul_le_mul_left _ (Nat.gcd_le_left (q - 1) (by norm_num))
    _ = q ^ 36 * (3 * q ^ 34) := by ring
    _ ≤ q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
        (q ^ 2 - 1)) := Nat.mul_le_mul_left _ h3F

private theorem e67_pow70_le_ordTwistedE6 {q : ℕ} (hq : 2 ≤ q) :
    q ^ 70 ≤ CFSG.Open.ordTwistedE6 q := by
  have hq2 : 3 ≤ q ^ 2 := by
    calc 3 ≤ 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h12 : q ^ 11 ≤ q ^ 12 - 1 := e67_shift_le 12 hq (by norm_num)
  have h9 : q ^ 9 ≤ q ^ 9 + 1 := Nat.le_add_right _ _
  have h8 : q ^ 7 ≤ q ^ 8 - 1 := e67_shift_le 8 hq (by norm_num)
  have h6 : q ^ 5 ≤ q ^ 6 - 1 := e67_shift_le 6 hq (by norm_num)
  have h5 : q ^ 5 ≤ q ^ 5 + 1 := Nat.le_add_right _ _
  have h2 : q ^ 1 ≤ q ^ 2 - 1 := e67_shift_le 2 hq (by norm_num)
  have hF : q ^ 36 ≤ (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
      (Nat.mul_le_mul h12 h9) h8) h6) h5) h2
    calc q ^ 36 ≤ q ^ 11 * q ^ 9 * q ^ 7 * q ^ 5 * q ^ 5 * q ^ 1 := by
          rw [show q ^ 11 * q ^ 9 * q ^ 7 * q ^ 5 * q ^ 5 * q ^ 1 = q ^ 38 by ring]
          exact Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ _ := h
  have h3F : 3 * q ^ 34 ≤ (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) := by
    refine le_trans ?_ hF
    calc 3 * q ^ 34 ≤ q ^ 2 * q ^ 34 := Nat.mul_le_mul_right _ hq2
      _ = q ^ 36 := by ring
  have hgpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [CFSG.Open.ordTwistedE6, Nat.le_div_iff_mul_le hgpos]
  rw [show q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1) =
      q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1)) by ring]
  calc q ^ 70 * Nat.gcd 3 (q + 1) ≤ q ^ 70 * 3 :=
        Nat.mul_le_mul_left _ (Nat.gcd_le_left (q + 1) (by norm_num))
    _ = q ^ 36 * (3 * q ^ 34) := by ring
    _ ≤ q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1)) := Nat.mul_le_mul_left _ h3F

private theorem e67_pow70_le_ordE7 {q : ℕ} (hq : 2 ≤ q) : q ^ 70 ≤ CFSG.Open.ordE7 q := by
  have h18 : q ^ 17 ≤ q ^ 18 - 1 := e67_shift_le 18 hq (by norm_num)
  have h14 : q ^ 13 ≤ q ^ 14 - 1 := e67_shift_le 14 hq (by norm_num)
  have h12 : q ^ 11 ≤ q ^ 12 - 1 := e67_shift_le 12 hq (by norm_num)
  have h10 : q ^ 9 ≤ q ^ 10 - 1 := e67_shift_le 10 hq (by norm_num)
  have h8 : q ^ 7 ≤ q ^ 8 - 1 := e67_shift_le 8 hq (by norm_num)
  have h6 : q ^ 5 ≤ q ^ 6 - 1 := e67_shift_le 6 hq (by norm_num)
  have h2 : q ^ 1 ≤ q ^ 2 - 1 := e67_shift_le 2 hq (by norm_num)
  have hF : q ^ 63 ≤ (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
      (Nat.mul_le_mul h18 h14) h12) h10) h8) h6) h2
    calc q ^ 63 = q ^ 17 * q ^ 13 * q ^ 11 * q ^ 9 * q ^ 7 * q ^ 5 * q ^ 1 := by ring
      _ ≤ _ := h
  have h2q : 2 * q ^ 7 ≤ q ^ 63 := by
    have h : 2 ≤ q ^ 56 := by
      calc 2 ≤ 2 ^ 56 := by norm_num
        _ ≤ q ^ 56 := Nat.pow_le_pow_left hq 56
    calc 2 * q ^ 7 = q ^ 7 * 2 := by ring
      _ ≤ q ^ 7 * q ^ 56 := Nat.mul_le_mul_left _ h
      _ = q ^ 63 := by ring
  have hgpos : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [CFSG.Open.ordE7, Nat.le_div_iff_mul_le hgpos]
  rw [show q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1) =
      q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1)) by ring]
  calc q ^ 70 * Nat.gcd 2 (q - 1) ≤ q ^ 70 * 2 :=
        Nat.mul_le_mul_left _ (Nat.gcd_le_left (q - 1) (by norm_num))
    _ = q ^ 63 * (2 * q ^ 7) := by ring
    _ ≤ q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1)) := Nat.mul_le_mul_left _ (le_trans h2q hF)

theorem eq_of_ggLabelIso_of_excE67 {labJ lab : LargeEvenLabel} (h : GGLabelIso labJ lab)
    (hT : labJ.tag = .E6 ∨ labJ.tag = .twE6 ∨ labJ.tag = .E7) : labJ = lab := by
  obtain ⟨t, l, n⟩ := labJ
  obtain ⟨t', l', n'⟩ := lab
  have hT' : t = .E6 ∨ t = .twE6 ∨ t = .E7 := by
    simpa only [] using hT
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h with ⟨h1, -, -, -⟩
    rcases hT' with h5 | h5 | h5 <;> rcases h1 with h6 | h6 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .D := congrArg LargeEvenLabel.tag h1
    rcases hT' with h5 | h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    rcases hT' with h5 | h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases hT' with h5 | h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twA := congrArg LargeEvenLabel.tag h1
    rcases hT' with h5 | h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases hT' with h5 | h5 | h5 <;> simp_all
  · rcases h with ⟨-, h1⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    rcases hT' with h5 | h5 | h5 <;> simp_all

theorem ggTorsion_not_markingE67_of_classical
    {J : Type} [Group J]
    (h : (∃ (t : CFSG.Open.StatedLieTag) (n f : ℕ),
        CFSG.Open.StatedClassicalModel (J ⧸ Subgroup.center J) t n 2 f) ∨
      Nat.card (J ⧸ Subgroup.center J) = 360) :
    ¬ LargeEvenMarking J fun lab _ _ _ _ _ =>
      lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 := by
  intro hmark
  obtain ⟨-, labJ, hlabJ, hrawJ⟩ := largeEvenMarking_markedModel hmark
  obtain ⟨R, _, I, F, _hs, _hna, θ, hP, hM⟩ := largeEvenRawDatum_exists hrawJ
  rcases h with ⟨t, n, f, hL⟩ | h360
  · obtain ⟨lab, hlab, htag, -, -, -, hraw⟩ :=
      CFSG.StandardType.exists_label_rawDatum_of_statedClassicalModel hL
    have hasJ : GGHasLabel labJ (J ⧸ Subgroup.center J) := by
      refine largeEvenRawDatum_mono ?_ hrawJ
      intro R _ I F h
      obtain ⟨-, -, θ, -⟩ := h
      exact ⟨θ⟩
    have hIso : GGLabelIso labJ lab :=
      ggLabelRigidInput_holds labJ lab (J ⧸ Subgroup.center J) hlabJ hlab hasJ hraw
    have hEq : labJ = lab := eq_of_ggLabelIso_of_excE67 hIso hP
    subst hEq
    obtain ⟨tg, l, n'⟩ := labJ
    rcases hP with rfl | rfl | rfl <;> dsimp only [markTag] at htag <;> subst htag <;>
      exact hL.2.elim
  · have hcard : Nat.card R = 360 := by
      rw [← h360]
      exact (Nat.card_congr θ.toEquiv).symm
    have hne : labJ.tag ≠ .B2der := by
      rcases hP with h | h | h <;> rw [h] <;> decide
    exact ggMarkedModel_card_ne_three_sixty hne hM hcard

theorem ggTorsion_markingE67_card
    {J : Type} [Group J]
    (hJ : LargeEvenMarking J fun lab _ _ _ _ _ =>
      lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) :
    3 ∣ Nat.card (J ⧸ Subgroup.center J) ∧ 2 ^ 70 ≤ Nat.card (J ⧸ Subgroup.center J) := by
  obtain ⟨lab, hlab, R, _hRgrp, I, F, θ, _hsimple, _hna, hP, hM⟩ :=
    largeEvenMarking_exists_markedModel hJ
  have hcard : Nat.card (J ⧸ Subgroup.center J) = Nat.card R := Nat.card_congr θ.toEquiv
  obtain ⟨t, l, n⟩ := lab
  have hT : t = .E6 ∨ t = .twE6 ∨ t = .E7 := by
    simpa only [] using hP
  rcases hT with hT | hT | hT
  · subst hT
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordE6 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    exact ⟨by rw [hcard, hR]; exact e67_three_dvd_ordE6 (e67_not_three_dvd_two_pow n),
      by
        rw [hcard, hR]
        exact le_trans (Nat.pow_le_pow_left (e67_two_le_two_pow hn) 70)
          (e67_pow70_le_ordE6 (e67_two_le_two_pow hn))⟩
  · subst hT
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordTwistedE6 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    exact ⟨by rw [hcard, hR]; exact e67_three_dvd_ordTwistedE6 (e67_not_three_dvd_two_pow n),
      by
        rw [hcard, hR]
        exact le_trans (Nat.pow_le_pow_left (e67_two_le_two_pow hn) 70)
          (e67_pow70_le_ordTwistedE6 (e67_two_le_two_pow hn))⟩
  · subst hT
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordE7 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    exact ⟨by
        rw [hcard, hR]
        exact e67_three_dvd_ordE7
          (dvd_trans (by norm_num : (2 : ℕ) ∣ 2) (dvd_pow_self 2 (by omega)))
          (e67_not_three_dvd_two_pow n),
      by
        rw [hcard, hR]
        exact le_trans (Nat.pow_le_pow_left (e67_two_le_two_pow hn) 70)
          (e67_pow70_le_ordE7 (e67_two_le_two_pow hn))⟩

theorem ggTorsionKnownOverTags_mono {P P' T : LargeEvenLabel → Prop}
    (h : GGTorsionKnownOverTags P T) (hP : ∀ lab, P' lab → P lab) :
    GGTorsionKnownOverTags P' T := by
  intro p X _ _ hX δ J hdat hJ
  refine h p X hX δ J ?_ hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmk⟩ := hdat
  exact ⟨hp, hp2, hδp, hδ1, hcomp,
    largeEvenMarking_mono (fun lab R _ I F θ hθ => ⟨hP lab hθ.1, hθ.2⟩) hmk⟩

theorem ggTorsionKnownOverTags_or {P Q T : LargeEvenLabel → Prop}
    (hP : GGTorsionKnownOverTags P T) (hQ : GGTorsionKnownOverTags Q T) :
    GGTorsionKnownOverTags (fun lab => P lab ∨ Q lab) T := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmk⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmk
  have key : ∀ P' : LargeEvenLabel → Prop, P' lab → GGTorsionDatum P' p δ J := by
    intro P' hP'
    refine ⟨hp, hp2, hδp, hδ1, hcomp, hXc, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, -, hI⟩
    exact ⟨hs, hna, θ, hP', hI⟩
  obtain ⟨R, _, I, F, -, -, θ, ⟨hPQ, -⟩⟩ := largeEvenRawDatum_exists hraw
  rcases hPQ with h | h
  · exact hP p X hX δ J (key _ h) hJ
  · exact hQ p X hX δ J (key _ h) hJ

end TorsionE67Basic

end CFSG.StandardType
