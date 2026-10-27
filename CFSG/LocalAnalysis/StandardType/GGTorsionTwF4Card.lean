module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionTwF4Card

private theorem tc_markDeg_of_torsion {t : LargeEvenLieTag} {l n : ℕ}
    (h : t = .E8 ∨ t = .F4 ∨ t = .twF4 ∨ t = .twF4der) :
    markDeg (⟨t, l, n⟩ : LargeEvenLabel) = n := by
  rcases h with rfl | rfl | rfl | rfl <;> rfl

theorem eq_of_ggLabelIso_of_torsionTag {labJ lab : LargeEvenLabel}
    (h : GGLabelIso labJ lab) (hP : GGL45TorsionTag labJ) : labJ = lab := by
  obtain ⟨t, l, n⟩ := labJ
  obtain ⟨t', l', n'⟩ := lab
  have hP' : t = .E8 ∨ t = .F4 ∨ t = .twF4 ∨ t = .twF4der := by
    simpa only [GGL45TorsionTag] using hP
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h with ⟨h1, -, -, -⟩
    rcases hP' with h5 | h5 | h5 | h5 <;> rcases h1 with h6 | h6 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .D := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 | h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 | h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 | h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twA := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 | h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 | h5 | h5 <;> simp_all
  · rcases h with ⟨-, h1⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    rcases hP' with h5 | h5 | h5 | h5 <;> simp_all

private theorem tc_pow_sub_one_pos {Q k : ℕ} (hQ : 2 ≤ Q) (hk : k ≠ 0) : 0 < Q ^ k - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hk (by omega))

private theorem tc_ordTwistedF4_le_pow28 {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordTwistedF4 q ≤ q ^ 28 := by
  rw [CFSG.Open.ordTwistedF4]
  have h6 : q ^ 6 + 1 ≤ 2 * q ^ 6 := by
    have : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  have h4 : q ^ 4 - 1 ≤ q ^ 4 := Nat.sub_le _ _
  have h3 : q ^ 3 + 1 ≤ 2 * q ^ 3 := by
    have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have h1 : q - 1 ≤ q := Nat.sub_le _ _
  calc q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)
      ≤ q ^ 12 * (2 * q ^ 6) * q ^ 4 * (2 * q ^ 3) * q :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl h6) h4) h3) h1
    _ = 4 * q ^ 26 := by ring
    _ ≤ q ^ 28 := by
      have hq2 : 4 ≤ q ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      calc 4 * q ^ 26 ≤ q ^ 2 * q ^ 26 := Nat.mul_le_mul_right _ hq2
        _ = q ^ 28 := by rw [← pow_add]

private theorem tc_pow28_le_ordE8 {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 28 ≤ CFSG.Open.ordE8 Q := by
  have h120 : Q ^ 120 ≤ CFSG.Open.ordE8 Q := by
    rw [CFSG.Open.ordE8]
    have h30 : 0 < Q ^ 30 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
    have h24 : 0 < Q ^ 24 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
    have h20 : 0 < Q ^ 20 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
    have h18 : 0 < Q ^ 18 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
    have h14 : 0 < Q ^ 14 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
    have h12 : 0 < Q ^ 12 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
    have h8 : 0 < Q ^ 8 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
    have h2 : 0 < Q ^ 2 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
    calc Q ^ 120
        ≤ Q ^ 120 * (Q ^ 30 - 1) := Nat.le_mul_of_pos_right _ h30
      _ ≤ Q ^ 120 * (Q ^ 30 - 1) * (Q ^ 24 - 1) := Nat.le_mul_of_pos_right _ h24
      _ ≤ Q ^ 120 * (Q ^ 30 - 1) * (Q ^ 24 - 1) * (Q ^ 20 - 1) :=
            Nat.le_mul_of_pos_right _ h20
      _ ≤ Q ^ 120 * (Q ^ 30 - 1) * (Q ^ 24 - 1) * (Q ^ 20 - 1) * (Q ^ 18 - 1) :=
            Nat.le_mul_of_pos_right _ h18
      _ ≤ Q ^ 120 * (Q ^ 30 - 1) * (Q ^ 24 - 1) * (Q ^ 20 - 1) * (Q ^ 18 - 1) *
            (Q ^ 14 - 1) := Nat.le_mul_of_pos_right _ h14
      _ ≤ Q ^ 120 * (Q ^ 30 - 1) * (Q ^ 24 - 1) * (Q ^ 20 - 1) * (Q ^ 18 - 1) *
            (Q ^ 14 - 1) * (Q ^ 12 - 1) := Nat.le_mul_of_pos_right _ h12
      _ ≤ Q ^ 120 * (Q ^ 30 - 1) * (Q ^ 24 - 1) * (Q ^ 20 - 1) * (Q ^ 18 - 1) *
            (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 8 - 1) := Nat.le_mul_of_pos_right _ h8
      _ ≤ Q ^ 120 * (Q ^ 30 - 1) * (Q ^ 24 - 1) * (Q ^ 20 - 1) * (Q ^ 18 - 1) *
            (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 2 - 1) :=
            Nat.le_mul_of_pos_right _ h2
  exact le_trans (Nat.pow_le_pow_right (by omega) (by norm_num : 28 ≤ 120)) h120

private theorem tc_pow28_le_ordF4 {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 28 ≤ CFSG.Open.ordF4 Q := by
  rw [CFSG.Open.ordF4]
  have h12 : Q ^ 4 ≤ Q ^ 12 - 1 := by
    have h2 : Q ^ 12 = Q ^ 4 * Q ^ 8 := by rw [show 12 = 4 + 8 by norm_num, pow_add]
    have hlt8 : 1 < Q ^ 8 := Nat.one_lt_pow (by norm_num) (by omega)
    have hpos : 0 < Q ^ 4 := Nat.pow_pos (by omega)
    have hlt : Q ^ 4 < Q ^ 12 := by
      calc Q ^ 4 = Q ^ 4 * 1 := by ring
        _ < Q ^ 4 * Q ^ 8 := Nat.mul_lt_mul_of_pos_left hlt8 hpos
        _ = Q ^ 12 := h2.symm
    omega
  have h8 : 0 < Q ^ 8 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
  have h6 : 0 < Q ^ 6 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
  have h2 : 0 < Q ^ 2 - 1 := tc_pow_sub_one_pos hQ (by norm_num)
  calc Q ^ 28
      ≤ Q ^ 24 * Q ^ 4 := by rw [show 28 = 24 + 4 by norm_num, pow_add]
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) := Nat.mul_le_mul_left _ h12
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) := Nat.le_mul_of_pos_right _ h8
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) := Nat.le_mul_of_pos_right _ h6
    _ ≤ Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
          Nat.le_mul_of_pos_right _ h2

private theorem tc_ordTwistedF4_mono {q Q : ℕ} (h : q ≤ Q) :
    CFSG.Open.ordTwistedF4 q ≤ CFSG.Open.ordTwistedF4 Q := by
  rw [CFSG.Open.ordTwistedF4, CFSG.Open.ordTwistedF4]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left h 12)
          (Nat.add_le_add_right (Nat.pow_le_pow_left h 6) 1))
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 4) 1))
      (Nat.add_le_add_right (Nat.pow_le_pow_left h 3) 1))
    (Nat.sub_le_sub_right h 1)

private theorem tc_ordTwistedF4_le_ordE8 {q Q : ℕ} (hq : 2 ≤ q) (hqQ : q ≤ Q) :
    CFSG.Open.ordTwistedF4 q ≤ CFSG.Open.ordE8 Q :=
  le_trans (tc_ordTwistedF4_le_pow28 hq)
    (le_trans (Nat.pow_le_pow_left hqQ 28) (tc_pow28_le_ordE8 (by omega)))

private theorem tc_ordTwistedF4_le_ordF4 {q Q : ℕ} (hq : 2 ≤ q) (hqQ : q ≤ Q) :
    CFSG.Open.ordTwistedF4 q ≤ CFSG.Open.ordF4 Q :=
  le_trans (tc_ordTwistedF4_le_pow28 hq)
    (le_trans (Nat.pow_le_pow_left hqQ 28) (tc_pow28_le_ordF4 (by omega)))

theorem ggTorsion_marking_card_ge_twF4
    {J : Type} [Group J] {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m)
    (h : LargeEvenMarking J fun lab _ _ _ _ _ => GGL45TorsionTag lab)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hdeg : markDeg lab = (2 * a + 1) * m)
    (hhas : GGHasLabel lab (J ⧸ Subgroup.center J)) :
    CFSG.Open.ordTwistedF4 (2 ^ (2 * a + 1)) ≤ Nat.card (J ⧸ Subgroup.center J) := by
  obtain ⟨-, labJ, hlabJ, hrawJ⟩ := largeEvenMarking_markedModel h
  obtain ⟨R, _, I, F, _hs, _hna, θ, hP, hM⟩ := largeEvenRawDatum_exists hrawJ
  have hasJ : GGHasLabel labJ (J ⧸ Subgroup.center J) := by
    refine largeEvenRawDatum_mono ?_ hrawJ
    intro R _ I F h
    obtain ⟨-, -, θ, -⟩ := h
    exact ⟨θ⟩
  have hIso : GGLabelIso labJ lab :=
    ggLabelRigidInput_holds labJ lab (J ⧸ Subgroup.center J) hlabJ hlab hasJ hhas
  have hEq : labJ = lab := eq_of_ggLabelIso_of_torsionTag hIso hP
  have hcard : Nat.card (J ⧸ Subgroup.center J) = Nat.card R := Nat.card_congr θ.toEquiv
  obtain ⟨t, l, n⟩ := labJ
  have hP' : t = .E8 ∨ t = .F4 ∨ t = .twF4 ∨ t = .twF4der := by
    simpa only [GGL45TorsionTag] using hP
  have hdegJ : markDeg (⟨t, l, n⟩ : LargeEvenLabel) = (2 * a + 1) * m := by
    rw [← hEq] at hdeg
    exact hdeg
  have hmarkDeg : markDeg (⟨t, l, n⟩ : LargeEvenLabel) = n := tc_markDeg_of_torsion hP'
  have hn : n = (2 * a + 1) * m := by
    rw [hmarkDeg] at hdegJ
    exact hdegJ
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    have h1 : 1 ≤ 2 * a + 1 := by omega
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) h1
  have hqQ : 2 ^ (2 * a + 1) ≤ 2 ^ n := by
    rw [hn]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))
  rcases hP' with rfl | rfl | rfl | rfl
  · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordE8 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    rw [hcard, hR]
    exact tc_ordTwistedF4_le_ordE8 hq hqQ
  · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordF4 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    rw [hcard, hR]
    exact tc_ordTwistedF4_le_ordF4 hq hqQ
  · dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hR : Nat.card R = CFSG.Open.ordTwistedF4 (2 ^ n) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
    rw [hcard, hR]
    exact tc_ordTwistedF4_mono hqQ
  · dsimp only [LargeEvenInLambda2] at hlabJ
    obtain ⟨-, -, hn1⟩ := hlabJ
    have hge : 3 ≤ (2 * a + 1) * m := by
      have h1 : 3 ≤ 2 * a + 1 := by omega
      calc 3 = 3 * 1 := by norm_num
        _ ≤ (2 * a + 1) * m := Nat.mul_le_mul h1 hm
    omega

end TorsionTwF4Card

end CFSG.StandardType