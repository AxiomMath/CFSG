module

public import CFSG.LocalAnalysis.StandardType.GGKGTag
public import CFSG.LocalAnalysis.StandardType.GGKGOrd
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F

private lemma kgsb_pow_twelve (n : ℕ) : (2 ^ n) ^ 12 = 2 ^ (12 * n) := by
  rw [← pow_mul, mul_comm n 12]

private lemma kgsb_two_pow_even_mul (n i : ℕ) :
    2 ^ (2 * n * i) = (2 ^ n) ^ (2 * i) := by
  rw [← pow_mul]
  congr 1
  ring_nf

private lemma kgsb_two_pow_mul_nine (n : ℕ) : 2 ^ (n * 9) = (2 ^ n) ^ 9 := by
  rw [pow_mul]

private lemma kgsb_prod_Icc_three (n : ℕ) :
    ∏ i ∈ Finset.Icc 1 3, (2 ^ (2 * n * i) - 1) =
      ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 6 - 1) := by
  rw [Finset.prod_Icc_succ_top (a := 1) (b := 2) (by norm_num)]
  rw [Finset.prod_Icc_succ_top (a := 1) (b := 1) (by norm_num)]
  rw [Finset.prod_Icc_succ_top (a := 1) (b := 0) (by norm_num)]
  simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (1 : ℕ) > 0), Finset.prod_empty, one_mul]
  rw [kgsb_two_pow_even_mul, kgsb_two_pow_even_mul, kgsb_two_pow_even_mul]

private lemma kgsb_pos_pow_sub_one {Q : ℕ} (hQ : 2 ≤ Q) {j : ℕ} (hj : j ≠ 0) :
    0 < Q ^ j - 1 := by
  have h1 : 1 < Q ^ j :=
    lt_of_lt_of_le (Nat.one_lt_two_pow hj) (Nat.pow_le_pow_left hQ j)
  exact Nat.sub_pos_of_lt h1

private lemma kgsb_coprime_pow_sub_one {Q : ℕ} (hQ : 2 ≤ Q) {j : ℕ} (hj : j ≠ 0) :
    Nat.Coprime (Q ^ j - 1) Q := by
  have h1 : 1 ≤ Q ^ j := Nat.one_le_pow j Q (by omega)
  have hcop : Nat.Coprime (Q ^ j) (Q ^ j - 1) :=
    (Nat.coprime_self_sub_right h1).mpr (Nat.coprime_one_right _)
  exact hcop.symm.coprime_dvd_right (dvd_pow_self Q hj)

private lemma kgsb_odd_pow_add_one {Q : ℕ} (hQ : Even Q) {j : ℕ} (hj : j ≠ 0) :
    Odd (Q ^ j + 1) :=
  (Nat.even_pow.mpr ⟨hQ, hj⟩).add_odd odd_one

private lemma kgsb_odd_pow_sub_one {Q : ℕ} (hQpos : 0 < Q) (hQ : Even Q) {j : ℕ}
    (hj : j ≠ 0) : Odd (Q ^ j - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow j Q hQpos) (Nat.even_pow.mpr ⟨hQ, hj⟩) odd_one

private lemma kgsb_odd_cofactor_triD4 {Q : ℕ} (hQpos : 0 < Q) (hQ : Even Q) :
    Odd ((Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1)) := by
  have h84 : Even (Q ^ 8 + Q ^ 4) :=
    (Nat.even_pow.mpr ⟨hQ, by norm_num⟩).add (Nat.even_pow.mpr ⟨hQ, by norm_num⟩)
  have h1 : Odd (Q ^ 8 + Q ^ 4 + 1) := h84.add_odd odd_one
  exact (h1.mul (kgsb_odd_pow_sub_one hQpos hQ (by norm_num))).mul
    (kgsb_odd_pow_sub_one hQpos hQ (by norm_num))

private lemma kgsb_odd_cofactor_twF4 {Q : ℕ} (hQpos : 0 < Q) (hQ : Even Q) :
    Odd ((Q ^ 6 + 1) * (Q ^ 4 - 1) * (Q ^ 3 + 1) * (Q - 1)) := by
  have h1 : Odd (Q ^ 6 + 1) := kgsb_odd_pow_add_one hQ (by norm_num)
  have h2 : Odd (Q ^ 4 - 1) := kgsb_odd_pow_sub_one hQpos hQ (by norm_num)
  have h3 : Odd (Q ^ 3 + 1) := kgsb_odd_pow_add_one hQ (by norm_num)
  have h4 : Odd (Q - 1) := by
    simpa using kgsb_odd_pow_sub_one hQpos hQ (j := 1) (by norm_num)
  exact ((h1.mul h2).mul h3).mul h4

private lemma kgsb_le_of_pow_two_dvd_odd {c b m : ℕ} (hm : Odd m)
    (h : 2 ^ c ∣ 2 ^ b * m) : c ≤ b := by
  have hcop : Nat.Coprime (2 ^ c) m := (Nat.coprime_two_left.mpr hm).pow_left c
  have hdvd : 2 ^ c ∣ 2 ^ b := hcop.dvd_of_dvd_mul_right h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd

private lemma kgsb_ordTrialityD4_two_part (n : ℕ) :
    ordTrialityD4 (2 ^ n) = 2 ^ (12 * n) *
      (((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1) * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
  unfold ordTrialityD4
  rw [kgsb_pow_twelve]
  ring_nf

private lemma kgsb_ordTwistedF4_two_part (n : ℕ) :
    ordTwistedF4 (2 ^ n) = 2 ^ (12 * n) *
      (((2 ^ n) ^ 6 + 1) * ((2 ^ n) ^ 4 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) - 1)) := by
  unfold ordTwistedF4
  rw [kgsb_pow_twelve]
  ring_nf

private lemma kgsb_triD4_absurd (Q : ℕ) (hQ : 2 ≤ Q)
    (h : Q ^ 9 * ((Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1)) ∣
        Q ^ 12 * ((Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1))) : False := by
  have hQpos : 0 < Q := by omega
  have h2 : 0 < Q ^ 2 - 1 := kgsb_pos_pow_sub_one hQ (by norm_num)
  have h4 : 0 < Q ^ 4 - 1 := kgsb_pos_pow_sub_one hQ (by norm_num)
  have h6 : 0 < Q ^ 6 - 1 := kgsb_pos_pow_sub_one hQ (by norm_num)
  have h1 : (Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1) ∣
      Q ^ 3 * ((Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1)) := by
    have h' : Q ^ 9 * ((Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1)) ∣
        Q ^ 9 * (Q ^ 3 * ((Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1))) := by
      convert h using 1
      ring_nf
    exact (Nat.mul_dvd_mul_iff_left (pow_pos hQpos 9)).mp h'
  have h2' : (Q ^ 4 - 1) * (Q ^ 6 - 1) ∣
      Q ^ 3 * ((Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1)) := by
    have h' : (Q ^ 2 - 1) * ((Q ^ 4 - 1) * (Q ^ 6 - 1)) ∣
        (Q ^ 2 - 1) * (Q ^ 3 * ((Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1))) := by
      convert h1 using 1 <;> ac_rfl
    exact (Nat.mul_dvd_mul_iff_left h2).mp h'
  have h3 : Q ^ 4 - 1 ∣ Q ^ 3 * (Q ^ 8 + Q ^ 4 + 1) := by
    have h' : (Q ^ 6 - 1) * (Q ^ 4 - 1) ∣
        (Q ^ 6 - 1) * (Q ^ 3 * (Q ^ 8 + Q ^ 4 + 1)) := by
      convert h2' using 1 <;> ac_rfl
    exact (Nat.mul_dvd_mul_iff_left h6).mp h'
  have hcop : Nat.Coprime (Q ^ 4 - 1) (Q ^ 3) :=
    (kgsb_coprime_pow_sub_one hQ (by norm_num : (4 : ℕ) ≠ 0)).pow_right 3
  have h4' : Q ^ 4 - 1 ∣ Q ^ 8 + Q ^ 4 + 1 := hcop.dvd_of_dvd_mul_left h3
  have hbase : Q ^ 4 - 1 ∣ (Q ^ 4 - 1) * (Q ^ 4 + 2) := dvd_mul_right _ _
  have hid : (Q ^ 4 - 1) * (Q ^ 4 + 2) + 3 = Q ^ 8 + Q ^ 4 + 1 := by
    have hQ4 : 1 ≤ Q ^ 4 := Nat.one_le_pow 4 Q (by omega)
    set R := Q ^ 4 - 1 with hR
    have hQR : Q ^ 4 = R + 1 := by
      rw [hR]
      exact (Nat.sub_add_cancel hQ4).symm
    rw [show Q ^ 8 = (Q ^ 4) ^ 2 by ring, hQR]
    ring_nf
  have h5 : Q ^ 4 - 1 ∣ 3 := by
    have hthis : Q ^ 4 - 1 ∣ (Q ^ 4 - 1) * (Q ^ 4 + 2) + 3 := by
      rw [hid]
      exact h4'
    exact (Nat.dvd_add_iff_right hbase).mpr hthis
  have hle : Q ^ 4 - 1 ≤ 3 := Nat.le_of_dvd (by norm_num) h5
  have hge : 15 ≤ Q ^ 4 - 1 := by
    have hQ4 : 16 ≤ Q ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ Q ^ 4 := Nat.pow_le_pow_left hQ 4
    omega
  omega

private lemma kgsb_twF4_absurd (Q : ℕ) (hQ : 2 ≤ Q)
    (h : Q ^ 9 * ((Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1)) ∣
        Q ^ 12 * ((Q ^ 6 + 1) * (Q ^ 4 - 1) * (Q ^ 3 + 1) * (Q - 1))) : False := by
  have hQpos : 0 < Q := by omega
  have h4 : 0 < Q ^ 4 - 1 := kgsb_pos_pow_sub_one hQ (by norm_num)
  have hQ1 : 0 < Q - 1 := by
    simpa using kgsb_pos_pow_sub_one hQ (j := 1) (by norm_num)
  have h1 : (Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1) ∣
      Q ^ 3 * ((Q ^ 6 + 1) * (Q ^ 4 - 1) * (Q ^ 3 + 1) * (Q - 1)) := by
    have h' : Q ^ 9 * ((Q ^ 2 - 1) * (Q ^ 4 - 1) * (Q ^ 6 - 1)) ∣
        Q ^ 9 * (Q ^ 3 * ((Q ^ 6 + 1) * (Q ^ 4 - 1) * (Q ^ 3 + 1) * (Q - 1))) := by
      convert h using 1
      ring_nf
    exact (Nat.mul_dvd_mul_iff_left (pow_pos hQpos 9)).mp h'
  have h2' : (Q ^ 2 - 1) * (Q ^ 6 - 1) ∣
      Q ^ 3 * ((Q ^ 6 + 1) * (Q ^ 3 + 1) * (Q - 1)) := by
    have h' : (Q ^ 4 - 1) * ((Q ^ 2 - 1) * (Q ^ 6 - 1)) ∣
        (Q ^ 4 - 1) * (Q ^ 3 * ((Q ^ 6 + 1) * (Q ^ 3 + 1) * (Q - 1))) := by
      convert h1 using 1 <;> ac_rfl
    exact (Nat.mul_dvd_mul_iff_left h4).mp h'
  have hfac2 : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    have hQ1' : 1 ≤ Q := by omega
    set R := Q - 1 with hR
    have hQR : Q = R + 1 := by
      rw [hR]
      exact (Nat.sub_add_cancel hQ1').symm
    have hsq : (R + 1) ^ 2 = R * (R + 2) + 1 := by ring
    rw [hQR, hsq]
    simp only [Nat.add_sub_cancel]
  have h4' : (Q + 1) * (Q ^ 6 - 1) ∣ Q ^ 3 * ((Q ^ 6 + 1) * (Q ^ 3 + 1)) := by
    have h' : (Q - 1) * ((Q + 1) * (Q ^ 6 - 1)) ∣
        (Q - 1) * (Q ^ 3 * ((Q ^ 6 + 1) * (Q ^ 3 + 1))) := by
      have heqL : (Q - 1) * ((Q + 1) * (Q ^ 6 - 1)) = (Q ^ 2 - 1) * (Q ^ 6 - 1) := by
        rw [hfac2]
        ac_rfl
      have heqR : (Q - 1) * (Q ^ 3 * ((Q ^ 6 + 1) * (Q ^ 3 + 1))) =
          Q ^ 3 * ((Q ^ 6 + 1) * (Q ^ 3 + 1) * (Q - 1)) := by
        ac_rfl
      rw [heqL, heqR]
      exact h2'
    exact (Nat.mul_dvd_mul_iff_left hQ1).mp h'
  have hcop1 : Nat.Coprime (Q + 1) Q :=
    (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right Q)).symm
  have hcop2 : Nat.Coprime (Q ^ 6 - 1) Q :=
    kgsb_coprime_pow_sub_one hQ (by norm_num : (6 : ℕ) ≠ 0)
  have hcop : Nat.Coprime ((Q + 1) * (Q ^ 6 - 1)) (Q ^ 3) :=
    (hcop1.mul_left hcop2).pow_right 3
  have h5 : (Q + 1) * (Q ^ 6 - 1) ∣ (Q ^ 6 + 1) * (Q ^ 3 + 1) :=
    hcop.dvd_of_dvd_mul_left h4'
  have h6' : Q ^ 6 - 1 ∣ (Q ^ 6 + 1) * (Q ^ 3 + 1) :=
    (dvd_mul_left (Q ^ 6 - 1) (Q + 1)).trans h5
  have hfac : Q ^ 6 - 1 = (Q ^ 3 - 1) * (Q ^ 3 + 1) := by
    have hQ3 : 1 ≤ Q ^ 3 := Nat.one_le_pow 3 Q (by omega)
    set R := Q ^ 3 - 1 with hR
    have hQR : Q ^ 3 = R + 1 := by
      rw [hR]
      exact (Nat.sub_add_cancel hQ3).symm
    have hsq : (R + 1) ^ 2 = R * (R + 2) + 1 := by ring
    rw [show Q ^ 6 = (Q ^ 3) ^ 2 by ring, hQR, hsq]
    simp only [Nat.add_sub_cancel]
  have hQ3p1 : 0 < Q ^ 3 + 1 := by positivity
  have h7 : Q ^ 3 - 1 ∣ Q ^ 6 + 1 := by
    have h' : (Q ^ 3 - 1) * (Q ^ 3 + 1) ∣ (Q ^ 6 + 1) * (Q ^ 3 + 1) := by
      rwa [← hfac]
    exact (Nat.mul_dvd_mul_iff_right hQ3p1).mp h'
  have hbase : Q ^ 3 - 1 ∣ (Q ^ 3 - 1) * (Q ^ 3 + 1) := dvd_mul_right _ _
  have hid : (Q ^ 3 - 1) * (Q ^ 3 + 1) + 2 = Q ^ 6 + 1 := by
    have hQ3 : 1 ≤ Q ^ 3 := Nat.one_le_pow 3 Q (by omega)
    set R := Q ^ 3 - 1 with hR
    have hQR : Q ^ 3 = R + 1 := by
      rw [hR]
      exact (Nat.sub_add_cancel hQ3).symm
    have hsq : (R + 1) ^ 2 = R * (R + 2) + 1 := by ring
    rw [show Q ^ 6 = (Q ^ 3) ^ 2 by ring, hQR, hsq]
  have h8 : Q ^ 3 - 1 ∣ 2 := by
    have hthis : Q ^ 3 - 1 ∣ (Q ^ 3 - 1) * (Q ^ 3 + 1) + 2 := by
      rw [hid]
      exact h7
    exact (Nat.dvd_add_iff_right hbase).mpr hthis
  have hle : Q ^ 3 - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) h8
  have hge : 7 ≤ Q ^ 3 - 1 := by
    have hQ3 : 8 ≤ Q ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
    omega
  omega

private lemma kgsb_markChar_two {lab : LargeEvenLabel}
    (h : lab.tag = .triD4 ∨ lab.tag = .twF4) : markChar lab = 2 := by
  obtain ⟨tg, r, n⟩ := lab
  rcases h with h | h
  · change tg = .triD4 at h
    rw [h]
    rfl
  · change tg = .twF4 at h
    rw [h]
    rfl

private lemma kgsb_evenLieOrder_triD4 {lab : LargeEvenLabel} (h : lab.tag = .triD4) :
    CFSG.SeitzReduction.F4Pilot.evenLieOrder (markTag lab) (markRank lab) (markDeg lab) =
      ordTrialityD4 (2 ^ lab.n) := by
  obtain ⟨tg, r, n⟩ := lab
  change tg = .triD4 at h
  subst h
  rfl

private lemma kgsb_evenLieOrder_twF4 {lab : LargeEvenLabel} (h : lab.tag = .twF4) :
    CFSG.SeitzReduction.F4Pilot.evenLieOrder (markTag lab) (markRank lab) (markDeg lab) =
      ordTwistedF4 (2 ^ lab.n) := by
  obtain ⟨tg, r, n⟩ := lab
  change tg = .twF4 at h
  subst h
  rfl

theorem kgSmallB_holds :
    KGSimpleOn fun lab : GLALabel => lab.tag = .triD4 ∨ lab.tag = .twF4 := by
  intro p hp hp2 S _ _ lab α K hFam hlab hcen hin hαp hα1 hK k f hk hlabK
  exfalso
  have hS : HasLabel S (· = lab) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hM : MarkedModel lab (S ⧸ Subgroup.center S) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
  have hchar : markChar lab = 2 := kgsb_markChar_two hFam
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) (markTag lab) (markRank lab)
      2 (markDeg lab) :=
    lieModel_of_mark_two hM hchar
  have hcard_quot : Nat.card (S ⧸ Subgroup.center S) =
      CFSG.SeitzReduction.F4Pilot.evenLieOrder (markTag lab) (markRank lab) (markDeg lab) :=
    CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hLM
  have hquot : Nat.card (S ⧸ Subgroup.center S) = Nat.card S :=
    Nat.card_congr
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).toEquiv
  have hKlambda : LargeEvenInLambda2 (⟨.C, k, f⟩ : LargeEvenLabel) := kg_inLambda2_C hk hlabK
  have hKcard : Nat.card (K ⧸ Subgroup.center K) =
      2 ^ (f * k ^ 2) * ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * f * i) - 1) :=
    kg_card_BC (lab := ⟨.C, k, f⟩) hKlambda (Or.inr rfl) hlabK
  have hKdvdS : Nat.card (K ⧸ Subgroup.center K) ∣ Nat.card S := by
    rw [← Subgroup.index_eq_card (Subgroup.center K)]
    exact (Subgroup.index_dvd_card (Subgroup.center K)).trans
      (Subgroup.card_subgroup_dvd_card K)
  obtain ⟨labJ, hlJ, hdvdJ, hhasJ⟩ :=
    CFSG.StandardType.TCJ.tcjSimple_holds p hp hp2 S lab α K hlab hcen hin hαp hK
  have hrig := kg_rigid_C hk hlabK hlJ hhasJ
  have hnf : lab.n ∣ f := by rw [← hrig.2.2]; exact hdvdJ
  have hf1 : 1 ≤ f := hKlambda.1
  have hn1 : 1 ≤ lab.n := hlab.1
  have hnlef : lab.n ≤ f := Nat.le_of_dvd (by omega) hnf
  have h2dvdK : 2 ^ (f * k ^ 2) ∣ Nat.card (K ⧸ Subgroup.center K) := by
    rw [hKcard]
    exact dvd_mul_right _ _
  have h2dvdS : 2 ^ (f * k ^ 2) ∣ Nat.card S := h2dvdK.trans hKdvdS
  have hfk_le : f * k ^ 2 ≤ 12 * lab.n := by
    rcases hFam with htri | htw
    · have hcardS' : Nat.card S = ordTrialityD4 (2 ^ lab.n) := by
        rw [← hquot, hcard_quot, kgsb_evenLieOrder_triD4 htri]
      have hcof : Odd (((2 ^ lab.n) ^ 8 + (2 ^ lab.n) ^ 4 + 1) *
          ((2 ^ lab.n) ^ 6 - 1) * ((2 ^ lab.n) ^ 2 - 1)) :=
        kgsb_odd_cofactor_triD4 (by positivity) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      have hdvd := h2dvdS
      rw [hcardS', kgsb_ordTrialityD4_two_part] at hdvd
      exact kgsb_le_of_pow_two_dvd_odd hcof hdvd
    · have hcardS' : Nat.card S = ordTwistedF4 (2 ^ lab.n) := by
        rw [← hquot, hcard_quot, kgsb_evenLieOrder_twF4 htw]
      have hcof : Odd (((2 ^ lab.n) ^ 6 + 1) * ((2 ^ lab.n) ^ 4 - 1) *
          ((2 ^ lab.n) ^ 3 + 1) * ((2 ^ lab.n) - 1)) :=
        kgsb_odd_cofactor_twF4 (by positivity) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      have hdvd := h2dvdS
      rw [hcardS', kgsb_ordTwistedF4_two_part] at hdvd
      exact kgsb_le_of_pow_two_dvd_odd hcof hdvd
  have hk3 : k = 3 := by
    by_contra hkne
    have hk4 : 4 ≤ k := by omega
    have h16 : 16 * lab.n ≤ f * k ^ 2 := by
      calc 16 * lab.n = lab.n * 4 ^ 2 := by ring
        _ ≤ lab.n * k ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk4 2)
        _ ≤ f * k ^ 2 := Nat.mul_le_mul_right _ hnlef
    omega
  have hfn : f = lab.n := by
    have hflt : f < 2 * lab.n := by
      by_contra hge
      have h2 : 2 * lab.n ≤ f := by omega
      have h18 : 18 * lab.n ≤ f * k ^ 2 := by
        rw [hk3]
        calc 18 * lab.n = (2 * lab.n) * 3 ^ 2 := by ring
          _ ≤ f * 3 ^ 2 := Nat.mul_le_mul_right _ h2
      omega
    obtain ⟨c, hc⟩ := hnf
    have hc1 : c = 1 := by
      have hpos : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · rw [h0, mul_zero] at hc
          omega
        · exact h0
      have hlt : c < 2 := by
        have hlt' : lab.n * c < lab.n * 2 := by
          rw [← hc]
          calc f < 2 * lab.n := hflt
            _ = lab.n * 2 := by ring
        exact Nat.lt_of_mul_lt_mul_left hlt'
      omega
    rw [hc, hc1, mul_one]
  have hQ : 2 ≤ 2 ^ lab.n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn1
  have hKord : Nat.card (K ⧸ Subgroup.center K) =
      (2 ^ lab.n) ^ 9 * (((2 ^ lab.n) ^ 2 - 1) * ((2 ^ lab.n) ^ 4 - 1) *
        ((2 ^ lab.n) ^ 6 - 1)) := by
    rw [hKcard, hk3, hfn, kgsb_prod_Icc_three]
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, kgsb_two_pow_mul_nine]
  rcases hFam with htri | htw
  · have hcardS' : Nat.card S = ordTrialityD4 (2 ^ lab.n) := by
      rw [← hquot, hcard_quot, kgsb_evenLieOrder_triD4 htri]
    have hdvd := hKdvdS
    rw [hKord, hcardS', kgsb_ordTrialityD4_two_part, ← kgsb_pow_twelve lab.n] at hdvd
    exact kgsb_triD4_absurd (2 ^ lab.n) hQ (by convert hdvd using 1 <;> ring)
  · have hcardS' : Nat.card S = ordTwistedF4 (2 ^ lab.n) := by
      rw [← hquot, hcard_quot, kgsb_evenLieOrder_twF4 htw]
    have hdvd := hKdvdS
    rw [hKord, hcardS', kgsb_ordTwistedF4_two_part, ← kgsb_pow_twelve lab.n] at hdvd
    exact kgsb_twF4_absurd (2 ^ lab.n) hQ (by convert hdvd using 1 <;> ring)

end CFSG.StandardType.KG
