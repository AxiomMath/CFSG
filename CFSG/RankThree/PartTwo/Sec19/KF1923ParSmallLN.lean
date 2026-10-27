module

public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSmallHomog
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dA8Holds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dL5Holds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dRed
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofA8
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofL52
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1D4
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowEight
public import CFSG.Quasithin.Vol2.Ch11L2Q5cL34
public import CFSG.Timmesfeld.Orders.ClassicalLinearThree

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec19 (IsTripleA6)

theorem ksm_card_gf2_even (k : ℕ) (hk : 1 ≤ k) :
    Nat.card (GaloisField 2 (2 * k)) = 2 ^ (2 * k) := by
  rw [GaloisField.card 2 (2 * k) (by omega)]

theorem ksm_f_arith (k : ℕ) (hk : 1 ≤ k) :
    ((2 ^ (2 * k)) ^ 3 * (((2 ^ (2 * k)) ^ 2 - 1) * ((2 ^ (2 * k)) ^ 3 - 1)) = 60480 ∧ k = 1) ∨
      4000000000 ≤ (2 ^ (2 * k)) ^ 3 * (((2 ^ (2 * k)) ^ 2 - 1) * ((2 ^ (2 * k)) ^ 3 - 1)) := by
  rcases Nat.lt_or_ge k 2 with h | h
  · left
    have hk1 : k = 1 := by omega
    subst hk1
    norm_num
  · right
    have h16 : 16 ≤ 2 ^ (2 * k) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 16 ^ 3 * ((16 ^ 2 - 1) * (16 ^ 3 - 1)) ≤
        (2 ^ (2 * k)) ^ 3 * (((2 ^ (2 * k)) ^ 2 - 1) * ((2 ^ (2 * k)) ^ 3 - 1)) := by
      apply Nat.mul_le_mul (Nat.pow_le_pow_left h16 3)
      apply Nat.mul_le_mul
      · exact Nat.sub_le_sub_right (Nat.pow_le_pow_left h16 2) 1
      · exact Nat.sub_le_sub_right (Nat.pow_le_pow_left h16 3) 1
    calc 4000000000 ≤ 16 ^ 3 * ((16 ^ 2 - 1) * (16 ^ 3 - 1)) := by norm_num
      _ ≤ _ := h1

theorem ksm_card_sl3_gf (k : ℕ) (hk : 1 ≤ k) {X : Type} [Group X]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * k))) :
    Nat.card X = (2 ^ (2 * k)) ^ 3 * (((2 ^ (2 * k)) ^ 2 - 1) * ((2 ^ (2 * k)) ^ 3 - 1)) := by
  rw [Nat.card_congr e.toEquiv, CFSG.GH74.KGroups.L3Eps.card_specialLinear_three,
    ksm_card_gf2_even k hk]
  ring

theorem ksm_stated_psl {X : Type} [Group X] (n : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ)
    (hadm : CFSG.Open.StatedLieAdmissible .PSL n p f) (hK : Nat.card K = p ^ f)
    (e : X ≃* projSL n K) : CFSG.Open.StatedClassicalModel X .PSL n p f :=
  ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans (CFSG.PGLModel.projSLEquivStatedProj n K)⟩⟩

theorem ksm_psl3_mul {X : Type} [Group X] (K : Type) [Field K] [Finite K]
    (e : X ≃* projSL 3 K) :
    Nat.card X * Nat.gcd 3 (Nat.card K - 1) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  have hX : Nat.card X = Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K)) :=
    Nat.card_congr (e.trans (CFSG.PGLModel.projSLEquivStatedProj 3 K)).toEquiv
  rw [hX]
  exact CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd

theorem ksm_psl3_bounds {X : Type} [Group X] (k : ℕ) (hk : 1 ≤ k)
    (e : X ≃* projSL 3 (GaloisField 2 (2 * k))) :
    Nat.card X ≤ (2 ^ (2 * k)) ^ 3 * (((2 ^ (2 * k)) ^ 2 - 1) * ((2 ^ (2 * k)) ^ 3 - 1)) ∧
      (2 ^ (2 * k)) ^ 3 * (((2 ^ (2 * k)) ^ 2 - 1) * ((2 ^ (2 * k)) ^ 3 - 1)) ≤
        3 * Nat.card X := by
  have hm := ksm_psl3_mul (X := X) (GaloisField 2 (2 * k)) e
  rw [ksm_card_gf2_even k hk] at hm
  have hg1 : 1 ≤ Nat.gcd 3 (2 ^ (2 * k) - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg3 : Nat.gcd 3 (2 ^ (2 * k) - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  constructor
  · rw [← hm]
    exact Nat.le_mul_of_pos_right _ hg1
  · rw [← hm]
    have h3 := Nat.mul_le_mul_left (Nat.card X) hg3
    linarith

theorem ksm_card_psl4_four {X : Type} [Group X] [Finite X]
    (e : X ≃* projSL 4 (GaloisField 2 2)) : Nat.card X = 987033600 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSL_four_mul (GaloisField 2 2)
  rw [hK, ← Nat.card_congr e.toEquiv] at h
  norm_num at h
  linarith

theorem ksm_card_tripleA6 {X : Type} [Group X] (hT : IsTripleA6 X) :
    Nat.card X = 1080 := by
  obtain ⟨hZ3, ⟨φ⟩⟩ := hT
  have h1 := Subgroup.card_mul_index (Subgroup.center X)
  have h2 : (Subgroup.center X).index = 360 := by
    rw [Subgroup.index, Nat.card_congr φ.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  rw [hZ3, h2] at h1
  omega

theorem ksm_card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem ksm_card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem ksm_not_noncyclic_l4 {X : Type} [Group X] [Finite X]
    (e4 : X ≃* projSL 4 (GaloisField 2 1)) : ¬ IsNoncyclicOutType X := by
  have hN : Nat.card X = 20160 :=
    (Nat.card_congr
      (e4.trans CFSG.RankThree.PartTwo.Sec4.Res417Four.a8EquivProjSL.symm).toEquiv).trans
      ksm_card_alt_eight
  intro h
  rcases h with ⟨k, hk, hSL | hPSL⟩ | hL4 | hA6 | hT6
  · obtain ⟨eSL⟩ := hSL
    have hc := ksm_card_sl3_gf k hk eSL
    rcases ksm_f_arith k hk with ⟨h1, -⟩ | h1 <;> linarith
  · obtain ⟨e3⟩ := hPSL
    obtain ⟨hb1, hb2⟩ := ksm_psl3_bounds k hk e3
    rcases ksm_f_arith k hk with ⟨h1, hk1⟩ | h1
    ·
      subst hk1
      have hm3 : CFSG.Open.StatedClassicalModel X .PSL 3 2 2 :=
        ksm_stated_psl 3 (GaloisField 2 (2 * 1)) 2 2 (by norm_num [CFSG.Open.StatedLieAdmissible])
          (by rw [ksm_card_gf2_even 1 le_rfl] <;> norm_num) e3
      have hm4 : CFSG.Open.StatedClassicalModel X .PSL 4 2 1 :=
        ksm_stated_psl 4 (GaloisField 2 1) 2 1 (by norm_num [CFSG.Open.StatedLieAdmissible])
          (by rw [GaloisField.card 2 1 (by norm_num)] <;> norm_num) e4
      exact CFSG.Quasithin.Vol2.Ch11.SecB.not_isPSL_four_two_one_of_isPSL_three_two_two hm3 hm4
    · linarith
  · obtain ⟨eL4⟩ := hL4
    have := ksm_card_psl4_four eL4
    linarith
  · obtain ⟨eA6⟩ := hA6
    have := Nat.card_congr eA6.toEquiv
    rw [ksm_card_alt_six] at this
    linarith
  · have := ksm_card_tripleA6 hT6
    linarith

theorem ksm_not_noncyclic_l5 {X : Type} [Group X] [Finite X]
    (e5 : X ≃* projSL 5 (GaloisField 2 1)) : ¬ IsNoncyclicOutType X := by
  have hN : Nat.card X = 9999360 := by
    rw [Nat.card_congr e5.toEquiv, CFSG.RankThree.PartTwo.Sec14.Ronan148K.card_projSL_five_two_gf2]
  intro h
  rcases h with ⟨k, hk, hSL | hPSL⟩ | hL4 | hA6 | hT6
  · obtain ⟨eSL⟩ := hSL
    have hc := ksm_card_sl3_gf k hk eSL
    rcases ksm_f_arith k hk with ⟨h1, -⟩ | h1 <;> linarith
  · obtain ⟨e3⟩ := hPSL
    obtain ⟨hb1, hb2⟩ := ksm_psl3_bounds k hk e3
    rcases ksm_f_arith k hk with ⟨h1, -⟩ | h1 <;> linarith
  · obtain ⟨eL4⟩ := hL4
    have := ksm_card_psl4_four eL4
    linarith
  · obtain ⟨eA6⟩ := hA6
    have := Nat.card_congr eA6.toEquiv
    rw [ksm_card_alt_six] at this
    linarith
  · have := ksm_card_tripleA6 hT6
    linarith

theorem ksm_nsq_l4 {X : Type} [Group X] [Finite X] (e4 : X ≃* projSL 4 (GaloisField 2 1)) :
    NoSquareInvertingInParabolic X := by
  have eA8 : X ≃* alternatingGroup (Fin 8) :=
    e4.trans CFSG.RankThree.PartTwo.Sec4.Res417Four.a8EquivProjSL.symm
  have hK : CFSG.LocalAnalysis.RankThreeUC.S15.K21dGeomAt X :=
    CFSG.LocalAnalysis.RankThreeUC.S15.k21dGeomA8_holds X ⟨eA8⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup X := eA8.isSimpleGroup
  have hN : Nat.card X = 20160 := (Nat.card_congr eA8.toEquiv).trans ksm_card_alt_eight
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K21dRedProof.center_eq_bot_of_simple
      (CFSG.RankThree.PartTwo.Sec4.Ronan148R.exists_ne_comm_of_simple (by rw [hN]; norm_num))
  exact ksm_noSq_of_K21 hK hZ

theorem ksm_nsq_l5 {X : Type} [Group X] [Finite X] (e5 : X ≃* projSL 5 (GaloisField 2 1)) :
    NoSquareInvertingInParabolic X := by
  have e' : X ≃* GL (Fin 5) (ZMod 2) :=
    e5.trans CFSG.RankThree.PartTwo.Sec4.Res417Four.gl5EquivProjSL.symm
  have hK : CFSG.LocalAnalysis.RankThreeUC.S15.K21dGeomAt X :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K21dA8Proof.k21dGeomAt_of_mulEquiv
      (e'.trans CFSG.LocalAnalysis.RankThreeUC.S15.K21dL5Proof.slEquivGL5.symm)
      CFSG.LocalAnalysis.RankThreeUC.S15.K21dL5Proof.k21dGeomAt_SL5
  haveI : IsSimpleGroup (GL (Fin 5) (ZMod 2)) := CFSG.GroupTheory.GL52.isSimpleGroup_G52
  haveI : IsSimpleGroup X := e'.isSimpleGroup
  have hN : Nat.card X = 9999360 := by
    rw [Nat.card_congr e5.toEquiv, CFSG.RankThree.PartTwo.Sec14.Ronan148K.card_projSL_five_two_gf2]
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K21dRedProof.center_eq_bot_of_simple
      (CFSG.RankThree.PartTwo.Sec4.Ronan148R.exists_ne_comm_of_simple (by rw [hN]; norm_num))
  exact ksm_noSq_of_K21 hK hZ

end CFSG.RankThree.PartTwo.Late
