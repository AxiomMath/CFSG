module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCenter
import CFSG.LocalAnalysis.ComponentClassification.Foote5GH74
import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.LocalAnalysis.ComponentClassification.Foote5Uniq

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial


private theorem q2cRigid_arith (q : ℕ) (hq : 5 ≤ q) :
    25920 * (q - 1) < q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
  have hq2 : 25 ≤ q ^ 2 := by
    have := Nat.mul_le_mul hq hq
    norm_num at this
    simpa [pow_two] using this
  have hq3 : 125 ≤ q ^ 3 := by
    have h := Nat.mul_le_mul hq2 hq
    norm_num at h
    calc 125 = 25 * 5 := by norm_num
      _ ≤ q ^ 2 * q := h
      _ = q ^ 3 := by ring
  have h1 : 24 ≤ q ^ 2 - 1 := by omega
  have h2 : 124 ≤ q ^ 3 - 1 := by omega
  have hprod : 2976 ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    have := Nat.mul_le_mul h1 h2
    norm_num at this
    exact this
  have hstep : 25920 * (q - 1) < 2976 * q ^ 3 := by
    have hlt : q - 1 < q := Nat.sub_lt (by omega) (by norm_num)
    have h1' : 25920 * (q - 1) < 25920 * q :=
      Nat.mul_lt_mul_of_pos_left hlt (by norm_num)
    have h2' : 25920 * q ≤ 74400 * q := Nat.mul_le_mul_right q (by norm_num)
    have h25 : 74400 ≤ 2976 * q ^ 2 := by
      have := Nat.mul_le_mul_left 2976 hq2
      norm_num at this
      exact this
    have h3' : 74400 * q ≤ 2976 * q ^ 3 := by
      calc 74400 * q ≤ (2976 * q ^ 2) * q := Nat.mul_le_mul_right q h25
        _ = 2976 * q ^ 3 := by ring
    linarith
  calc 25920 * (q - 1) < 2976 * q ^ 3 := hstep
    _ = q ^ 3 * 2976 := by ring
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul_left _ hprod
    _ = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by rw [Nat.mul_assoc]

private theorem q2cRigid_lieModel_of_projectiveSL {X : Type} [Group X]
    {n p f : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 2 ≤ n)
    (h22 : ¬ (n = 2 ∧ Nat.card K = 2)) (h23 : ¬ (n = 2 ∧ Nat.card K = 3))
    (e : X ≃* LinearFlag.projectiveSL n K) :
    CFSG.Blueprint.LieModel X .PSL n p f := by
  have h22' : ¬ ((n, p ^ f) = (2, 2)) := by
    rintro h
    simp only [Prod.mk.injEq] at h
    exact h22 ⟨h.1, by rw [hK, h.2]⟩
  have h23' : ¬ ((n, p ^ f) = (2, 3)) := by
    rintro h
    simp only [Prod.mk.injEq] at h
    exact h23 ⟨h.1, by rw [hK, h.2]⟩
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL n p f :=
    ⟨hp, hf, hn, h22', h23'⟩
  refine Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩⟩
  exact e.trans ((LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K))

private theorem q2cRigid_projectiveSL_card_gt (K : Type) [Field K] [Finite K] {d : ℕ}
    (hd : 3 ≤ d) (hK5 : 5 ≤ Nat.card K) :
    25920 < Nat.card (LinearFlag.projectiveSL d K) := by
  have hgpos : 0 < Nat.card (LinearFlag.scalars d K) := Nat.card_pos
  have hdvd : Nat.card (LinearFlag.scalars d K) ∣ Nat.card K - 1 :=
    LinearFlag.card_scalars_dvd (K := K) (n := d) (by omega)
  have hgle : Nat.card (LinearFlag.scalars d K) ≤ Nat.card K - 1 :=
    Nat.le_of_dvd (by omega) hdvd
  have hN3 : 3 ≤ d * (d - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    exact Nat.mul_le_mul hd (by omega : 2 ≤ d - 1)
  have hpows : Nat.card K ^ 3 ≤ Nat.card K ^ (d * (d - 1) / 2) :=
    Nat.pow_le_pow_right (by omega) hN3
  have hsubset : Finset.Icc 2 3 ⊆ Finset.Icc 2 d := by
    intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have hsmall : ∏ j ∈ Finset.Icc 2 3, (Nat.card K ^ j - 1) =
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1)]
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 1 + 1)]
    simp
  have hprod23 : (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) ≤
      ∏ j ∈ Finset.Icc 2 d, (Nat.card K ^ j - 1) := by
    rw [← hsmall]
    refine Finset.prod_le_prod_of_subset_of_one_le hsubset ?_
    intro j hj _
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have h2q : 2 ≤ Nat.card K ^ 2 := by
      have h : 25 ≤ Nat.card K * Nat.card K := by
        simpa using Nat.mul_le_mul hK5 hK5
      have : 2 ≤ Nat.card K * Nat.card K := le_trans (by norm_num : 2 ≤ 25) h
      simpa [pow_two] using this
    have hle : Nat.card K ^ 2 ≤ Nat.card K ^ j :=
      Nat.pow_le_pow_right (by omega) hj2
    omega
  have hSL : Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin d) K) := by
    rw [LinearFlag.card_SL_eq (K := K) (n := d) (by omega)]
    calc Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)
        = Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
          rw [Nat.mul_assoc]
      _ ≤ Nat.card K ^ (d * (d - 1) / 2) *
          ∏ j ∈ Finset.Icc 2 d, (Nat.card K ^ j - 1) := Nat.mul_le_mul hpows hprod23
  have harith := q2cRigid_arith (Nat.card K) hK5
  have hmul : 25920 * Nat.card (LinearFlag.scalars d K) <
      Nat.card (Matrix.SpecialLinearGroup (Fin d) K) := by
    calc 25920 * Nat.card (LinearFlag.scalars d K)
        ≤ 25920 * (Nat.card K - 1) := Nat.mul_le_mul_left _ hgle
      _ < Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := harith
      _ ≤ Nat.card (Matrix.SpecialLinearGroup (Fin d) K) := hSL
  have hEq : Nat.card (LinearFlag.projectiveSL d K) *
        Nat.card (LinearFlag.scalars d K) =
      Nat.card (Matrix.SpecialLinearGroup (Fin d) K) := by
    change Nat.card (Matrix.SpecialLinearGroup (Fin d) K ⧸ LinearFlag.scalars d K) *
        Nat.card (LinearFlag.scalars d K) = Nat.card (Matrix.SpecialLinearGroup (Fin d) K)
    rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup (LinearFlag.scalars d K)]
  have hlt : 25920 * Nat.card (LinearFlag.scalars d K) <
      Nat.card (LinearFlag.projectiveSL d K) * Nat.card (LinearFlag.scalars d K) := by
    rw [hEq]
    exact hmul
  exact (Nat.mul_lt_mul_right hgpos).1 hlt

private theorem q2cRigid_nontrivial_centerQuot {J : Type} [Group J]
    (hmark : LargeEvenMarking J fun _ _ _ _ _ _ => True) :
    Nontrivial (J ⧸ Subgroup.center J) := by
  obtain ⟨-, lab, hlab, hraw⟩ := hmark
  obtain ⟨R, instR, I, F, hconj⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hsimple, -, θ, -⟩ := hconj
  haveI : IsSimpleGroup R := hsimple
  exact θ.toEquiv.nontrivial

private theorem q2cRigid_three_le_d {J : Type} [Group J] {p d : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hmark : LargeEvenMarking J fun _ _ _ _ _ _ => True)
    (θ : J ⧸ Subgroup.center J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hpd : p ∣ d) : 3 ≤ d := by
  haveI : Nontrivial (J ⧸ Subgroup.center J) := q2cRigid_nontrivial_centerQuot hmark
  by_contra h
  have hcases : d ≤ 1 ∨ d = 2 := by omega
  rcases hcases with hd1 | hd2
  · haveI hsub1 : Subsingleton (LinearFlag.projectiveSL d K) :=
      CFSG.AGLEmbedding.ToralCensus.subsingleton_projectiveSL hd1 K
    haveI hsub2 : Subsingleton (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
      (TypeA.recipeEquiv d K).toEquiv.subsingleton
    exact not_subsingleton _ θ.toEquiv.subsingleton
  · subst hd2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpd)

private theorem q2cRigid_not_odd {J : Type} [Group J] {p d : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hmark : LargeEvenMarking J fun _ _ _ _ _ _ => True)
    (θ : J ⧸ Subgroup.center J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hpd : p ∣ d) (hpq : p ∣ Nat.card K - 1) (hodd : Odd (Nat.card K)) : False := by
  letI : Fintype K := Fintype.ofFinite K
  have hd : 3 ≤ d := q2cRigid_three_le_d hp hp2 hmark θ hpd
  have hK5 : 5 ≤ Nat.card K := by
    have h4 : 4 ≤ Nat.card K := TableBSymp.four_le_card_of_dvd hp hp2 hpq
    have hmod : Nat.card K % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  obtain ⟨g, hgprime, hcardK⟩ := FiniteField.card K (ringChar K)
  have hcardK' : Nat.card K = ringChar K ^ (g : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcardK
  have hℓ2 : ringChar K ≠ 2 := by
    intro h2
    have h0 : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two h2
    have h1 : Nat.card K % 2 = 1 := Nat.odd_iff.mp hodd
    have hcard : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
    omega
  let X := J ⧸ Subgroup.center J
  have eX : X ≃* LinearFlag.projectiveSL d K := θ.trans (TypeA.recipeEquiv d K)
  have hcardX : Nat.card X = Nat.card (LinearFlag.projectiveSL d K) :=
    Nat.card_congr eX.toEquiv
  have hgtX : 25920 < Nat.card X := by
    rw [hcardX]
    exact q2cRigid_projectiveSL_card_gt (K := K) (d := d) hd hK5
  have hE : CFSG.Blueprint.LieModel (LinearFlag.projectiveSL d K) .PSL d
      (ringChar K) (g : ℕ) :=
    q2cRigid_lieModel_of_projectiveSL (X := LinearFlag.projectiveSL d K) (K := K)
      (n := d) (p := ringChar K) (f := (g : ℕ)) hgprime (Nat.succ_le_of_lt g.pos) hcardK'
      (by omega)
      (fun h => by omega) (fun h => by omega) (MulEquiv.refl _)
  have hEX : CFSG.Blueprint.LieModel X .PSL d (ringChar K) (g : ℕ) :=
    CFSG.Blueprint.LieModel.of_mulEquiv eX.symm hE
  have hoddLie : CFSG.Blueprint.OddLieType X :=
    CFSG.ComponentClassification.Foote5.oddLieType_of_lieModel_ne_two hEX hgprime hℓ2
  obtain ⟨lab, hlab, hM⟩ :=
    largeEvenMarking_markedModel_centerQuot (L := J) (P := fun _ _ _ _ _ _ => True) hmark
  by_cases hc : markChar lab = 2
  · have hX2 : CFSG.Blueprint.LieModel X (markTag lab) (markRank lab) 2 (markDeg lab) :=
      NbrInnerMore.lieModel_of_markedModel_two hc hM
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hX2 hoddLie with
      ⟨ht, hn, hf⟩ | ⟨ht, hn, hf⟩ | ⟨ht, hn, hf⟩
    · have hmod : CFSG.Blueprint.LieModel X .PSL 2 2 2 := by simpa [ht, hn, hf] using hX2
      have hcard : Nat.card X = 60 :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four
          (hmod.statedClassicalModel (by decide))
      omega
    · have hmod : CFSG.Blueprint.LieModel X .PSL 3 2 1 := by simpa [ht, hn, hf] using hX2
      have hcard : Nat.card X = 168 :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two
          (hmod.statedClassicalModel (by decide))
      omega
    · have hmod : CFSG.Blueprint.LieModel X .PSU 4 2 1 := by simpa [ht, hn, hf] using hX2
      have hcard : Nat.card X = 25920 :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two
          (hmod.statedClassicalModel (by decide))
      omega
  · obtain ⟨tag, rank, n⟩ := lab
    have htag : tag = .B2der ∨ tag = .G2der := by
      cases tag <;> simp [markChar] at hc ⊢
    rcases htag with htag | htag
    · subst htag
      have hmod : CFSG.Blueprint.LieModel X .PSL 2 3 2 := by
        simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
      have hcard : Nat.card X = 360 :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_nine
          (hmod.statedClassicalModel (by decide))
      omega
    · subst htag
      have hmod : CFSG.Blueprint.LieModel X .PSU 3 3 1 := by
        simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
      have hcard : Nat.card X = 6048 :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three
          (hmod.statedClassicalModel (by decide))
      omega

theorem q2c_three_le_d {J : Type} [Group J] {p d : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hmark : LargeEvenMarking J fun _ _ _ _ _ _ => True)
    (θ : J ⧸ Subgroup.center J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hpd : p ∣ d) : 3 ≤ d :=
  q2cRigid_three_le_d hp hp2 hmark θ hpd

theorem q2c_card_two_pow {J : Type} [Group J] {p d : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hmark : LargeEvenMarking J fun _ _ _ _ _ _ => True)
    (θ : J ⧸ Subgroup.center J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hpd : p ∣ d) (hpq : p ∣ Nat.card K - 1) :
    3 ≤ d ∧ ∃ m : ℕ, 2 ≤ m ∧ Nat.card K = 2 ^ m := by
  refine ⟨q2c_three_le_d hp hp2 hmark θ hpd, ?_⟩
  letI : Fintype K := Fintype.ofFinite K
  have hK4 : 4 ≤ Nat.card K := TableBSymp.four_le_card_of_dvd hp hp2 hpq
  have hEven : Even (Nat.card K) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact q2cRigid_not_odd hp hp2 hmark θ hpd hpq hodd
  have hmod : Fintype.card K % 2 = 0 := by
    have h1 : Nat.card K % 2 = 0 :=
      Nat.not_odd_iff.mp (Nat.not_odd_iff_even.mpr hEven)
    have h2 : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
    omega
  have hchar : ringChar K = 2 := (FiniteField.even_card_iff_char_two).mpr hmod
  haveI : CharP K 2 := ringChar.of_eq hchar
  obtain ⟨m, hmprime, hcard⟩ := FiniteField.card K 2
  refine ⟨(m : ℕ), ?_, ?_⟩
  · have hcard' : Nat.card K = 2 ^ (m : ℕ) := by
      rw [Nat.card_eq_fintype_card]
      exact hcard
    have h4 : 4 ≤ 2 ^ (m : ℕ) := by rw [← hcard']; exact hK4
    have h22 : 2 ^ 2 ≤ 2 ^ (m : ℕ) := by simpa using h4
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h22
  · rw [Nat.card_eq_fintype_card]
    exact hcard

end CFSG.StandardType
