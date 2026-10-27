module

public import CFSG.RankThree.PartTwo.Sec8.Hering418RSix
public import CFSG.RankThree.PartTwo.Sec8.Hering418ROuter
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4
public import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.RankThreeEven (projSp)

section Outer


theorem exists_mul_pow_inn_sp4 {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) {A B : MulAut (StatedProj (StatedSp 2 F))} (hA3 : A ^ 3 = 1)
    (hB3 : B ^ 3 = 1) (hAD : A ∉ (conjAut 2 F).range) (hBD : B ∉ (conjAut 2 F).range) :
    ∃ j : ℕ, A * B ^ j ∈ (conjAut 2 F).range := by
  obtain ⟨σ₁, hσ₁, H₁, hA⟩ := KFacts.sp4_even_order_three_field_descent A hA3 hAD
  obtain ⟨σ₂, hσ₂, H₂, hB⟩ := KFacts.sp4_even_order_three_field_descent B hB3 hBD
  have h3 : σ₁ ^ 3 = 1 := by rw [← hσ₁]; exact pow_orderOf_eq_one σ₁
  have hΦ : ∀ (σ : F ≃+* F) (t : gsp 2 F), ∃ t' : gsp 2 F,
      fieldAut 2 F σ * conjAut 2 F t * (fieldAut 2 F σ)⁻¹ = conjAut 2 F t' :=
    fun σ t => ⟨_, fieldAut_mul_conjAut_mul_inv σ t⟩
  obtain ⟨t₁, ht₁⟩ := exists_conj_mul_inv_eq_of_normalizes (conjAut 2 F) (fieldAut 2 F σ₁)
    (hΦ σ₁) H₁
  obtain ⟨t₂, ht₂⟩ := exists_conj_mul_inv_eq_of_normalizes (conjAut 2 F) (fieldAut 2 F σ₂)
    (hΦ σ₂) H₂
  obtain ⟨j, hj⟩ := exists_mul_pow_mem_range_of_normalizes (conjAut 2 F) (fieldAut 2 F) hΦ
    (ringAut_order_three_rel Nat.prime_two hf hF hσ₁ hσ₂) h3 t₁ t₂
  refine ⟨j, ?_⟩
  rw [hA, hB, ht₁, ht₂]
  exact hj


theorem isSimpleGroup_projSp_two {j : ℕ} (hj : 2 ≤ j) :
    IsSimpleGroup (projSp 2 (GaloisField 2 j)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 j) = 2 ^ j := GaloisField.card 2 j (by omega)
  have hq : 4 ≤ 2 ^ j := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
    (GaloisField 2 j) 2 (by norm_num) (Or.inl (Or.inr (by rw [hF]; exact hq)))
  exact (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
    (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 j))).symm.isSimpleGroup

theorem kF418OuterOn_SpFourSix : KF418OuterOn (fun X _ => IsSpFourSix X) := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa hbk
  obtain ⟨k, hk1, ⟨m, rfl⟩, ⟨φ⟩⟩ := hl
  have hm1 : 1 ≤ m := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hβ : Sec4.InducesOuterTheta b L := by
    rcases hbk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .field) L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .graphField) L h (by decide)
  obtain ⟨-, ⟨eC⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := m) (by omega) hb3 hβ ⟨φ⟩
  haveI hF3 : IsSimpleGroup (projSp 2 (GaloisField 2 (3 * m))) :=
    isSimpleGroup_projSp_two (by omega)
  haveI : IsSimpleGroup (L ⧸ aschbacherSolvableCore 3 L) := φ.isSimpleGroup
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_isQuasisimple_of_isSimpleGroup hL.2.2
  by_cases hm : m = 1
  ·
    subst hm
    have h7 : 7 ∣ Nat.card ((K ⧸ aschbacherSolvableCore 3 K) ⧸
        Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) := (type418Arith_of hn hKq htype).1
    have h1 := card_quot_center_dvd_card c.hKL
    have hT := c.card_rhoK_range_dvd hZ
    have hC : Nat.card (Sec8.barCentralizer (Subgroup.zpowers b) L) = 720 := by
      rw [Nat.card_congr eC.toEquiv]
      exact CFSG.PGLModel.card_projSp_two_two
    have h := h7.trans (h1.trans hT)
    rw [hC] at h
    omega
  ·
    have hm2 : 2 ≤ m := by omega
    haveI := isSimpleGroup_projSp_two hm2
    haveI : IsSimpleGroup ↥(Sec8.barCentralizer (Subgroup.zpowers b) L) := eC.isSimpleGroup
    have hC := barCentralizer_le_imageModTheta_of_simple c.hbL hb3 hK inferInstance
      (imageModTheta_ne_bot c.hKL hKq)
    have hinn : ∃ j : ℕ, c.alpha * c.beta ^ j ∈ innBar L := by
      set F := GaloisField 2 (3 * m) with hFdef
      let e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 F) :=
        φ.trans (CFSG.PGLModel.projSpEquivStatedProj 2 F)
      have hA3 : KFacts.inducedAutHom L e ⟨a, c.haL⟩ ^ 3 = 1 :=
        KFacts.inducedAutHom_pow_eq_one L e c.haL c.ha3
      have hB3 : KFacts.inducedAutHom L e ⟨b, c.hbL⟩ ^ 3 = 1 :=
        KFacts.inducedAutHom_pow_eq_one L e c.hbL c.hb3
      have hBout : ¬ KFacts.IsInnerAut (KFacts.inducedAutHom L e ⟨b, c.hbL⟩) :=
        (KFacts.not_isInnerAut_inducedAutHom_iff L e c.hbL).mpr hβ
      by_cases hAin : KFacts.IsInnerAut (KFacts.inducedAutHom L e ⟨a, c.haL⟩)
      · refine ⟨0, ?_⟩
        rw [pow_zero, mul_one]
        exact (KFacts.isInnerAut_congr e c.alpha).mp hAin
      · have hAD : KFacts.inducedAutHom L e ⟨a, c.haL⟩ ∉ (conjAut 2 F).range := by
          rintro ⟨H, hH⟩
          exact hAin (hH ▸ KFacts.conjAut_mem_inner_of_charTwo H)
        have hBD : KFacts.inducedAutHom L e ⟨b, c.hbL⟩ ∉ (conjAut 2 F).range := by
          rintro ⟨H, hH⟩
          exact hBout (hH ▸ KFacts.conjAut_mem_inner_of_charTwo H)
        have hFcard : Nat.card F = 2 ^ (3 * m) := GaloisField.card 2 (3 * m) (by omega)
        obtain ⟨j, H, hH⟩ := exists_mul_pow_inn_sp4 (by omega : 1 ≤ 3 * m) hFcard hA3 hB3 hAD hBD
        refine ⟨j, ?_⟩
        have h1 : KFacts.inducedAutHom L e ⟨a, c.haL⟩ *
            KFacts.inducedAutHom L e ⟨b, c.hbL⟩ ^ j = MulAut.congr e (c.alpha * c.beta ^ j) := by
          rw [map_mul, map_pow]
          rfl
        have hin : KFacts.IsInnerAut (MulAut.congr e (c.alpha * c.beta ^ j)) := by
          rw [← h1, ← hH]
          exact KFacts.conjAut_mem_inner_of_charTwo H
        exact (KFacts.isInnerAut_congr e _).mp hin
    exact c.false_of_outer_core hZ hinn hC

theorem kF418ModelOn_SpFourSix : KF418ModelOn (fun X _ => IsSpFourSix X) :=
  kF418ModelOn_SpFourSix_of_outer kF418OuterOn_SpFourSix

end Outer

end CFSG.RankThree.PartTwo.Sec8.Hering418
