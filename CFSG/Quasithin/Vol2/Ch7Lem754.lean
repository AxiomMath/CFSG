module

public import CFSG.Quasithin.Vol2.Ch7Lem741

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

@[expose] def Stmt7_2_1_M12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I),
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      Row711M12 T L I →
        Nat.card ↥(fsuV T I) = 2 ^ 10 ∧ CFSG.Open.pRank 2 (autI hV ⊤) ≤ 4 ∧
          (6 : ℕ∞) ≤ betaH (autI hV ⊤) ∧ alphaH (autI hV ⊤) = 1 ∧
          ∀ A : Subgroup (MulAut (IntMod (fsuV T I) hV)), A ≤ autI hV ⊤ → IsElemAbelian2 A →
            Nat.card A = 16 → Nat.card ↥(fixV A) ≤ 2 ^ 3 ∧ 2 ^ 8 ≤ Nat.card ↥(Mathieu.xiV A)

@[expose] def Stmt7_2_1_M23Code : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I),
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      Row711M23Code T L I →
        CFSG.Open.pRank 2 (autI hV ⊤) ≤ 4 ∧ (6 : ℕ∞) ≤ betaH (autI hV ⊤) ∧
          alphaH (autI hV ⊤) = 1 ∧
          ∀ A : Subgroup (MulAut (IntMod (fsuV T I) hV)), A ≤ autI hV ⊤ → IsElemAbelian2 A →
            Nat.card A = 16 → rkIdx (Mathieu.xiV A) ≤ 1

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fwci_eq_six (h734 : Stmt7_3_4) (hin : Input8_1_2) (h325 : Stmt3_2_5)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hk : nPrime (autI hV ⊤) = 2)
    (hm2 : CFSG.Open.pRank 2 (autI hV ⊤) ≤ 4) (hβ : (6 : ℕ∞) ≤ betaH (autI hV ⊤))
    (hα : alphaH (autI hV ⊤) = 1) :
    rParam (fsuV T I) = ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T (fsuV T I) ∧
      CFSG.Open.pRank 2 (autI hV ⊤) = 4 ∧ wParam T (fsuV T I) = 2 := by
  have hr6 := hβ.trans (betaH_le_rParam_of_alpha hin h325 hyp h731 hTL hV hN hNM hα)
  have hfw := lemma_7_5_1 hyp hV hN hNM
  obtain ⟨-, hwn, -, -⟩ := h734 G T L I hyp h731 hV
  rw [hk] at hwn
  obtain ⟨w, hw⟩ : ∃ w : ℕ, wParam T (fsuV T I) = w :=
    ⟨(wParam T (fsuV T I)).toNat, (ENat.coe_toNat (ne_top_of_le_ne_top (by simp) hwn)).symm⟩
  rw [hw] at hwn hfw ⊢
  have hw2 : w ≤ 2 := by exact_mod_cast hwn
  have h6 : (6 : ℕ∞) ≤ ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + (w : ℕ∞) := hr6.trans hfw
  have h6' : 6 ≤ CFSG.Open.pRank 2 (autI hV ⊤) + w := by exact_mod_cast h6
  have hm4 : CFSG.Open.pRank 2 (autI hV ⊤) = 4 := by omega
  have hw2' : w = 2 := by omega
  refine ⟨le_antisymm hfw ?_, hm4, by exact_mod_cast hw2'⟩
  calc ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + (w : ℕ∞) = 6 := by
        rw [hm4, hw2'] <;> norm_num
    _ ≤ rParam (fsuV T I) := hr6

theorem offender_xiV (hV : IsElemAbelian 2 (fsuV T I)) (hT : HypE322 T (fsuV T I))
    (h24 : HypE324 T (fsuV T I) hV) {g : G} (hg : IsWOffenderAt T (fsuV T I) g)
    (hEq : rParam (fsuV T I) =
      ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T (fsuV T I))
    (hm4 : CFSG.Open.pRank 2 (autI hV ⊤) = 4) :
    rk ↥(autI hV (conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G))) = 4 ∧
      Nat.card ↥(autI hV (conjSubgroup (fsuV T I) g ⊓
        Subgroup.normalizer (fsuV T I : Set G))) = 16 ∧
      IsElemAbelian2 (autI hV (conjSubgroup (fsuV T I) g ⊓
        Subgroup.normalizer (fsuV T I : Set G))) ∧
      wParam T (fsuV T I) ≤ ((rkIdx (gammaCheck 3 (autI hV (conjSubgroup (fsuV T I) g ⊓
        Subgroup.normalizer (fsuV T I : Set G)))) : ℕ) : ℕ∞) ∧
      rkIdx (gammaCheck 3 (autI hV (conjSubgroup (fsuV T I) g ⊓
          Subgroup.normalizer (fsuV T I : Set G)))) ≤
        rkIdx (Mathieu.xiV (autI hV (conjSubgroup (fsuV T I) g ⊓
          Subgroup.normalizer (fsuV T I : Set G)))) := by
  have hVg : IsElemAbelian 2 (conjSubgroup (fsuV T I) g) := isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 (conjSubgroup (fsuV T I) g ⊓
      Subgroup.normalizer (fsuV T I : Set G)) := B2F.isElemAbelian_mono inf_le_left hVg
  have hA2 := isElemAbelian2_autI hV hAel inf_le_right
  obtain ⟨hrkA, -⟩ := e3_31_one_core hV hT h24 hg hEq
  rw [hm4] at hrkA
  have hcardA := card_eq_two_pow_rk hA2
  rw [hrkA] at hcardA
  have hW := e3_31_two_ge hV hT h24 hg hEq
  rw [hrkA] at hW
  refine ⟨hrkA, by rw [hcardA] <;> norm_num, hA2, hW, ?_⟩
  exact CFSG.Quasithin.rkIdx_anti (xiV_le_gammaCheck hA2 (by omega))

theorem stmt7_5_4_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711 : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h734 : Stmt7_3_4)
    (hin : Input8_1_2) (hM12 : Stmt7_2_1_M12) (hM23 : Stmt7_2_1_M23Code) : Stmt7_5_4 := by
  intro G _ _ T L I hyp h731 hc
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hT := hypE322_of_fsu hyp.fsu hV hN
  have h24 := hypE324_of_hyp702 hyp hV hNM
  obtain ⟨-, -, -, hn'⟩ := h734 G T L I hyp h731 hV
  obtain ⟨-, -, -, hkM, -, -, -, -, -⟩ := hn' hc
  refine ⟨fun hrow => ?_, fun hrow => ?_⟩
  ·
    have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
      h711 G T L I hyp hc (Or.inr (Or.inr (Or.inr (Or.inl hrow))))
    obtain ⟨hcard, hm2, hβ, hα, hA16⟩ := hM12 G T L I hyp hV hNM hc hrow
    obtain ⟨hEq, hm4, hw⟩ := fwci_eq_six h734 hin h325 hyp h731 hV hN hNM hTL
      (hkM (Or.inl hrow)) hm2 hβ hα
    obtain ⟨g, hg⟩ := exists_isWOffenderAt hV hT (by rw [hw]; simp)
    obtain ⟨hrkA, hcardA, hA2, hW, hWxi⟩ := offender_xiV hV hT h24 hg hEq hm4
    obtain ⟨hfix3, hxi8⟩ := hA16 _ (autI_mono hV le_top) hA2 hcardA
    have hcardI : Nat.card (IntMod (fsuV T I) hV) = 2 ^ 10 := hcard
    have hxi2 : rkIdx (Mathieu.xiV (autI hV (conjSubgroup (fsuV T I) g ⊓
        Subgroup.normalizer (fsuV T I : Set G)))) ≤ 2 := by
      have h1 := SL3Pair.card_eq_two_pow_sub_rkIdx hcardI (Mathieu.xiV (autI hV
        (conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G))))
      rw [h1] at hxi8
      have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hxi8
      omega
    rw [hw] at hW
    have hW2 : rkIdx (gammaCheck 3 (autI hV (conjSubgroup (fsuV T I) g ⊓
        Subgroup.normalizer (fsuV T I : Set G)))) = 2 := by
      have : 2 ≤ rkIdx (gammaCheck 3 (autI hV (conjSubgroup (fsuV T I) g ⊓
          Subgroup.normalizer (fsuV T I : Set G)))) := by exact_mod_cast hW
      omega
    have hVg : IsElemAbelian 2 (conjSubgroup (fsuV T I) g) := isElemAbelian_conjSubgroup hV g
    have hrk3 : rk ↥(autI hV (conjSubgroup (fsuV T I) g ⊓
        Subgroup.normalizer (fsuV T I : Set G))) - 1 = 3 := by
      rw [hrkA]
    obtain ⟨-, hWeq, -, hrkW⟩ := e3_31_two_eq hV hVg hT h24 hg hEq
      (by rw [hrk3, hw, hW2] <;> simp)
    rw [hrk3] at hWeq
    have hcardW : 2 ^ 8 ≤ Nat.card ↥(fsuV T I ⊓
        Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G)) := by
      rw [← hWeq, Subgroup.card_map_of_injective (E3.valHom_injective hV),
        SL3Pair.card_eq_two_pow_sub_rkIdx hcardI, hW2] <;> norm_num
    have hBN : fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) ≤
        Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := inf_le_right
    have hAN : conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G) ≤
        Subgroup.normalizer (fsuV T I : Set G) := inf_le_right
    have hC : Nat.card ↥(fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) ⊓
        Subgroup.centralizer (conjSubgroup (fsuV T I) g : Set G)) ≤ 2 ^ 3 := by
      refine le_trans (Subgroup.card_le_of_le ?_) ((card_fixV_autI hV hAN).symm.trans_le hfix3)
      intro v hv
      refine ⟨hv.1.1, ?_⟩
      exact Subgroup.centralizer_le (fun a ha => ha.1) hv.2
    have hprod := card_autI_mul_card_inf hVg hBN
    have hpgW := E3.isPGroup_of_isElemAbelian2 (isElemAbelian2_autI hVg
      (B2F.isElemAbelian_mono inf_le_left hV) hBN)
    have hcW := card_eq_two_pow_of_isPGroup hpgW
    rw [hrkW, hm4] at hcW
    rw [hcW] at hprod
    have : 2 ^ 8 ≤ 2 ^ 4 * 2 ^ 3 := by
      calc 2 ^ 8 ≤ _ := hcardW
        _ = _ := hprod.symm
        _ ≤ 2 ^ 4 * 2 ^ 3 := Nat.mul_le_mul_left _ hC
    norm_num at this
  ·
    have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
      h711 G T L I hyp hc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        hrow))))))))
    obtain ⟨hm2, hβ, hα, hA16⟩ := hM23 G T L I hyp hV hNM hc hrow
    obtain ⟨hEq, hm4, hw⟩ := fwci_eq_six h734 hin h325 hyp h731 hV hN hNM hTL
      (hkM (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hrow)))))) hm2 hβ hα
    obtain ⟨g, hg⟩ := exists_isWOffenderAt hV hT (by rw [hw]; simp)
    obtain ⟨-, hcardA, hA2, hW, hWxi⟩ := offender_xiV hV hT h24 hg hEq hm4
    have hxi1 := hA16 _ (autI_mono hV le_top) hA2 hcardA
    rw [hw] at hW
    have : (2 : ℕ∞) ≤ (1 : ℕ∞) := hW.trans (by exact_mod_cast hWxi.trans hxi1)
    norm_num at this

end CFSG.Quasithin.H13
