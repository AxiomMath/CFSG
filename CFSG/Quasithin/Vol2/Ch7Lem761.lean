module

public import CFSG.Quasithin.Vol2.Ch7NotFF
public import CFSG.Quasithin.Background.HSL3One

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

@[expose] def Stmt7_7_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711SL3Pair T L I 1 → (2 : ℕ∞) < rParam (fsuV T I)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem rkIdx_gammaCheck_le_one {W : Type*} [CommGroup W] [Finite W] (hW : Nat.card W = 2 ^ 6)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelian2 E) (hE4 : Nat.card E = 4) {x y : MulAut W}
    (hxE : x ∈ E) (hyE : y ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (h32 : 2 ^ 5 ≤ Nat.card ↥(fixV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers y))) :
    rkIdx (gammaCheck 1 E) ≤ 1 := by
  have hpg : IsPGroup 2 ↥E := E3.isPGroup_of_isElemAbelian2 hE
  have hindex : ∀ z ∈ E, z ≠ 1 → mQuot E (Subgroup.zpowers z) ≤ 1 := by
    intro z hzE hz1
    have hzz : z * z = 1 := by
      rw [← sq]
      exact hE.2 z hzE
    have hm := E3.card_eq_two_pow_mul hpg (Subgroup.zpowers_le.mpr hzE)
    rw [SL3One.card_zpowers_eq_two hzz hz1, hE4] at hm
    by_contra h
    push Not at h
    have h4 : 4 ≤ 2 ^ mQuot E (Subgroup.zpowers z) :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hle : fixV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers y) ≤ gammaCheck 1 E := by
    unfold gammaCheck
    refine sup_le ?_ ?_
    · exact le_iSup_of_le (Subgroup.zpowers x) (le_iSup_of_le (Subgroup.zpowers_le.mpr hxE)
        (le_iSup_of_le (hindex x hxE hx1) le_rfl))
    · exact le_iSup_of_le (Subgroup.zpowers y) (le_iSup_of_le (Subgroup.zpowers_le.mpr hyE)
        (le_iSup_of_le (hindex y hyE hy1) le_rfl))
  have hcard := (h32.trans (Subgroup.card_le_of_le hle))
  rw [SL3Pair.card_eq_two_pow_sub_rkIdx hW] at hcard
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
  omega

theorem offender_le_autL_761 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h734 : Stmt7_3_4) (h771 : Stmt7_7_1) (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711SL3Pair T L I 1)
    (hV : IsElemAbelian 2 (fsuV T I)) :
    wParam T (fsuV T I) = 1 ∧ rParam (fsuV T I) = 3 ∧ CFSG.Open.pRank 2 (autI hV ⊤) = 2 ∧
      ∀ g : G, IsWOffenderAt T (fsuV T I) g →
        Nat.card ↥(autI hV (conjSubgroup (fsuV T I) g ⊓
            Subgroup.normalizer (fsuV T I : Set G))) = 4 ∧
          autI hV (conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G)) ≤
            autI hV (fsuL0 T L) := by
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφN, hinf, hsup, hniso⟩ := exists_twist hV hN hNM htw
  have hL3 : BinaryNaturalSL (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥
      3 1 := hnat
  obtain ⟨hcard, hm2, hm2', hm3, ha1, hE4⟩ := SL3One.H4_SL3One hL3 hφN hinf hsup hniso
    (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)
  have hT := hypE322_of_fsu hyp.fsu hV hN
  have h24 := hypE324_of_hyp702 hyp hV hNM
  have hr2 := h771 G T L I hyp h731 inferInstance ⟨htw, hnat⟩
  have hr3 : (3 : ℕ∞) ≤ rParam (fsuV T I) := by
    have h := Order.add_one_le_of_lt hr2
    norm_num at h
    exact h
  obtain ⟨-, hwn, -, hn'⟩ := h734 G T L I hyp h731 hV
  have hk : nPrime (autI hV ⊤) = 1 := (hn' inferInstance).2.2.2.2.1 1 ⟨htw, hnat⟩
  have hw1 : wParam T (fsuV T I) ≤ 1 := by
    rw [hk] at hwn
    exact_mod_cast hwn
  have h732 : (mParam (autI hV ⊤) : ℕ∞) ≤ rParam (fsuV T I) := by
    have h : (mParam (autI hV ⊤) : ℕ∞) ≤ 3 := by exact_mod_cast hm3
    exact h.trans hr3
  have hw0 := lemma_7_3_3 hyp hV hN h732 (by omega)
  have hw1' : (1 : ℕ∞) ≤ wParam T (fsuV T I) := by
    refine le_trans ?_ hw0
    exact_mod_cast (by omega : 1 ≤ mParam (autI hV ⊤) - aParam (autI hV ⊤))
  have hw : wParam T (fsuV T I) = 1 := le_antisymm hw1 hw1'
  have hfw := lemma_7_5_1 hyp hV hN hNM
  rw [hw] at hfw
  have hr3' : rParam (fsuV T I) ≤ 3 := hfw.trans (by
    exact_mod_cast (by omega : CFSG.Open.pRank 2 (autI hV ⊤) + 1 ≤ 3))
  have hr : rParam (fsuV T I) = 3 := le_antisymm hr3' hr3
  have hm22 : CFSG.Open.pRank 2 (autI hV ⊤) = 2 := by
    have h := hfw
    rw [hr] at h
    have : 3 ≤ CFSG.Open.pRank 2 (autI hV ⊤) + 1 := by exact_mod_cast h
    omega
  have hEq : rParam (fsuV T I) =
      ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T (fsuV T I) := by
    rw [hr, hm22, hw]
    norm_num
  refine ⟨hw, hr, hm22, fun g hg => ?_⟩
  have hVg : IsElemAbelian 2 (conjSubgroup (fsuV T I) g) := isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 (conjSubgroup (fsuV T I) g ⊓
      Subgroup.normalizer (fsuV T I : Set G)) := B2F.isElemAbelian_mono inf_le_left hVg
  have hAN : conjSubgroup (fsuV T I) g ⊓ Subgroup.normalizer (fsuV T I : Set G) ≤
      Subgroup.normalizer (fsuV T I : Set G) := inf_le_right
  have hA2 := isElemAbelian2_autI hV hAel hAN
  obtain ⟨hrkA, -⟩ := e3_31_one_core hV hT h24 hg hEq
  rw [hm22] at hrkA
  have hcardA : Nat.card ↥(autI hV (conjSubgroup (fsuV T I) g ⊓
      Subgroup.normalizer (fsuV T I : Set G))) = 4 :=
    (card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hA2)).trans
      (by rw [hrkA] <;> norm_num)
  have h21 : rk ↥(autI hV (conjSubgroup (fsuV T I) g ⊓
      Subgroup.normalizer (fsuV T I : Set G))) - 1 = 1 := by rw [hrkA] <;> norm_num
  refine ⟨hcardA, ?_⟩
  by_contra hAH
  obtain ⟨hfix4, x, hxA, y, hyA, hxH, hx1, hyH, h32⟩ :=
    hE4 _ (autI_mono hV le_top) hA2 hcardA hAH
  have hy1 : y ≠ 1 := fun h => hyH (h ▸ Subgroup.one_mem _)
  have hW1 := rkIdx_gammaCheck_le_one hcard hA2 hcardA hxA hyA hx1 hy1 h32
  have hW2 := e3_31_two_ge hV hT h24 hg hEq
  rw [h21, hw] at hW2
  have hW : rkIdx (gammaCheck 1 (autI hV (conjSubgroup (fsuV T I) g ⊓
      Subgroup.normalizer (fsuV T I : Set G)))) = 1 := by
    have : 1 ≤ rkIdx (gammaCheck 1 (autI hV (conjSubgroup (fsuV T I) g ⊓
        Subgroup.normalizer (fsuV T I : Set G)))) := by exact_mod_cast hW2
    omega
  obtain ⟨-, hWeq, -, hrkW⟩ := e3_31_two_eq hV hVg hT h24 hg hEq (by rw [h21, hw, hW] <;> simp)
  rw [h21] at hWeq
  have hcardW : 2 ^ 5 ≤ Nat.card ↥(fsuV T I ⊓
      Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G)) := by
    rw [← hWeq, Subgroup.card_map_of_injective (E3.valHom_injective hV),
      SL3Pair.card_eq_two_pow_sub_rkIdx hcard, hW]
    all_goals norm_num
  have hBN : fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) ≤
      Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := inf_le_right
  have hC : Nat.card ↥(fsuV T I ⊓ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) ⊓
      Subgroup.centralizer (conjSubgroup (fsuV T I) g : Set G)) ≤ 4 := by
    refine le_trans (Subgroup.card_le_of_le ?_) ((card_fixV_autI hV hAN).symm.trans_le hfix4)
    intro v hv
    refine ⟨hv.1.1, ?_⟩
    exact Subgroup.centralizer_le (fun a ha => ha.1) hv.2
  have hprod := card_autI_mul_card_inf hVg hBN
  have hpgW := E3.isPGroup_of_isElemAbelian2 (isElemAbelian2_autI hVg
    (B2F.isElemAbelian_mono inf_le_left hV) hBN)
  have hcW := card_eq_two_pow_of_isPGroup hpgW
  rw [hrkW, hm22] at hcW
  rw [hcW] at hprod
  have : 2 ^ 5 ≤ 2 ^ 2 * 4 := by
    calc 2 ^ 5 ≤ _ := hcardW
      _ = _ := hprod.symm
      _ ≤ 2 ^ 2 * 4 := Nat.mul_le_mul_left _ hC
  norm_num at this

end CFSG.Quasithin.H13
