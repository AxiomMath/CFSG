module

public import CFSG.Quasithin.Vol2.Ch10SecD33B
public import CFSG.Quasithin.Vol2.Ch10SecD211

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem concl10_2_4_Kz (hW : FactSymFiveWrTwo) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1023 : Stmt10_2_3) (h1024 : Stmt10_2_4)
    (h10213 : Stmt10_2_13) (h1032 : Stmt10_3_2) (hMax : FactMaxP) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) :
    Concl10_2_4TwoThree T (Kz T L (v₁ * v₂)) (Subgroup.centralizer ({v₁ * v₂} : Set G)) := by
  have hTz := T_le_centralizer_z h37 h38 h h3 hc hd
  have hXGz : Xz T L (v₁ * v₂) ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hPX := oTwoUpper_P_eq (T := T) (L := L) h.fsu.sylow.1 (z := v₁ * v₂)
  have hKP : KOf ((fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G))
      (Subgroup.centralizer ({v₁ * v₂} : Set G)) = Kz T L (v₁ * v₂) := by
    rw [KOf, hPX]
  have hH : InH (oTwoUpper ((fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G)) ⊔ T)
      (Subgroup.centralizer ({v₁ * v₂} : Set G)) :=
    ⟨sup_le (hPX ▸ hXGz) hTz, pCoreOf_Gz_ne_bot h37 h38 h hc hd⟩
  have h4 := h1024 G T L I h h3.1 (not_case10_1_1Five h3 hc) _
    (hMax G T L I h h3 hc t v₁ v₂ hd) (le_inf le_sup_right hTz) _ hH
  rcases h4 with h4 | h4 | h4
  · exfalso
    apply not_Kz_le_fsuM hW h37 h38 h1023 h10213 h1032 h h3 hc hd
    rw [← hKP, h4, hPX]
    exact (oTwoUpper_le _).trans (inf_le_left.trans (SecA.fsuL0_le_fsuM T L))
  · exact concl10_2_4_of_eq hKP (Or.inl h4)
  · exact concl10_2_4_of_eq hKP (Or.inr h4)

theorem exists_isHStar_le_KzT (hW : FactSymFiveWrTwo) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1023 : Stmt10_2_3) (h10213 : Stmt10_2_13)
    (h1032 : Stmt10_3_2) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) :
    ∃ H : Subgroup G, IsHStar T (fsuM T L) H ∧ H ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) ∧
      oTwoUpper H ≤ Kz T L (v₁ * v₂) ∧ H ≤ Kz T L (v₁ * v₂) ⊔ T ∧
      Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) := by
  obtain ⟨H, hH, hHz⟩ := exists_isHStar_le_centralizer h37 h38 h1032 h h3 hc hd
  have hO := oTwoUpper_le_Kz hW h1023 h10213 h h3 hc hd hH hHz
  have hn := (h10213 G T L I h).2.2 H hH
  obtain ⟨-, -, h3', -⟩ := h1023 G T L I h H hH (by rw [hn]; norm_num)
  obtain ⟨-, -, he⟩ := h3' h3.1
  refine ⟨H, hH, hHz, hO, ?_, he⟩
  rw [← oTwoUpper_sup_eq (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hH.1.1)]
  exact sup_le_sup_right hO T

theorem card_symFiveWrTwo : Nat.card SymFiveWrTwo = 28800 := by
  rw [RegularWreathProduct.card, Nat.card_perm, Nat.card_eq_fintype_card (α := Multiplicative _)]
  simp [Fintype.card_fin, Nat.factorial]

theorem twentyFive_dvd_card (hW : FactSymFiveWrTwo) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1023 : Stmt10_2_3) (h10213 : Stmt10_2_13)
    (h1032 : Stmt10_3_2) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) :
    25 ∣ Nat.card (↥(Kz T L (v₁ * v₂) ⊔ T) ⧸ CFSG.pCore 2 ↥(Kz T L (v₁ * v₂) ⊔ T)) := by
  obtain ⟨H, -, -, -, hHK, ⟨e⟩⟩ := exists_isHStar_le_KzT hW h37 h38 h1023 h10213 h1032 h h3 hc hd
  have h1 : 25 ∣ Nat.card ↥H := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H)
    rw [Nat.card_congr e.toEquiv, card_symFiveWrTwo] at this
    rw [this]
    exact Dvd.dvd.mul_right (by norm_num) _
  have h2 : Nat.card ↥H ∣ Nat.card ↥(Kz T L (v₁ * v₂) ⊔ T) := Subgroup.card_dvd_of_le hHK
  have h3' := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.pCore 2 ↥(Kz T L (v₁ * v₂) ⊔ T))
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Kz T L (v₁ * v₂) ⊔ T)))
  rw [hn] at h3'
  have h4 := h1.trans h2
  rw [h3'] at h4
  exact (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 25 2)).dvd_of_dvd_mul_right h4

theorem not_case_three_Kz (hW : FactSymFiveWrTwo) (hAut : FactAutSL)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1023 : Stmt10_2_3)
    (h10213 : Stmt10_2_13) (h1032 : Stmt10_3_2) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂) (k : ℕ)
    (hk : k = 4 ∨ k = 5)
    (e : ↥(Kz T L (v₁ * v₂) ⊔ T) ⧸ CFSG.pCore 2 ↥(Kz T L (v₁ * v₂) ⊔ T) ≃*
      MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))) : False := by
  have h25 := twentyFive_dvd_card hW h37 h38 h1023 h10213 h1032 h h3 hc hd
  rw [Nat.card_congr e.toEquiv, hAut k hk] at h25
  rcases hk with rfl | rfl
  · rw [Matrix.card_SL_field] at h25
    simp [Fin.prod_univ_four] at h25
  · rw [Matrix.card_SL_field] at h25
    simp [Fin.prod_univ_five] at h25

end CFSG.Quasithin.Vol2.Ch10.SecD
