module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSpTag
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.StandardType

namespace LayerPDiv

open Matrix LayerCores CFSG.LocalAnalysis.ComponentInitial

theorem altFactorPDivInput_holds : AltFactorPDivInput := by
  intro D _ _ _ d T hT h1 hy
  classical
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    left
    have : Subsingleton (GL (Fin 0) D) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    infer_instance
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨H, hH⟩ := hT.exists_gram_id h1
  have hsym := transpose_gram_eq hT H hH
  obtain ⟨y, hy⟩ := hy
  have hHy := gram_eq_add_transpose H hH hsym hy
  have hB : (Matrix.toBilin' (H : Matrix (Fin d) (Fin d) D)).IsAlt := by
    have h2 := isAlt_toBilin'_add_transpose ((H : Matrix (Fin d) (Fin d) D) * y)
    rwa [← hHy] at h2
  have hn := nondegenerate_toBilin'_gram H
  have hmap := map_toLin_matUnitary H hH (hT := hT)
  let e : matUnitary hT ≃* sesqUnitaryGroup (Matrix.toBilin' (H : Matrix (Fin d) (Fin d) D)) :=
    ((matUnitary hT).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hfr : Module.finrank D (Fin d → D) = d := Module.finrank_fin_fun D
  obtain ⟨s, hs, ⟨eS⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  rw [hfr] at hs
  have hs1 : 1 ≤ s := by omega
  have hdvdU : Nat.card D ^ 2 - 1 ∣ Nat.card (matUnitary hT) := by
    rw [Nat.card_congr (e.trans eS).toEquiv, SymplecticFlag.card_statedSp]
    refine Dvd.dvd.mul_left ?_ _
    have := Finset.dvd_prod_of_mem (fun j => Nat.card D ^ (2 * j) - 1)
      (Finset.mem_Icc.2 ⟨le_rfl, hs1⟩)
    simpa using this
  have hquasi : CFSG.IsQuasisimple (sesqUnitaryGroup (Matrix.toBilin'
      (H : Matrix (Fin d) (Fin d) D))) → Group.IsSolvable (matUnitary hT) ∨
        ∃ X : Subgroup (GL (Fin d) D), X ≤ matUnitary hT ∧ ⁅X, X⁆ = X ∧
          Nat.card D ^ 2 - 1 ∣ Nat.card X := fun hq =>
    Or.inr ⟨matUnitary hT, le_rfl, LayerFacts.ggCommutator_eq_of_isQuasisimple
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq), hdvdU⟩
  rcases card_eq_two_or_four_le (D := D) with hD2 | hD4
  · by_cases h6 : 6 ≤ d
    · exact hquasi (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB
        hn (by omega) (Or.inr (Or.inr ⟨hD2, by omega⟩)))
    rcases (show d = 2 ∨ d = 4 by omega) with hd2 | hd4
    · subst hd2
      left
      have : Group.IsSolvable (GL (Fin 2) D) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 2 D
          (Or.inr ⟨rfl, Or.inl hD2⟩)
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    ·
      right
      obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hD2 hB hn
        (by rw [hfr, hd4])
      obtain ⟨hq, hodd⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (e.trans E)
      set U := matUnitary hT with hU
      let eS' : ↥(commutator ↥U) ≃* ↥⁅U, U⁆ :=
        ((commutator ↥U).equivMapOfInjective U.subtype U.subtype_injective).trans
          (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator U))
      have hqS : CFSG.IsQuasisimple ↥⁅U, U⁆ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eS' hq
      refine ⟨⁅U, U⁆, Subgroup.commutator_le_self U,
        LayerFacts.ggCommutator_eq_of_isQuasisimple hqS, ?_⟩
      rw [hD2, show (2 : ℕ) ^ 2 - 1 = 3 by norm_num] at hdvdU ⊢
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥U) 3 hdvdU
      have hwc : w ∈ commutator ↥U :=
        hodd Nat.prime_three (by norm_num) w (by rw [← hw]; exact pow_orderOf_eq_one w)
      rw [← Nat.card_congr eS'.toEquiv, ← hw]
      have h1 : orderOf (⟨w, hwc⟩ : commutator ↥U) = orderOf w :=
        Subgroup.orderOf_mk w hwc
      rw [← h1]
      exact orderOf_dvd_natCard _
  · exact hquasi (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB
      hn (by omega) (Or.inl hD4))

open CFSG.ClassicalGroups.UnitaryFlag in
theorem hermFactorPDivInput_holds : HermFactorPDivInput := by
  intro D _ _ _ d T hT hk
  classical
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exfalso
    obtain ⟨c, hc⟩ := hk
    exact hc (Subsingleton.elim _ _)
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨ρ, hρ, hρ2⟩ := hT.exists_rho
  have hρ1 : ∃ c, ρ c ≠ c := by
    obtain ⟨c, hc⟩ := hk
    exact ⟨c, fun h => hc (by rw [hρ, h])⟩
  obtain ⟨H, hH⟩ := hT.exists_gram ρ hρ hρ2
  obtain ⟨f', hE, hbar⟩ := exists_unitaryFieldData_of_invol ρ hρ2 hρ1
  obtain ⟨l, hlH, hl⟩ := exists_ct_gram_eq hT ρ hρ2 H hH
  obtain ⟨μ, hμ0, hμ⟩ := exists_hilbert90 ρ hρ2 hρ1 hl
  set G : Matrix (Fin d) (Fin d) D := μ • (H : Matrix (Fin d) (Fin d) D) with hGdef
  have hct : ∀ x : Matrix (Fin d) (Fin d) D, (x.map hE.bar)ᵀ = ct ρ x := fun x => by
    rw [show (⇑hE.bar : D → D) = ⇑ρ from funext hbar]
    rfl
  have hG : (G.map hE.bar)ᵀ = G := by
    rw [hct, hGdef, ct_smul, hlH, smul_smul, hμ]
  have hHdet : (H : Matrix (Fin d) (Fin d) D).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp H.isUnit).ne_zero
  have hGdet : G.det ≠ 0 := by
    rw [hGdef, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hμ0) hHdet
  have hMMi : (H : Matrix (Fin d) (Fin d) D) * ((H⁻¹ : GL (Fin d) D) :
      Matrix (Fin d) (Fin d) D) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
      (H : Matrix (Fin d) (Fin d) D) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hU : ∀ g : GL (Fin d) D, g ∈ matUnitary hT ↔
      ((g : Matrix (Fin d) (Fin d) D).map hE.bar)ᵀ * G * g = G := by
    intro g
    rw [mem_matUnitary, hH, hct, hGdef, Matrix.mul_smul, Matrix.smul_mul]
    constructor
    · intro h
      congr 1
      calc ct ρ (g : Matrix (Fin d) (Fin d) D) * H * g
          = H * (((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
            ((g : Matrix (Fin d) (Fin d) D).map ρ)ᵀ * H * g) := by
            simp only [← Matrix.mul_assoc, hMMi, Matrix.one_mul]
            rfl
        _ = H := by rw [h, Matrix.mul_one]
    · intro h
      have h1 : ct ρ (g : Matrix (Fin d) (Fin d) D) * H * g = H := smul_right_injective _ hμ0 h
      calc ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
            ((g : Matrix (Fin d) (Fin d) D).map ρ)ᵀ * H * g
          = ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
            (ct ρ (g : Matrix (Fin d) (Fin d) D) * H * g) := by
            simp only [Matrix.mul_assoc]
            rfl
        _ = 1 := by rw [h1, hMiM]
  have hBs : (gramForm hE G).IsSymm := gramForm_isSymm hE hG
  have hBl : (gramForm hE G).SeparatingLeft := gramForm_separatingLeft hE hGdet
  have hfr : Module.finrank D (Fin d → D) = d := Module.finrank_fin_fun D
  have hSU : gramSU hE G ≤ matUnitary hT := fun g hg => (hU g).mpr hg.1
  have hq2 : 2 ≤ 2 ^ f' := by
    have := Nat.one_lt_two_pow (n := f') (by have := hE.one_le; omega)
    omega
  have hcard : Nat.card D = (2 ^ f') ^ 2 := hE.card_eq_sq
  by_cases hgood : 2 ≤ d ∧ ¬ (d ≤ 3 ∧ Nat.card D = 4)
  · right
    have hq4 : d ≤ 3 → 4 ≤ 2 ^ f' := by
      intro h3
      have h4 : Nat.card D ≠ 4 := fun h4 => hgood.2 ⟨h3, h4⟩
      by_contra hlt
      have hf1 : f' = 1 := by
        by_contra hne
        have h2f : 2 ≤ f' := by have := hE.one_le; omega
        have : 2 ^ 2 ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) h2f
        omega
      rw [hcard, hf1] at h4
      exact h4 rfl
    have hq := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE
      hBs hBl (by rw [hfr]; exact hgood.1)
      ⟨fun h => hq4 (by rw [hfr] at h; omega), fun h => le_trans (by norm_num)
        (hq4 (by rw [hfr] at h; omega))⟩
    let eSU := ((gramSU hE G).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
      (MulEquiv.subgroupCongr (map_toLin_gramSU hE G))
    refine ⟨gramSU hE G, hSU, LayerFacts.ggCommutator_eq_of_isQuasisimple
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eSU.symm hq), ?_⟩
    have hSUcard := (CFSG.LinearGroups.unitary_full_group_order hE hBs hBl hfr (by omega)).2.1
    have h1 : 1 ≤ (2 ^ f') ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have hdvdZ : ((Nat.card D - 1 : ℕ) : ℤ) ∣ (Nat.card (gramSU hE G) : ℤ) := by
      rw [Nat.card_congr eSU.toEquiv, hSUcard]
      refine Dvd.dvd.mul_left (dvd_trans ?_
        (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨le_rfl, hgood.1⟩))) _
      rw [hcard, Nat.cast_sub h1]
      push_cast
      norm_num
    exact Int.natCast_dvd_natCast.mp hdvdZ
  · left
    by_cases hd1 : d = 1
    · subst hd1
      have : Group.IsSolvable (GL (Fin 1) D) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 1 D
          (Or.inl rfl)
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    have hd23 : d = 2 ∨ d = 3 := by omega
    have hD4 : Nat.card D = 4 := by
      by_contra h
      exact hgood ⟨by omega, fun h' => h h'.2⟩
    have hq : 2 ^ f' = 2 := by
      rw [hcard] at hD4
      nlinarith
    have hmapU := map_toLin_eq_sesqUnitaryGroup hE G hU
    have hcardU : Nat.card (matUnitary hT) = 18 ∨ Nat.card (matUnitary hT) = 648 := by
      have h1 := (CFSG.LinearGroups.unitary_full_group_order hE hBs hBl hfr (by omega)).1
      have h2 : Nat.card (matUnitary hT) = Nat.card (sesqUnitaryGroup (gramForm hE G)) :=
        Nat.card_congr (((matUnitary hT).equivMapOfInjective _
          Matrix.GeneralLinearGroup.toLin.injective).trans
            (MulEquiv.subgroupCongr hmapU)).toEquiv
      rw [hq] at h1
      rcases hd23 with rfl | rfl
      · left
        have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
        rw [h2]
        exact_mod_cast h1.trans e
      · right
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
        rw [h2]
        exact_mod_cast h1.trans e
    have : Finite (GL (Fin d) D) := inferInstance
    exact isSolvable_of_card_primeFactors_le_two (card_primeFactors_small hcardU)

end LayerPDiv

section Tags

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem ggLayerPDivTag_PSp : GGLayerPDivTag .PSp :=
  ggLayerPDivTag_PSp_of_factors LayerPDiv.altFactorPDivInput_holds
    LayerPDiv.hermFactorPDivInput_holds

theorem ggLayerPDivInput_of_remaining_eight (hPSU : GGLayerPDivTag .PSU)
    (hPlus : GGLayerPDivTag .POmegaPlus) (hMinus : GGLayerPDivTag .POmegaMinus)
    (hF4 : GGLayerPDivTag .F4) (hE6 : GGLayerPDivTag .E6) (hE7 : GGLayerPDivTag .E7)
    (hE8 : GGLayerPDivTag .E8) (hTwE6 : GGLayerPDivTag .twistedE6) : GGLayerPDivInput :=
  ggLayerPDivInput_of_remaining hPSU ggLayerPDivTag_PSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6

theorem ggSixLayerCXInput_of_pDivTags_eight (hPSU : GGLayerPDivTag .PSU)
    (hPlus : GGLayerPDivTag .POmegaPlus) (hMinus : GGLayerPDivTag .POmegaMinus)
    (hF4 : GGLayerPDivTag .F4) (hE6 : GGLayerPDivTag .E6) (hE7 : GGLayerPDivTag .E7)
    (hE8 : GGLayerPDivTag .E8) (hTwE6 : GGLayerPDivTag .twistedE6)
    (hNS : GGSixLayerCXNonsplitInput) : GGSixLayerCXInput :=
  ggSixLayerCXInput_of_split
    (ggLayerPDivInput_of_remaining_eight hPSU hPlus hMinus hF4 hE6 hE7 hE8 hTwE6) hNS

end Tags

end CFSG.StandardType
