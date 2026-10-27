module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveProofSp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClHerm
public import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

namespace FieldFiveSU

open CFSG.Assembly Matrix LayerCores LayerFacts ClNonsplit CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem five_dvd_unitary_order {d : ℕ} (hd : 4 ≤ d) :
    (5 : ℤ) ∣ ((2 : ℕ) : ℤ) ^ (d * (d - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 d, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have h4 : (4 : ℕ) ∈ Finset.Icc 2 d := Finset.mem_Icc.mpr ⟨by norm_num, hd⟩
  have h15 := Finset.dvd_prod_of_mem (fun i => (((2 : ℕ) : ℤ) ^ i - (-1) ^ i)) h4
  have h5 : (5 : ℤ) ∣ ((2 : ℕ) : ℤ) ^ 4 - (-1) ^ 4 := ⟨3, by norm_num⟩
  exact (h5.trans h15).mul_left _

theorem eq_one_of_pow_five_of_card_four {D : Type} [Field D] [Finite D] (hD : Nat.card D = 4)
    {c : D} (hc : c ^ 5 = 1) : c = 1 := by
  classical
  have := Fintype.ofFinite D
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hc
    exact zero_ne_one hc
  have h3 : c ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [← Nat.card_eq_fintype_card, hD] at h
  have h2 : c ^ 2 = 1 := by
    have e : c ^ 5 = c ^ 3 * c ^ 2 := by ring
    rw [e, h3, one_mul] at hc
    exact hc
  calc c = c ^ 3 * (c ^ 2)⁻¹ := by
        rw [show c ^ 3 = c ^ 2 * c by ring, mul_comm (c ^ 2) c, mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero 2 hc0), mul_one]
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

theorem herm_core_facts {D : Type} [Field D] [Finite D] [CharP D 2] {d : ℕ}
    {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D} (hT : IsInvol T)
    (hk : ∃ c : D, T (Matrix.scalar (Fin d) c) ≠ Matrix.scalar (Fin d) c)
    (hD4 : Nat.card D = 4) {S : Subgroup (GL (Fin d) D)} (hSU : S ≤ matUnitary hT)
    (hder : ∃ k, LayerFacts.ggDer (matUnitary hT) k ≤ S) (hq : CFSG.IsQuasisimple S) :
    (∀ g : GL (Fin d) D, g ^ 5 = 1 → (∀ s ∈ S, g * s = s * g) → g = 1) ∧
      5 ∣ Nat.card S := by
  classical
  obtain ⟨kS, hkS⟩ := hder
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
  obtain ⟨μ, hμ0, hμ⟩ := LayerCores.exists_hilbert90 ρ hρ2 hρ1 hl
  set Hm : Matrix (Fin d) (Fin d) D := μ • (H : Matrix (Fin d) (Fin d) D) with hHmdef
  have hct : ∀ z : Matrix (Fin d) (Fin d) D, (z.map hE.bar)ᵀ = ct ρ z := fun z => by
    rw [show (⇑hE.bar : D → D) = ⇑ρ from funext hbar]
    rfl
  have hHm : (Hm.map hE.bar)ᵀ = Hm := by
    rw [hct, hHmdef, ct_smul, hlH, smul_smul, hμ]
  have hHdet : (H : Matrix (Fin d) (Fin d) D).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp H.isUnit).ne_zero
  have hHmdet : Hm.det ≠ 0 := by
    rw [hHmdef, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hμ0) hHdet
  have hMMi : (H : Matrix (Fin d) (Fin d) D) * ((H⁻¹ : GL (Fin d) D) :
      Matrix (Fin d) (Fin d) D) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
      (H : Matrix (Fin d) (Fin d) D) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hU : ∀ g : GL (Fin d) D, g ∈ matUnitary hT ↔
      ((g : Matrix (Fin d) (Fin d) D).map hE.bar)ᵀ * Hm * g = Hm := by
    intro g
    rw [mem_matUnitary, hH, hct, hHmdef, Matrix.mul_smul, Matrix.smul_mul]
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
  have hBs : (gramForm hE Hm).IsSymm := gramForm_isSymm hE hHm
  have hBl : (gramForm hE Hm).SeparatingLeft := gramForm_separatingLeft hE hHmdet
  have hfr : Module.finrank D (Fin d → D) = d := Module.finrank_fin_fun D
  have hmapU := map_toLin_eq_sesqUnitaryGroup hE Hm hU
  have hcard : Nat.card D = (2 ^ f') ^ 2 := hE.card_eq_sq
  have hq2 : 2 ^ f' = 2 := by
    have h1 : (2 ^ f') ^ 2 = 2 ^ 2 := by rw [← hcard, hD4]; norm_num
    exact Nat.pow_left_injective (by norm_num) h1
  have hq2' : 2 ≤ 2 ^ f' := hq2.ge
  by_cases hgood : 4 ≤ d
  · have hqSU := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE
      hBs hBl (by rw [hfr]; omega)
      ⟨fun h => by rw [hfr] at h; omega, fun h => by rw [hfr] at h; omega⟩
    let eG : ↥(gramSU hE Hm) ≃* sesqSpecialUnitaryGroup (gramForm hE Hm) :=
      ((gramSU hE Hm).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
        (MulEquiv.subgroupCongr (map_toLin_gramSU hE Hm))
    have hqG : CFSG.IsQuasisimple (gramSU hE Hm) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eG.symm hqSU
    have hSU' : gramSU hE Hm ≤ matUnitary hT := fun g hg => (hU g).mpr hg.1
    have hGS : gramSU hE Hm ≤ S :=
      le_of_ggDer_le (LayerFacts.ggCommutator_eq_of_isQuasisimple hqG) hSU' hkS
    have hSG : S ≤ gramSU hE Hm := by
      intro g hg
      have hg' : g ∈ ⁅S, S⁆ := by rw [LayerFacts.ggCommutator_eq_of_isQuasisimple hq]; exact hg
      have hgdet : g ∈ (Matrix.GeneralLinearGroup.det : GL (Fin d) D →* Dˣ).ker :=
        ((Subgroup.commutator_mono le_top le_top).trans
          (Abelianization.commutator_subset_ker _)) hg'
      rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply,
        Units.val_one] at hgdet
      exact ⟨(hU g).mp (hSU hg), hgdet⟩
    have hSeq : S = gramSU hE Hm := le_antisymm hSG hGS
    refine ⟨fun g hg5 hgc => ?_, ?_⟩
    ·
      obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KCUnitary.exists_smul_of_commute_special_unitary hE
        hBs hBl (by rw [hfr]; omega) hq2' _ fun δ hδ => by
          rw [← map_toLin_gramSU] at hδ
          obtain ⟨u, hu, rfl⟩ := hδ
          have h2 : Matrix.GeneralLinearGroup.toLin g * Matrix.GeneralLinearGroup.toLin u =
              Matrix.GeneralLinearGroup.toLin u * Matrix.GeneralLinearGroup.toLin g := by
            rw [← map_mul, ← map_mul, hgc u (hSeq ▸ hu)]
          exact congrArg Units.val h2
      have hgc' := eq_smul_one_of_toLin hc
      have hc5 : c ^ 5 = 1 := by
        have h1 := congrArg (fun g : GL (Fin d) D => (g : Matrix (Fin d) (Fin d) D) 0 0) hg5
        simp only [Units.val_pow_eq_pow_val, hgc', Units.val_one, smul_pow, one_pow] at h1
        simpa using h1
      have hc1 := eq_one_of_pow_five_of_card_four hD4 hc5
      apply Units.ext
      rw [hgc', hc1, one_smul, Units.val_one]
    ·
      have h1 := (CFSG.LinearGroups.unitary_full_group_order hE hBs hBl hfr (by omega)).2.1
      rw [hq2] at h1
      have h2 : Nat.card S = Nat.card (sesqSpecialUnitaryGroup (gramForm hE Hm)) := by
        rw [hSeq]
        exact card_gramSU hE Hm
      have h3 : (5 : ℤ) ∣ (Nat.card S : ℤ) := by
        rw [h2, h1]
        exact five_dvd_unitary_order hgood
      exact_mod_cast h3
  ·
    exfalso
    apply not_isQuasisimple_of_le (U := matUnitary hT) _ hSU hq
    by_cases hd1 : d = 1
    · subst hd1
      have : Group.IsSolvable (GL (Fin 1) D) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 1 D
          (Or.inl rfl)
      infer_instance
    have hd23 : d = 2 ∨ d = 3 := by omega
    have hcardU : Nat.card (matUnitary hT) = 18 ∨ Nat.card (matUnitary hT) = 648 := by
      have h1 := (CFSG.LinearGroups.unitary_full_group_order hE hBs hBl hfr (by omega)).1
      have h2 : Nat.card (matUnitary hT) = Nat.card (sesqUnitaryGroup (gramForm hE Hm)) :=
        Nat.card_congr (((matUnitary hT).equivMapOfInjective _
          Matrix.GeneralLinearGroup.toLin.injective).trans
            (MulEquiv.subgroupCongr hmapU)).toEquiv
      rw [hq2] at h1
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
    exact isSolvable_of_card_primeFactors_le_two (card_primeFactors_small hcardU)

end FieldFiveSU

end CFSG.StandardType
