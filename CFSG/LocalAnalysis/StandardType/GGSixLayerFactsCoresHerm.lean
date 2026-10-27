module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresHermField
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresAlt
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {D : Type} [Field D] {f d : ℕ}

theorem toLin_mem_sesqUnitaryGroup_gramForm_iff (hE : UnitaryFieldData 2 f D)
    (G : Matrix (Fin d) (Fin d) D) (g : GL (Fin d) D) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqUnitaryGroup (gramForm hE G) ↔
      ((g : Matrix (Fin d) (Fin d) D).map hE.bar)ᵀ * G * g = G := by
  rw [mem_sesqUnitaryGroup, Matrix.GeneralLinearGroup.coe_toLin, ← gramForm_isometry_iff]
  rfl

theorem map_toLin_eq_sesqUnitaryGroup (hE : UnitaryFieldData 2 f D) (G : Matrix (Fin d) (Fin d) D)
    {U : Subgroup (GL (Fin d) D)}
    (hU : ∀ g : GL (Fin d) D, g ∈ U ↔ ((g : Matrix (Fin d) (Fin d) D).map hE.bar)ᵀ * G * g = G) :
    U.map (Matrix.GeneralLinearGroup.toLin : GL (Fin d) D ≃*
      LinearMap.GeneralLinearGroup D (Fin d → D)).toMonoidHom =
      sesqUnitaryGroup (gramForm hE G) := by
  ext g'
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (toLin_mem_sesqUnitaryGroup_gramForm_iff hE G g).mpr ((hU g).mp hg)
  · intro hg'
    refine ⟨Matrix.GeneralLinearGroup.toLin.symm g', (hU _).mpr ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [← toLin_mem_sesqUnitaryGroup_gramForm_iff, MulEquiv.apply_symm_apply]
    exact hg'

theorem map_toLin_gramSU (hE : UnitaryFieldData 2 f D) (G : Matrix (Fin d) (Fin d) D) :
    (gramSU hE G).map (Matrix.GeneralLinearGroup.toLin : GL (Fin d) D ≃*
      LinearMap.GeneralLinearGroup D (Fin d → D)).toMonoidHom =
      sesqSpecialUnitaryGroup (gramForm hE G) := by
  ext g'
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff hE G g).mpr hg
  · intro hg'
    refine ⟨Matrix.GeneralLinearGroup.toLin.symm g', ?_, MulEquiv.apply_symm_apply _ _⟩
    show Matrix.GeneralLinearGroup.toLin.symm g' ∈ gramSU hE G
    rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, MulEquiv.apply_symm_apply]
    exact hg'

theorem card_primeFactors_small {n : ℕ} (hn : n = 18 ∨ n = 648) : n.primeFactors.card ≤ 2 := by
  rcases hn with rfl | rfl
  · rw [show (18 : ℕ) = 2 * 3 ^ 2 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three,
      Nat.Prime.primeFactors Nat.prime_two]
    decide
  · rw [show (648 : ℕ) = 2 ^ 3 * 3 ^ 4 by norm_num,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
    decide


theorem hermCoreInput_holds : HermCoreInput := by
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
  have hmapU := map_toLin_eq_sesqUnitaryGroup hE G hU
  have hSU : gramSU hE G ≤ matUnitary hT := fun g hg => (hU g).mpr hg.1
  have hq2 : 2 ≤ 2 ^ f' := by
    have := Nat.one_lt_two_pow (n := f') (by have := hE.one_le; omega)
    omega
  have hcard : Nat.card D = (2 ^ f') ^ 2 := hE.card_eq_sq
  by_cases hgood : 2 ≤ d ∧ ¬ (d ≤ 3 ∧ Nat.card D = 4)
  · have hq4 : d ≤ 3 → 4 ≤ 2 ^ f' := by
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
    refine ⟨gramSU hE G, hSU, fun u hu s hs => ⟨(hU _).mp (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hu (hSU hs)) (Subgroup.inv_mem _ hu)), ?_⟩, ⟨1, fun x hx => ?_⟩,
      Or.inr ⟨?_, fun z hz hzc hz2 => ?_⟩⟩
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hs.2, mul_one, ← det_mul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    · have hxU : x ∈ matUnitary hT := Subgroup.commutator_le_self _ hx
      have hxdet : x ∈ (Matrix.GeneralLinearGroup.det : GL (Fin d) D →* Dˣ).ker :=
        ((Subgroup.commutator_mono le_top le_top).trans
          (Abelianization.commutator_subset_ker _)) hx
      refine ⟨(hU x).mp hxU, ?_⟩
      rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply] at hxdet
      exact hxdet
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (((gramSU hE G).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
          (MulEquiv.subgroupCongr (map_toLin_gramSU hE G))).symm hq
    · obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KCUnitary.exists_smul_of_commute_special_unitary hE
        hBs hBl (by rw [hfr]; exact hgood.1) hq2 _ fun δ hδ => by
          rw [← map_toLin_gramSU] at hδ
          obtain ⟨u, hu, rfl⟩ := hδ
          have h2 : Matrix.GeneralLinearGroup.toLin z * Matrix.GeneralLinearGroup.toLin u =
              Matrix.GeneralLinearGroup.toLin u * Matrix.GeneralLinearGroup.toLin z := by
            rw [← map_mul, ← map_mul, hzc u hu]
          exact congrArg Units.val h2
      exact eq_one_of_smul_one (eq_smul_one_of_toLin hc) hz2
  · apply hasCore_of_isSolvable
    by_cases hd1 : d = 1
    · subst hd1
      have : Group.IsSolvable (GL (Fin 1) D) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 1 D
          (Or.inl rfl)
      infer_instance
    have hd23 : d = 2 ∨ d = 3 := by omega
    have hD4 : Nat.card D = 4 := by
      by_contra h
      exact hgood ⟨by omega, fun h' => h h'.2⟩
    have hq : 2 ^ f' = 2 := by
      rw [hcard] at hD4
      nlinarith
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

end LayerCores

end CFSG.StandardType
