module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresHerm
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsBlock
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock

public section

namespace CFSG.StandardType.A6Red.CoreShape

open Matrix CFSG.StandardType.LayerCores
open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

private theorem hasCoreLie_of_isSolvable {G : Type} [Group G] {U : Subgroup G}
    (hU : Group.IsSolvable U) : HasCoreLie U := by
  obtain ⟨k, hk⟩ := exists_ggDer_eq_bot hU
  refine ⟨⊥, bot_le, fun u _ s hs => ?_, ⟨k, hk.le⟩, Or.inl rfl⟩
  rw [Subgroup.mem_bot.mp hs, mul_one, mul_inv_cancel]
  exact Subgroup.one_mem _

private theorem gga6_gramSU {D : Type} [Field D] [Finite D] [CharP D 2] {f d : ℕ}
    (hE : UnitaryFieldData 2 f D) (G : Matrix (Fin d) (Fin d) D)
    (hG : (G.map hE.bar)ᵀ = G) (hGdet : G.det ≠ 0)
    (hgood : 2 ≤ d ∧ ¬ (d ≤ 3 ∧ Nat.card D = 4)) :
    GGA6CharTwoLie ↥(gramSU hE G) := by
  classical
  have hBs : (gramForm hE G).IsSymm := gramForm_isSymm hE hG
  have hBl : (gramForm hE G).SeparatingLeft := gramForm_separatingLeft hE hGdet
  have hfr : Module.finrank D (Fin d → D) = d := Module.finrank_fin_fun D
  let eG : ↥(gramSU hE G) ≃* sesqSpecialUnitaryGroup (gramForm hE G) :=
    ((gramSU hE G).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
      (MulEquiv.subgroupCongr (map_toLin_gramSU hE G))
  by_cases hd3 : 3 ≤ d
  ·
    have hmq : (d, 2 ^ f) ≠ (3, 2) := by
      intro hc
      have h1 := congrArg Prod.fst hc
      have h2 := congrArg Prod.snd hc
      simp only at h1 h2
      have hcard : Nat.card D = 4 := by rw [hE.card_eq_sq, h2]; norm_num
      exact hgood.2 ⟨by omega, hcard⟩
    obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hBs hBl
    obtain ⟨ι⟩ :=
      CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
        (G := (1 : Matrix (Fin (Module.finrank D (Fin d → D)))
                (Fin (Module.finrank D (Fin d → D))) D))
        (fun i j => by rw [hb i j, Matrix.one_apply])
    let eU : ↥(gramSU hE G) ≃* ↥(unitarySU 2 f D (Module.finrank D (Fin d → D))) :=
      (eG.trans ι).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
    have hLS := SUFacts.lieModel_quotient_center_of_mulEquiv_unitarySU hE
      (by rw [hfr]; exact hd3) (by rw [hfr]; exact hmq) eU
    rw [hfr] at hLS
    exact ⟨.PSU, d, f, hLS⟩
  ·
    have hd2 : d = 2 := by omega
    have hf2 : 2 ≤ f := by
      have h1 := hE.one_le
      by_contra hlt
      have hf1 : f = 1 := by omega
      have : Nat.card D = 4 := by rw [hE.card_eq_sq, hf1]; norm_num
      exact hgood.2 ⟨by omega, this⟩
    obtain ⟨σ⟩ :=
      CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hBs hBl
        (by rw [hfr, hd2])
    let e : ↥(gramSU hE G) ≃* SpecialLinearGroup (Fin 2) hE.fixedField := eG.trans σ
    have hadm : StatedLieAdmissible .PSL 2 2 f := by
      refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
      · intro hc
        simp only [Prod.mk.injEq] at hc
        exact absurd hc.2 (by
          intro h2
          have h1 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
          rw [h2] at h1
          norm_num at h1)
      · intro hc
        simp only [Prod.mk.injEq] at hc
        have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
        rw [hc.2] at h2
        norm_num at h2
    have hcardF : Nat.card hE.fixedField = 2 ^ f := hE.card_fixedField
    have hmodel : StatedClassicalModel
        (↥(gramSU hE G) ⧸ Subgroup.center ↥(gramSU hE G)) .PSL 2 2 f := by
      refine ⟨hadm, hE.fixedField, inferInstance, inferInstance, hcardF, ?_⟩
      exact ⟨(QuotientGroup.congr (Subgroup.center (gramSU hE G))
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) hE.fixedField)) e
          (Subgroup.map_center_eq e)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 hE.fixedField)⟩
    exact ⟨.PSL, 2, f, Or.inl ⟨by decide, hmodel⟩⟩

theorem hermCoreInputLie_holds : HermCoreInputLie := by
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
    let eG : ↥(gramSU hE G) ≃* sesqSpecialUnitaryGroup (gramForm hE G) :=
      ((gramSU hE G).equivMapOfInjective _ Matrix.GeneralLinearGroup.toLin.injective).trans
        (MulEquiv.subgroupCongr (map_toLin_gramSU hE G))
    have hqG : CFSG.IsQuasisimple (gramSU hE G) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eG.symm hq
    refine ⟨gramSU hE G, hSU, fun u hu s hs => ⟨(hU _).mp (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hu (hSU hs)) (Subgroup.inv_mem _ hu)), ?_⟩, ⟨1, fun x hx => ?_⟩,
      Or.inr ⟨?_, fun z hz hzc hz2 => ?_, ?_⟩⟩
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
    · exact gga6_gramSU hE G hG hGdet hgood
  · apply hasCoreLie_of_isSolvable
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

end CFSG.StandardType.A6Red.CoreShape

end
