module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresHerm
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresLinear

public section

namespace CFSG.StandardType

namespace LayerCyc

open Matrix LayerCores CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.PresentationLocal

theorem mem_center_of_commute_range_toGL {D : Type} [Field D] {m : ℕ} {z : GL (Fin m) D}
    (hzc : ∀ y ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) D →* GL (Fin m) D).range,
      z * y = y * z) : z ∈ Subgroup.center (GL (Fin m) D) := by
  have hcomm : ∀ t : TransvectionStruct (Fin m) D,
      Commute t.toMatrix (z : Matrix (Fin m) (Fin m) D) := by
    intro t
    have h1 := hzc (SpecialLinearGroup.toGL ⟨t.toMatrix, t.det⟩) ⟨_, rfl⟩
    have h3 := congrArg (fun g : GL (Fin m) D => (g : Matrix (Fin m) (Fin m) D)) h1
    simp only [Units.val_mul] at h3
    exact h3.symm
  exact GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    (Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm)

theorem hasCycCore_top_GL {D : Type} [Field D] [Finite D] [CharP D 2] (m : ℕ) :
    HasCycCore (⊤ : Subgroup (GL (Fin m) D)) := by
  by_cases hg : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset D, s.card = 4)
  · refine ⟨(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) D →* GL (Fin m) D).range,
      le_top, fun u _ s hs => ?_, ⟨1, ?_⟩, Or.inr ⟨?_, isCyclic_center_of_forall_mem_center
        fun _ _ hzc => mem_center_of_commute_range_toGL hzc⟩⟩
    · rw [SpecialLinearGroup.range_toGL_eq_ker_det] at hs ⊢
      exact (MonoidHom.normal_ker _).conj_mem s hs u
    · rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_zero, SpecialLinearGroup.range_toGL_eq_ker_det]
      exact Abelianization.commutator_subset_ker _
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective)
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hg.1 hg.2)
  · have : Group.IsSolvable (GL (Fin m) D) :=
      LayerFacts.isSolvable_of_not_goodBlock (E := fun _ : Unit => D) (m := fun _ => m)
        (b := ()) hg
    exact hasCycCore_of_isSolvable inferInstance

theorem hasCycCore_herm {D : Type} [Field D] [Finite D] [CharP D 2] {d : ℕ}
    {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D} (hT : IsInvol T)
    (hk : ∃ c : D, T (Matrix.scalar (Fin d) c) ≠ Matrix.scalar (Fin d) c) :
    HasCycCore (matUnitary hT) := by
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
      Or.inr ⟨?_, isCyclic_center_of_forall_mem_center fun z _ hzc => ?_⟩⟩
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
      exact mem_center_of_eq_smul_one (eq_smul_one_of_toLin hc)
  · apply hasCycCore_of_isSolvable
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

theorem hasCycCore_alt {D : Type} [Field D] [Finite D] [CharP D 2] {d : ℕ}
    {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D} (hT : IsInvol T)
    (h1 : ∀ c : D, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) c)
    (hy : ∃ y, y + T y = 1) : HasCycCore (matUnitary hT) := by
  classical
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : Subsingleton (GL (Fin 0) D) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    exact hasCycCore_of_isSolvable inferInstance
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
  obtain ⟨s, hs, -⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  rw [hfr] at hs
  have hquasi : CFSG.IsQuasisimple (sesqUnitaryGroup (Matrix.toBilin'
      (H : Matrix (Fin d) (Fin d) D))) → HasCycCore (matUnitary hT) := by
    intro hq
    refine ⟨matUnitary hT, le_rfl, fun u hu s hs =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hs) (Subgroup.inv_mem _ hu), ⟨0, le_rfl⟩,
      Or.inr ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq,
        isCyclic_center_of_forall_mem_center fun z _ hzc => ?_⟩⟩
    obtain ⟨c, hc⟩ :=
      CFSG.RankThree.PartOne.KCSpIsotypic.exists_smul_of_commute_sesqUnitaryGroup_alt
      hB hn _ fun g hg => by
        rw [← hmap] at hg
        obtain ⟨u, hu, rfl⟩ := hg
        have h2 : Matrix.GeneralLinearGroup.toLin z * Matrix.GeneralLinearGroup.toLin u =
            Matrix.GeneralLinearGroup.toLin u * Matrix.GeneralLinearGroup.toLin z := by
          rw [← map_mul, ← map_mul, hzc u hu]
        exact congrArg Units.val h2
    exact mem_center_of_eq_smul_one (eq_smul_one_of_toLin hc)
  rcases card_eq_two_or_four_le (D := D) with hD2 | hD4
  · by_cases h6 : 6 ≤ d
    · exact hquasi (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB hn
        (by omega) (Or.inr (Or.inr ⟨hD2, by omega⟩)))
    rcases (show d = 2 ∨ d = 4 by omega) with hd2 | hd4
    · subst hd2
      have : Group.IsSolvable (GL (Fin 2) D) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 2 D
          (Or.inr ⟨rfl, Or.inl hD2⟩)
      exact hasCycCore_of_isSolvable inferInstance
    ·
      obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hD2 hB hn (by rw [hfr, hd4])
      obtain ⟨hq, -⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (e.trans E)
      set U := matUnitary hT with hU
      let eS : ↥(commutator ↥U) ≃* ↥⁅U, U⁆ :=
        ((commutator ↥U).equivMapOfInjective U.subtype U.subtype_injective).trans
          (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator U))
      have hqS : CFSG.IsQuasisimple ↥⁅U, U⁆ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eS hq
      have hsS : IsSimpleGroup ↥⁅U, U⁆ := by
        have hmapc : (commutator ↥U).map (e.trans E).toMonoidHom = commutator sympFour := by
          rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
            MonoidHom.range_eq_top.2 (e.trans E).surjective]
        let e' : ↥(commutator ↥U) ≃* ↥(commutator sympFour) :=
          ((commutator ↥U).equivMapOfInjective _ (e.trans E).injective).trans
            (MulEquiv.subgroupCongr hmapc)
        have : IsSimpleGroup ↥(commutator sympFour) := isSimpleGroup_commutator_sympFour
        exact (eS.symm.trans e').isSimpleGroup
      refine ⟨⁅U, U⁆, Subgroup.commutator_le_self U, fun u hu s hs => ?_, ⟨1, le_rfl⟩,
        Or.inr ⟨hqS, isCyclic_center_of_forall_mem_center fun z hz hzc => ?_⟩⟩
      · rw [← Subgroup.map_subtype_commutator] at hs ⊢
        obtain ⟨s', hs', rfl⟩ := hs
        have hs'' : (⟨u, hu⟩ : ↥U) * s' * (⟨u, hu⟩ : ↥U)⁻¹ ∈ commutator ↥U :=
          (inferInstance : (commutator ↥U).Normal).conj_mem s' hs' ⟨u, hu⟩
        exact ⟨_, hs'', rfl⟩
      · rw [eq_one_of_mem_center_of_isSimpleGroup hqS hsS hz hzc]
        exact Subgroup.one_mem _
  · exact hquasi (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB hn
      (by omega) (Or.inl hD4))

end LayerCyc

end CFSG.StandardType

end
