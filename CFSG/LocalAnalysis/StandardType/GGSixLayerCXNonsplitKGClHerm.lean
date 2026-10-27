module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClSUNbr
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClSpOne
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsBlock
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender

public section

namespace CFSG.StandardType

namespace ClNonsplit

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.Universal Matrix
  LayerCores CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem unitaryLabel_of_markTag_PSU {lab : LargeEvenLabel} (hT : markTag lab = .PSU)
    (hc : markChar lab = 2) : GGInndiagUnitaryLabel lab ∧ markDeg lab = lab.n := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [markTag, markChar] at hT hc
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | exact absurd hc (by decide)
    | simp at hT
    | (by_cases h3 : l = 3 <;> simp [h3] at hT <;> done)
    | (by_cases h2 : l = 2
       · simp [h2] at hT
       · by_cases h3 : l = 3
         · exact ⟨Or.inr ⟨rfl, h3⟩, by simp [markDeg, h2]⟩
         · simp [h2, h3] at hT)

section Main

theorem not_ggNbrClauseFiveMarking_su_of_lieModel {G : Type} [Group G] {K' : Subgroup G}
    {m f : ℕ} (hL : LieModel (↥K' ⧸ Subgroup.center ↥K') .PSU m 2 f) (hm : 3 ≤ m) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1) {x : G}
    (hinn : ∃ k ∈ K', ∀ l ∈ K', x⁻¹ * l * x = k⁻¹ * l * k) :
    ¬ GGNbrClauseFiveMarking p x K' := by
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hdet : ∀ lab : LargeEvenLabel, markChar lab = 2 →
      MarkedModel lab (↥K' ⧸ Subgroup.center ↥K') → markTag lab = .PSU ∧ markDeg lab = f := by
    intro lab hc hX
    have hX' : LieModel (↥K' ⧸ Subgroup.center ↥K') (markTag lab) (markRank lab) 2
        (markDeg lab) := by
      have h := hX
      unfold MarkedModel at h
      rwa [hc] at h
    have hadm' := CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hX'
    rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | hm4
    · obtain ⟨h1, -, h3⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet _ f _ _ _ hL hadm' hX'
      exact ⟨h1, h3⟩
    · obtain ⟨h1, -, h3⟩ :=
        CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt hm4 _ f _ _ _ hL hadm' hX'
      exact ⟨h1, h3⟩
  refine not_ggNbrClauseFiveMarking_of_inner hp hp3 hinn (fun lab _ hc hX hHS => ?_)
    (fun lab hlab hc hX => ?_)
  · obtain ⟨hT, hD⟩ := hdet lab hc hX
    obtain ⟨hU, hDn⟩ := unitaryLabel_of_markTag_PSU hT hc
    have hn : lab.n = f := hDn.symm.trans hD
    rcases LinNonsplit.halfSplit_cases hHS with h1 | h1 | h1 | ⟨h0, -, -⟩ | ⟨h0 | h0, -, -⟩
    · exact hq1 (hn ▸ h1)
    · exact hq2 (hn ▸ h1)
    · exact hp3 h1
    all_goals (rcases hU with h' | ⟨h', -⟩ <;> rw [h'] at h0 <;> simp at h0)
  · obtain ⟨hT, -⟩ := hdet lab hc hX
    exact ggRawInnFieldOn_unitary p hp hp2 lab hlab (unitaryLabel_of_markTag_PSU hT hc).1

end Main

section Input

theorem ggNonsplitNbrHermInput_holds : GGNonsplitNbrHermInput := by
  intro G _ _ K' D _ _ _ d T hT hk S hSU hder hq φ hφr hφk f hD p hp hp2 hq1 hq2 x hinn
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
  have hq2' : 2 ≤ 2 ^ f' := by
    have := Nat.one_lt_two_pow (n := f') (by have := hE.one_le; omega)
    omega
  have hcard : Nat.card D = (2 ^ f') ^ 2 := hE.card_eq_sq
  have hff : f' = f := by
    have h1 : (2 ^ f') ^ 2 = (2 ^ f) ^ 2 := hcard.symm.trans hD
    exact Nat.pow_right_injective (le_refl 2) (Nat.pow_left_injective (by norm_num) h1)
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
    have hqSU := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE
      hBs hBl (by rw [hfr]; exact hgood.1)
      ⟨fun h => hq4 (by rw [hfr] at h; omega), fun h => le_trans (by norm_num)
        (hq4 (by rw [hfr] at h; omega))⟩
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
    have hperfS : commutator ↥S = ⊤ := Group.isPerfect_def.mp hq.1
    have hZ : Subgroup.center ↥φ.range = (Subgroup.center ↥S).map φ.rangeRestrict := by
      ext l'
      obtain ⟨u, rfl⟩ := φ.rangeRestrict_surjective l'
      constructor
      · intro hu
        exact ⟨u, InnerDiagA.mem_center_of_rangeRestrict_mem_center hperfS φ hφk hu, rfl⟩
      · rintro ⟨v, hv, hvu⟩
        rw [← hvu, Subgroup.mem_center_iff]
        intro l''
        obtain ⟨w, rfl⟩ := φ.rangeRestrict_surjective l''
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hv w]
    let e0 : ↥S ⧸ Subgroup.center ↥S ≃* ↥φ.range ⧸ Subgroup.center ↥φ.range :=
      CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective φ.rangeRestrict
        φ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hφk) hZ
    let eS : ↥S ≃* sesqSpecialUnitaryGroup (gramForm hE Hm) :=
      (MulEquiv.subgroupCongr hSeq).trans eG
    by_cases hd3 : 3 ≤ d
    ·
      obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hBs hBl
      obtain ⟨ι⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
        (G := (1 : Matrix (Fin (Module.finrank D (Fin d → D))) (Fin (Module.finrank D (Fin d → D)))
          D)) (fun i j => by rw [hb i j, Matrix.one_apply])
      let eU : ↥S ≃* ↥(unitarySU 2 f' D (Module.finrank D (Fin d → D))) :=
        (eS.trans ι).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
      have hmq : (Module.finrank D (Fin d → D), 2 ^ f') ≠ (3, 2) := by
        rw [hfr]
        intro hc
        have h1 := congrArg Prod.fst hc
        have h2 := congrArg Prod.snd hc
        simp only at h1 h2
        exact hgood.2 ⟨by omega, by simp [hcard, h2]⟩
      have hLS := SUFacts.lieModel_quotient_center_of_mulEquiv_unitarySU hE
        (by rw [hfr]; exact hd3) hmq eU
      have hL := lieModel_of_mulEquiv' e0 hLS
      rw [hφr, hff] at hL
      exact not_ggNbrClauseFiveMarking_su_of_lieModel hL (by rw [hfr]; exact hd3) hp hp2 hq1 hq2
        hinn
    ·
      have hd2 : d = 2 := by omega
      obtain ⟨σ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hBs
        hBl (by rw [hfr, hd2])
      set ψ' : SpecialLinearGroup (Fin (1 + 1)) hE.fixedField →* G :=
        φ.comp ((eS.trans σ).symm.toMonoidHom) with hψ'
      have hrange : ψ'.range = K' := by
        rw [← hφr]
        ext g
        constructor
        · rintro ⟨z, rfl⟩
          exact ⟨_, rfl⟩
        · rintro ⟨s, rfl⟩
          exact ⟨(eS.trans σ) s, by simp [hψ']⟩
      have hker' : ψ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (1 + 1)) hE.fixedField) := by
        intro z hz
        have hz' : (eS.trans σ).symm z ∈ φ.ker := hz
        have hc := Subgroup.mem_center_iff.mp (hφk hz')
        rw [Subgroup.mem_center_iff]
        intro w
        apply (eS.trans σ).symm.injective
        rw [map_mul, map_mul]
        exact hc _
      have hcardF : Nat.card hE.fixedField = 2 ^ f := hff ▸ hE.card_fixedField
      have hf2 : 2 ≤ f := by
        have h1 := hE.one_le
        by_contra hlt
        have hf1 : f' = 1 := by omega
        exact hgood.2 ⟨by omega, by rw [hcard, hf1]; norm_num⟩
      have h := not_ggNbrClauseFiveMarking_sl_two hcardF hf2 ψ' hker' hp hp2 hq1 hq2
        (hrange ▸ hinn)
      rwa [hrange] at h

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
    have hD4 : Nat.card D = 4 := by
      by_contra h
      exact hgood ⟨by omega, fun h' => h h'.2⟩
    have hq : 2 ^ f' = 2 := by
      rw [hcard] at hD4
      nlinarith
    have hcardU : Nat.card (matUnitary hT) = 18 ∨ Nat.card (matUnitary hT) = 648 := by
      have h1 := (CFSG.LinearGroups.unitary_full_group_order hE hBs hBl hfr (by omega)).1
      have h2 : Nat.card (matUnitary hT) = Nat.card (sesqUnitaryGroup (gramForm hE Hm)) :=
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
    exact isSolvable_of_card_primeFactors_le_two (card_primeFactors_small hcardU)

end Input

end ClNonsplit

section Tag

theorem ggNonsplitTag_PSU_holds : GGNonsplitTag .PSU :=
  ggNonsplitTag_PSU ClNonsplit.ggNonsplitNbrHermInput_holds

end Tag

end CFSG.StandardType
