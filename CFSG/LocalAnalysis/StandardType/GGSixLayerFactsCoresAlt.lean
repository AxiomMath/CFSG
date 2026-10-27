module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresAltForm
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresTransport
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCore
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.PresentationLocal

variable {D : Type} [Field D] {d : ℕ}

theorem card_eq_two_or_four_le [Finite D] [CharP D 2] : Nat.card D = 2 ∨ 4 ≤ Nat.card D := by
  by_contra h
  push Not at h
  have := Fintype.ofFinite D
  have heven := FiniteField.even_card_iff_char_two.mp (ringChar.eq D 2)
  have h2 : 2 ≤ Fintype.card D := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card] at h
  omega

theorem eq_smul_one_of_toLin {z : GL (Fin d) D} {c : D}
    (hc : ∀ w, ((Matrix.GeneralLinearGroup.toLin z : LinearMap.GeneralLinearGroup D (Fin d → D)) :
      Module.End D (Fin d → D)) w = c • w) :
    (z : Matrix (Fin d) (Fin d) D) = c • (1 : Matrix (Fin d) (Fin d) D) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  have h1 := hc w
  rw [Matrix.GeneralLinearGroup.coe_toLin] at h1
  rw [Matrix.toLin'_apply, ← Matrix.mulVecLin_apply, h1, Matrix.toLin'_apply, Matrix.smul_mulVec,
    Matrix.one_mulVec]

theorem eq_one_of_smul_one [CharP D 2] [NeZero d] {z : GL (Fin d) D} {c : D}
    (hz : (z : Matrix (Fin d) (Fin d) D) = c • (1 : Matrix (Fin d) (Fin d) D)) (hz2 : z ^ 2 = 1) :
    z = 1 := by
  have hc2 : c * c = 1 := by
    have h1 := congrArg (fun g : GL (Fin d) D => (g : Matrix (Fin d) (Fin d) D) 0 0) hz2
    simp only [sq, Units.val_mul, hz, Units.val_one, smul_mul_smul, Matrix.one_mul] at h1
    simpa using h1
  have hc1 : c = 1 := by
    have h5 : (c + 1) * (c + 1) = 0 := by
      rw [add_mul, mul_add, mul_add, hc2, mul_one, one_mul, mul_one, add_assoc,
        ← add_assoc c c, CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
    rw [← CharTwo.neg_eq (1 : D)]
    exact eq_neg_of_add_eq_zero_left (mul_self_eq_zero.mp h5)
  exact Units.ext (by rw [hz, hc1, one_smul, Units.val_one])

theorem eq_one_of_mem_center_of_isSimpleGroup {G : Type*} [Group G] {S : Subgroup G}
    (hq : CFSG.IsQuasisimple S) (hs : IsSimpleGroup S) {z : G} (hz : z ∈ S)
    (hzc : ∀ y ∈ S, z * y = y * z) : z = 1 := by
  rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · have hmem : (⟨z, hz⟩ : S) ∈ Subgroup.center S :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hzc y y.2).symm
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    obtain ⟨a, b, hab⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hq
    have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm


theorem altCoreInput_holds : AltCoreInput := by
  intro D _ _ _ d T hT h1 hy
  classical
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : Subsingleton (GL (Fin 0) D) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    exact hasCore_of_isSolvable inferInstance
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
      (H : Matrix (Fin d) (Fin d) D))) → HasCore (matUnitary hT) := by
    intro hq
    refine ⟨matUnitary hT, le_rfl, fun u hu s hs =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hs) (Subgroup.inv_mem _ hu), ⟨0, le_rfl⟩,
      Or.inr ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, fun z hz hzc hz2 => ?_⟩⟩
    obtain ⟨c, hc⟩ :=
      CFSG.RankThree.PartOne.KCSpIsotypic.exists_smul_of_commute_sesqUnitaryGroup_alt
      hB hn _ fun g hg => by
        rw [← hmap] at hg
        obtain ⟨u, hu, rfl⟩ := hg
        have h2 : Matrix.GeneralLinearGroup.toLin z * Matrix.GeneralLinearGroup.toLin u =
            Matrix.GeneralLinearGroup.toLin u * Matrix.GeneralLinearGroup.toLin z := by
          rw [← map_mul, ← map_mul, hzc u hu]
        exact congrArg Units.val h2
    exact eq_one_of_smul_one (eq_smul_one_of_toLin hc) hz2
  rcases card_eq_two_or_four_le (D := D) with hD2 | hD4
  · by_cases h6 : 6 ≤ d
    · exact hquasi (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB hn
        (by omega) (Or.inr (Or.inr ⟨hD2, by omega⟩)))
    rcases (show d = 2 ∨ d = 4 by omega) with hd2 | hd4
    · subst hd2
      have : Group.IsSolvable (GL (Fin 2) D) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable 2 D
          (Or.inr ⟨rfl, Or.inl hD2⟩)
      exact hasCore_of_isSolvable inferInstance
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
        Or.inr ⟨hqS, fun z hz hzc _ => eq_one_of_mem_center_of_isSimpleGroup hqS hsS hz hzc⟩⟩
      rw [← Subgroup.map_subtype_commutator] at hs ⊢
      obtain ⟨s', hs', rfl⟩ := hs
      have hs'' : (⟨u, hu⟩ : ↥U) * s' * (⟨u, hu⟩ : ↥U)⁻¹ ∈ commutator ↥U :=
        (inferInstance : (commutator ↥U).Normal).conj_mem s' hs' ⟨u, hu⟩
      exact ⟨_, hs'', rfl⟩
  · exact hquasi (CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hB hn
      (by omega) (Or.inl hD4))

end LayerCores

end CFSG.StandardType
