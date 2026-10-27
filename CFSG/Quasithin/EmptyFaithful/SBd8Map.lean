module

public import CFSG.Quasithin.EmptyFaithful.SBd8Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

section MapEquiv

variable {X Y : Type} [Group X] [Group Y]

theorem isMaxSubgroupIn_map_equiv_iff (e : X ≃* Y) {P N : Subgroup X} :
    IsMaxSubgroupIn (P.map e.toMonoidHom) (N.map e.toMonoidHom) ↔ IsMaxSubgroupIn P N := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  constructor
  · rintro ⟨hlt, hmax⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective hinj).1 hlt, fun Q hNQ hQP => ?_⟩
    have h1 := hmax (Q.map e.toMonoidHom) ((Subgroup.map_lt_map_iff_of_injective hinj).2 hNQ)
      (Subgroup.map_mono hQP)
    exact Subgroup.map_injective hinj h1
  · rintro ⟨hlt, hmax⟩
    refine ⟨(Subgroup.map_lt_map_iff_of_injective hinj).2 hlt, fun K hNK hKP => ?_⟩
    set Q := K.map e.symm.toMonoidHom with hQ
    have hQe : Q.map e.toMonoidHom = K := by
      rw [hQ, Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext x; simp
      rw [this, Subgroup.map_id]
    rw [← hQe] at hNK hKP ⊢
    have h1 := hmax Q ((Subgroup.map_lt_map_iff_of_injective hinj).1 hNK)
      ((Subgroup.map_le_map_iff_of_injective hinj).1 hKP)
    rw [h1]

theorem ncard_maxOver_map_equiv (e : X ≃* Y) (P T : Subgroup X) :
    (maxOver (P.map e.toMonoidHom) (T.map e.toMonoidHom)).ncard = (maxOver P T).ncard := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have : maxOver (P.map e.toMonoidHom) (T.map e.toMonoidHom) =
      (maxOver P T).image (Subgroup.map e.toMonoidHom) := by
    ext N
    constructor
    · rintro ⟨hN, hTN⟩
      set N' := N.map e.symm.toMonoidHom with hN'
      have hNe : N'.map e.toMonoidHom = N := by
        rw [hN', Subgroup.map_map]
        have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext x; simp
        rw [this, Subgroup.map_id]
      refine ⟨N', ⟨?_, ?_⟩, hNe⟩
      · rw [← hNe] at hN
        exact (isMaxSubgroupIn_map_equiv_iff e).1 hN
      · rw [← hNe] at hTN
        exact (Subgroup.map_le_map_iff_of_injective hinj).1 hTN
    · rintro ⟨N', ⟨hN', hTN'⟩, rfl⟩
      exact ⟨(isMaxSubgroupIn_map_equiv_iff e).2 hN', Subgroup.map_mono hTN'⟩
  rw [this]
  exact Set.ncard_image_of_injective _ (Subgroup.map_injective hinj)


theorem map_symm_map_equiv (e : X ≃* Y) (H : Subgroup X) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by ext x; simp
  rw [this, Subgroup.map_id]

theorem map_map_symm_equiv (e : X ≃* Y) (H : Subgroup Y) :
    (H.map e.symm.toMonoidHom).map e.toMonoidHom = H := map_symm_map_equiv e.symm H

theorem isMinParabolicOf_map_equiv {e : X ≃* Y} {H P : Subgroup X} (h : IsMinParabolicOf H P) :
    IsMinParabolicOf (H.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  obtain ⟨T, hT, ⟨⟨hPH, hTP, hcard⟩, hnn⟩⟩ := h
  refine ⟨T.map e.toMonoidHom, (SBd3T.isSylowTwoOf_map_iff e.toMonoidHom hinj T H).2 hT,
    ⟨⟨Subgroup.map_mono hPH, (Subgroup.map_lt_map_iff_of_injective hinj).2 hTP, ?_⟩, ?_⟩⟩
  · rwa [ncard_maxOver_map_equiv]
  · intro hle
    apply hnn
    intro p hp
    exact (SBd3T.map_mem_normalizer_iff e.toMonoidHom hinj T p).1 (hle ⟨p, hp, rfl⟩)

theorem isMinParabolicOf_map_equiv_iff (e : X ≃* Y) {H P : Subgroup X} :
    IsMinParabolicOf (H.map e.toMonoidHom) (P.map e.toMonoidHom) ↔ IsMinParabolicOf H P := by
  refine ⟨fun h => ?_, isMinParabolicOf_map_equiv⟩
  have := isMinParabolicOf_map_equiv (e := e.symm) h
  rwa [map_symm_map_equiv, map_symm_map_equiv] at this

theorem map_map_congr (e : X ≃* Y) (α : MulAut X) (S : Subgroup X) :
    (S.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom = (S.map α.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

theorem map_symm_congr (e : X ≃* Y) (α : MulAut X) (S : Subgroup Y) :
    (S.map e.symm.toMonoidHom).map α.toMonoidHom =
      (S.map (MulAut.congr e α).toMonoidHom).map e.symm.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

end MapEquiv

section OvgMap

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]

theorem OvgData.map (e : X ≃* Y) {A : Subgroup (MulAut X)} {U K : Subgroup X}
    (d : OvgData X A U K) :
    OvgData Y (A.map (MulAut.congr e).toMonoidHom) (U.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hα' : ∀ β ∈ A.map (MulAut.congr e).toMonoidHom, ∃ α ∈ A, MulAut.congr e α = β := by
    rintro β ⟨α, hα, rfl⟩
    exact ⟨α, hα, rfl⟩
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e d.quasi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := isSylowTwoOf_map' d.U_syl e.toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  · intro β hβ
    obtain ⟨α, hα, rfl⟩ := hα' β hβ
    rw [map_map_congr, d.A_U α hα]
  · exact Subgroup.map_mono d.U_le
  · intro h
    apply d.K_ne
    apply Subgroup.map_injective hinj
    rw [h, Subgroup.map_top_of_surjective _ e.surjective]
  · intro β hβ
    obtain ⟨α, hα, rfl⟩ := hα' β hβ
    rw [map_map_congr, d.A_K α hα]
  · intro K' hKK' hK'top hinv
    set K₀ := K'.map e.symm.toMonoidHom with hK₀
    have hK₀e : K₀.map e.toMonoidHom = K' := map_map_symm_equiv e K'
    have hKK₀ : K ≤ K₀ := by
      have := Subgroup.map_mono (f := e.symm.toMonoidHom) hKK'
      rwa [map_symm_map_equiv] at this
    have hK₀top : K₀ ≠ ⊤ := by
      intro h
      apply hK'top
      rw [← hK₀e, h, Subgroup.map_top_of_surjective _ e.surjective]
    have hK₀inv : ∀ α ∈ A, K₀.map α.toMonoidHom = K₀ := by
      intro α hα
      have h2 : K'.map (MulAut.congr e α).toMonoidHom = K' :=
        hinv (MulAut.congr e α) ⟨α, hα, rfl⟩
      rw [hK₀, map_symm_congr, h2]
    have h1 := d.K_max K₀ hKK₀ hK₀top hK₀inv
    rw [← hK₀e]
    exact Subgroup.map_mono h1
  · rw [Subgroup.card_map_of_injective hinj]
    exact d.three_dvd
  · rw [Subgroup.card_map_of_injective hinj]
    exact d.not_nine
  · rw [← SBd3T.map_oPrimeResidualOf e.toMonoidHom 3 Nat.prime_three K]
    have := d.Y_solv
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((oPrimeResidualOf 3 K).equivMapOfInjective e.toMonoidHom hinj).symm.toMonoidHom)
      (MulEquiv.injective _)

end OvgMap

end SBd8

end CFSG.Quasithin
