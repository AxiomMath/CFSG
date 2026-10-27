module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ID
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_cover_sylow_fixed_aux (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    {T : Subgroup (MulAut W)} (hT : T ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hT2 : IsPGroup 2 ↥T) :
    ∃ w ∈ commSub ⊤ L, w ∉ commSub ⊤ L ⊓ fixV L ∧ ∀ t ∈ T, t w = w := by
  classical
  obtain ⟨ψ, π, hπ, hact, hZcorr⟩ := s16h_sl24_cover_model hW hrow hZ4
  let U : Subgroup W := commSub ⊤ L
  have hTU : T ≤ stabSub U := fun t ht =>
    CFSG.Quasithin.StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := (t : MulAut W))
      (CFSG.Quasithin.mem_stabSub_top (t : MulAut W)) (hT ht)
  let ρT : ↥T →* MulAut ↥U := (resHom U).comp (Subgroup.inclusion hTU)
  let φ : ↥T →* MulAut Orth3 := (CFSG.Quasithin.H.congrHom ψ).comp ρT
  let TM : Subgroup (MulAut Orth3) := φ.range
  have horth3L : orth3L = (autSub L U).map (MulAut.congr ψ).toMonoidHom :=
    s16h_sl24_cover_orth3L_eq_map_autSub hπ hact
  have hρTnorm : ∀ t : ↥T, ρT t ∈ Subgroup.normalizer (autSub L U : Set (MulAut ↥U)) := by
    intro t
    exact s16h_sl24_cover_resHom_normalizer (L := L) (n := (t : MulAut W)) (hT t.2) (hTU t.2)
  have hTMnorm : TM ≤ Subgroup.normalizer (orth3L : Set (MulAut Orth3)) := by
    intro m hm
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hm
    have h1 : φ t ∈ (Subgroup.normalizer (autSub L U : Set (MulAut ↥U))).map
        (CFSG.Quasithin.H.congrHom ψ) :=
      Subgroup.mem_map_of_mem _ (hρTnorm t)
    have h2 := Subgroup.le_normalizer_map (H := autSub L U) (CFSG.Quasithin.H.congrHom ψ) h1
    rw [← horth3L] at h2
    exact h2
  have hTM2 : IsPGroup 2 ↥TM :=
    hT2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨v, hvZ, hvfix⟩ := s16h_orth3_sylow_fixed hTMnorm hTM2
  refine ⟨((ψ.symm v : ↥U) : W), (ψ.symm v).2, ?_, ?_⟩
  · intro hwZ
    have hmem : ψ (ψ.symm v) ∈ orth3Z := (hZcorr (ψ.symm v)).mp hwZ.2
    rw [MulEquiv.apply_symm_apply] at hmem
    exact hvZ hmem
  · intro t ht
    let tT : ↥T := ⟨t, ht⟩
    have hfixφ : φ tT v = v := hvfix (φ tT) (MonoidHom.mem_range.mpr ⟨tT, rfl⟩)
    have hφv : φ tT v = ψ (ρT tT (ψ.symm v)) := rfl
    have hfixψ : ψ (ρT tT (ψ.symm v)) = v := by rw [← hφv]; exact hfixφ
    have heq : ρT tT (ψ.symm v) = ψ.symm v :=
      ψ.injective (by rw [hfixψ, MulEquiv.apply_symm_apply])
    have hval : ((ρT tT (ψ.symm v) : ↥U) : W) = t ((ψ.symm v : ↥U) : W) :=
      CFSG.Quasithin.resHom_apply U (Subgroup.inclusion hTU tT) (ψ.symm v)
    rw [← hval]
    exact congrArg (fun u : ↥U => (u : W)) heq

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
