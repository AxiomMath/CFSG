module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {X Y : Type} [Group X] [Group Y]

noncomputable abbrev centerQuotientCongr (e : X ≃* Y) :
    X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
  QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (Subgroup.map_center_eq e)

theorem centerQuotientCongr_symm_mk (e : X ≃* Y) (x : X) :
    (centerQuotientCongr e).symm (QuotientGroup.mk (e x)) = QuotientGroup.mk x :=
  (MulEquiv.symm_apply_eq _).mpr rfl

theorem isOrthReflection_map (e : X ≃* Y) {m f : ℕ} {s : X} (h : IsOrthReflection X m f s) :
    IsOrthReflection Y m f (e s) := by
  rcases h with ⟨k, hk, hmk, F, hF, hFin, hcard, e', hr⟩ |
      ⟨k, hk, hmk, F, hF, hFin, hcard, b, c, hbc, e', hr⟩
  · refine Or.inl ⟨k, hk, hmk, F, hF, hFin, hcard, (centerQuotientCongr e).symm.trans e', ?_⟩
    rwa [MulEquiv.trans_apply, centerQuotientCongr_symm_mk]
  · refine Or.inr ⟨k, hk, hmk, F, hF, hFin, hcard, b, c, hbc,
      (centerQuotientCongr e).symm.trans e', ?_⟩
    rwa [MulEquiv.trans_apply, centerQuotientCongr_symm_mk]

theorem isSymplecticTransvection_map (e : X ≃* Y) {m f : ℕ} {s : X}
    (h : IsSymplecticTransvection X m f s) : IsSymplecticTransvection Y m f (e s) := by
  obtain ⟨k, hmk, F, hF, hFin, hcard, e', hr⟩ := h
  refine ⟨k, hmk, F, hF, hFin, hcard, (centerQuotientCongr e).symm.trans e', ?_⟩
  rwa [MulEquiv.trans_apply, centerQuotientCongr_symm_mk]

theorem isUnitaryTransvection_map (e : X ≃* Y) {m f : ℕ} {s : X}
    (h : IsUnitaryTransvection X m f s) : IsUnitaryTransvection Y m f (e s) := by
  obtain ⟨F, hF, hFin, hcard, e', hr⟩ := h
  refine ⟨F, hF, hFin, hcard, (centerQuotientCongr e).symm.trans e', ?_⟩
  rwa [MulEquiv.trans_apply, centerQuotientCongr_symm_mk]

end CFSG.OddTranspositions.PartFour

end
