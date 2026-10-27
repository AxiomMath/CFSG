module

public import CFSG.Quasithin.Background.B4Models
import CFSG.Quasithin.Background.B69Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open CFSG.Quasithin

theorem commutator_eq_top_of_realizes {W : Type} [CommGroup W] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (hR : (FFModel.nat Γ).Realizes H ⊤ ⊥) (hH : ⁅H, H⁆ = H) : commutator ↥Γ = ⊤ := by
  obtain ⟨π, hπ⟩ := hR
  have hπinj : Function.Injective π := B69.natRealizes_injective hπ
  obtain ⟨hπsurj, -⟩ := hπ
  have hHtop : commutator ↥H = ⊤ := (Subgroup.isPerfect_iff.mpr hH).commutator_eq_top
  have hmap1 : (commutator ((FFModel.nat Γ).Gam)).map π = commutator ↥H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hπsurj, ← commutator_def]
  have hmap : (commutator ((FFModel.nat Γ).Gam)).map π =
      (⊤ : Subgroup ((FFModel.nat Γ).Gam)).map π := by
    rw [hmap1, hHtop, Subgroup.map_top_of_surjective π hπsurj]
  exact Subgroup.map_injective hπinj hmap

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
