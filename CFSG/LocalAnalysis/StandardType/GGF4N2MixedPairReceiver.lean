module

public import CFSG.LocalAnalysis.StandardType.GGF4N2MixedMarkedL
public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeDict
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.RankThree.PartOne.KE.TitsFiveCentralizer

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.Blueprint

section Native

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny N2E6Native in
theorem ggF4N2_mixed_dict_components_of_native {G : Type} [Group G]
    (Ψ : ↥(e6Data_valid.minGroup (GaloisField 2 2)) →* G)
    (hΨ : Ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    {X₀ : Subgroup G} (hX₀ : Ψ.range = X₀) (c : G)
    {t : SL2 (GaloisField 2 2)} (ht : orderOf t = 5)
    {i' : Fin 4}
    (u' : ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    (hu' : e6Isogeny (GaloisField 2 2) u' = nativeY t (Pi.single i' 1))
    {w : G} (hw : Subgroup.zpowers w = Subgroup.zpowers (c * Ψ u' * c⁻¹))
    {i j : Fin 4} (hij : i ≠ j) {e : ℤ} (he : e = 1 ∨ e = -1)
    (u : ↥(e6Data_valid.minGroup (GaloisField 2 2)))
    (hu : e6Isogeny (GaloisField 2 2) u = nativeY t (Pi.single i 1 + e • Pi.single j 1))
    {x : G} (hx : Subgroup.zpowers x = Subgroup.zpowers (c * Ψ u * c⁻¹)) :
    (∃ I₂ : Subgroup G, CFSG.Open.IsComponentOf I₂
        (X₀.map (MulAut.conj c).toMonoidHom ⊓ Subgroup.centralizer ({w} : Set G)) ∧
      LieModel (↥I₂ ⧸ Subgroup.center ↥I₂) .PSL 6 2 2) ∧
    (∃ I : Subgroup G, CFSG.Open.IsComponentOf I
        (X₀.map (MulAut.conj c).toMonoidHom ⊓ Subgroup.centralizer ({x} : Set G)) ∧
      LieModel (↥I ⧸ Subgroup.center ↥I) .POmegaMinus 4 2 2) := by
  set ψ : ↥(e6Data_valid.minGroup (GaloisField 2 2)) →* G := (MulAut.conj c).toMonoidHom.comp Ψ
    with hψdef
  have hψ : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 2)) := by
    rw [hψdef, ← MonoidHom.comap_ker,
      (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj c).injective, MonoidHom.comap_bot]
    exact hΨ
  have hrange : ψ.range = X₀.map (MulAut.conj c).toMonoidHom := by
    rw [hψdef, MonoidHom.range_comp, hX₀]
  have hψu : ∀ v, ψ v = c * Ψ v * c⁻¹ := fun v => rfl
  obtain ⟨K₂, -, hK₂ψ, -, hK₂L, -⟩ := native_axis_component_of_order_five ψ hψ ht i' u' hu'
  obtain ⟨K₁, -, hK₁ψ, -, hK₁L, -⟩ := native_pair_component_of_order_five ψ hψ ht hij he u hu
  have hCw := CFSG.RankThree.PartOne.KE.tits_centralizer_singleton_eq_of_zpowers_eq hw
  have hCx := CFSG.RankThree.PartOne.KE.tits_centralizer_singleton_eq_of_zpowers_eq hx
  refine ⟨⟨K₂.map ψ, ?_, hK₂L⟩, ⟨K₁.map ψ, ?_, hK₁L⟩⟩
  · rw [← hrange, hCw, ← hψu]
    exact hK₂ψ
  · rw [← hrange, hCx, ← hψu]
    exact hK₁ψ

end Native

end CFSG.StandardType

end
