module

public import CFSG.Quasithin.Background.RonanG1015Transport
public import CFSG.Quasithin.Background.P4InspOrthSimple
public import CFSG.LieType.ChevTwo.Orthogonal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace RonanG1015

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth CFSG.Open CFSG.GroupTheory.WeirSylow
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv statedOmega_eq_comap)
open CFSG.LieType.ChevTwo (OmegaTwoAutInduced InducedByIso omegaTwoAutInduced)

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}
  {q : U → ZMod 2}

theorem map_commutator_eq_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι]
    {Qm : QuadraticForm (ZMod 2) (ι → ZMod 2)} {Q₀ : (ι → ZMod 2) → ZMod 2} (hQ : ⇑Qm = Q₀)
    (e : U ≃ₗ[ZMod 2] (ι → ZMod 2)) (he : ∀ x, Q₀ (e x) = q x) :
    (⁅orthSub q, orthSub q⁆).map
        ((p4insporth_cg e).trans (toLinEquiv ι (ZMod 2)).symm).toMonoidHom = StatedOmega Q₀ := by
  have h1 : (⁅orthSub q, orthSub q⁆).map (p4insporth_cg e).toMonoidHom =
      ⁅orthSub Q₀, orthSub Q₀⁆ := p4insporth_map_cg_commutator e he
  have h2 := statedOmega_eq_comap hQ
  rw [p4insporth_orthogonalGroup_eq Qm, hQ] at h2
  have key : ∀ H : Subgroup ((ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)),
      H.comap (toLinEquiv ι (ZMod 2)).toMonoidHom = H.map (toLinEquiv ι (ZMod 2)).symm.toMonoidHom :=
    fun H => Subgroup.comap_equiv_eq_map_symm (toLinEquiv ι (ZMod 2)) H
  rw [h2, key, ← h1, Subgroup.map_map]
  rfl

theorem indAll_of_model {ι : Type} [Fintype ι] [DecidableEq ι]
    {Qm : QuadraticForm (ZMod 2) (ι → ZMod 2)} {Q₀ : (ι → ZMod 2) → ZMod 2} (hQ : ⇑Qm = Q₀)
    (hind : OmegaTwoAutInduced Q₀) (e : U ≃ₗ[ZMod 2] (ι → ZMod 2)) (he : ∀ x, Q₀ (e x) = q x) :
    IndAll ⁅orthSub q, orthSub q⁆ := by
  refine IndAll.of_equiv ((p4insporth_cg e).trans (toLinEquiv ι (ZMod 2)).symm)
    (map_commutator_eq_statedOmega hQ e he) ?_
  intro α'
  obtain ⟨g, -, hg⟩ := hind α'
  exact ⟨g, fun x => hg x⟩

theorem indAll_orth_plus [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {n : ℕ} (hn : 5 ≤ n)
    (hdim : Module.finrank (ZMod 2) U = 2 * n) (hplus : IsPlusType (p4insporth_quad hq)) :
    IndAll ⁅orthSub q, orthSub q⁆ := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨e⟩ := nonempty_isometry_quadPlus (p4insporth_nondegenerate_quad hf hq) hdim hplus
  refine indAll_of_model (CFSG.LieType.Universal.Spin.coe_quadPlus (n' + 1) (ZMod 2))
    (omegaTwoAutInduced.2 n' (by omega) (by omega)) e.toLinearEquiv fun x => ?_
  have := e.map_app x
  rw [p4insporth_quad_apply] at this
  rw [← CFSG.LieType.Universal.Spin.coe_quadPlus]
  exact this

theorem indAll_orth_minus [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {n : ℕ} (hn : 3 ≤ n)
    (hdim : Module.finrank (ZMod 2) U = 2 * n) (hminus : ¬ IsPlusType (p4insporth_quad hq)) :
    IndAll ⁅orthSub q, orthSub q⁆ := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨e⟩ := nonempty_isometry_of_not_isPlusType (p4insporth_nondegenerate_quad hf hq)
    (by omega) hdim hminus hirr
  refine indAll_of_model (CFSG.LieType.Universal.Spin.coe_quadMinus (n' + 1) (ZMod 2) 1 1)
    (omegaTwoAutInduced.1 n' (by omega)) e.toLinearEquiv fun x => ?_
  have := e.map_app x
  rw [p4insporth_quad_apply] at this
  rw [← CFSG.LieType.Universal.Spin.coe_quadMinus]
  exact this

end RonanG1015

end CFSG.Quasithin
