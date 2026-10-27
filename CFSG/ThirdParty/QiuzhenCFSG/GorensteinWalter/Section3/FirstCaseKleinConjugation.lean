module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinReflectionHall
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugating inverted subgroups in the Klein-four branch

This is the transport step used to make the inverted subgroup independent of
the chosen involution: conjugation by an element normalizing `U` carries
`I_U(s)` to `I_U(s^g)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem firstCase_conjugate_invertedSubgroup
    {G : Type u} [Group G]
    {U I : Subgroup G} {s g s' : G}
    (hs : IsInvolution s)
    (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (hgs : g * s * g⁻¹ = s')
    (hI : IsInvertedSubgroup I U s) :
    IsInvertedSubgroup (I.map (MulAut.conj g).toMonoidHom) U s' := by
  change (I.map (MulAut.conj g).toMonoidHom : Set G) = invertedElements U s'
  change (I : Set G) = invertedElements U s at hI
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyI : y ∈ invertedElements U s := by
      rw [← hI]
      exact hy
    have hyU : y ∈ U := hyI.1
    have hgyU : g * y * g⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hgU y).1 hyU
    refine ⟨hgyU, ?_⟩
    calc
      s' * (g * y * g⁻¹) * s'⁻¹ =
          g * (s * y * s⁻¹) * g⁻¹ := by rw [← hgs]; group
      _ = g * y⁻¹ * g⁻¹ := by rw [hyI.2]
      _ = (g * y * g⁻¹)⁻¹ := by group
  · intro hx
    have hginvU : g⁻¹ ∈ Subgroup.normalizer (U : Set G) := by
      exact (Subgroup.normalizer (U : Set G)).inv_mem hgU
    have hxU : x ∈ U := hx.1
    have hyU : g⁻¹ * x * g ∈ U := by
      simpa using (Subgroup.mem_normalizer_iff.mp hginvU x).1 hxU
    have hsg : s = g⁻¹ * s' * g := by
      calc
        s = g⁻¹ * (g * s * g⁻¹) * g := by group
        _ = g⁻¹ * s' * g := by rw [hgs]
    have hsy : s * (g⁻¹ * x * g) * s⁻¹ =
        (g⁻¹ * x * g)⁻¹ := by
      calc
        s * (g⁻¹ * x * g) * s⁻¹ =
            g⁻¹ * (s' * x * s'⁻¹) * g := by rw [hsg]; group
        _ = g⁻¹ * x⁻¹ * g := by rw [hx.2]
        _ = (g⁻¹ * x * g)⁻¹ := by group
    have hyI : g⁻¹ * x * g ∈ I := by
      change g⁻¹ * x * g ∈ (I : Set G)
      rw [hI]
      exact ⟨hyU, hsy⟩
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hyI, by
      simp [MulAut.conj_apply, mul_assoc]⟩

end CFSG.GorensteinWalter
