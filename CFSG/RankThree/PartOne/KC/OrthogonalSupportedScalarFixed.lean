module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCPrimary

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.suppPerp_fixedSpace (hx : OddOrderIsometry Q p x) :
    suppPerp Q (fixedSpace x) = othersSpace x.toLinearMap (X - 1) := by
  ext v
  constructor
  · intro hv
    exact hx.perp_fixed_le_others fun u hu => by
      rw [polar_comm]
      exact mem_suppPerp.mp hv u hu
  · intro hv
    rw [mem_suppPerp]
    exact fun w hw => hx.fixed_others.2 w hw v hv

theorem OddOrderIsometry.supportedDerived_fixedSpace (hx : OddOrderIsometry Q p x) :
    supportedDerived Q (fixedSpace x) = supportedFixedDerived Q x := by
  have hperp := hx.suppPerp_fixedSpace
  ext g
  rw [mem_supportedFixedDerived]
  constructor
  · intro hg
    obtain ⟨hgp, h, hh, e⟩ := hg
    have hg' : g ∈ supportedDerived Q (fixedSpace x) := ⟨hgp, h, hh, e⟩
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      supportedDerived_le_orthogonalGroup
        (polarNondegOn_of_nondegenerate hx.polarBilin_fixed_nondegenerate) hg'
    have hgfix : ∀ r ∈ othersSpace x.toLinearMap (X - 1), g r = r := fun r hr =>
      hgp r (hperp ▸ hr)
    have hgW : ∀ w ∈ fixedSpace x, g w ∈ fixedSpace x := fun w hw =>
      supportedDerived_apply_mem hg' hw
    have hxmem : x ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => by rw [Set.mem_singleton_iff.mp hy]
    have hcomm : ∀ v, g (x v) = x (g v) := by
      intro v
      obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
      have hxr : x r ∈ othersSpace x.toLinearMap (X - 1) := mem_othersSpace_of_apply hxmem hr
      calc g (x (w + r)) = g (x w + x r) := by rw [map_add]
        _ = g w + x r := by rw [mem_fixedSpace.mp hw, map_add, hgfix _ hxr]
        _ = x (g w) + x r := by rw [mem_fixedSpace.mp (hgW w hw)]
        _ = x (g w + g r) := by rw [map_add, hgfix r hr]
        _ = x (g (w + r)) := by rw [map_add g w r]
    have hgblock : g ∈ supportedBlock Q x (X - 1) :=
      mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr
        ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO v, hcomm⟩, hgfix⟩
    refine ⟨hgblock, ?_⟩
    have hres : restrictFixed Q x ⟨g, hgblock⟩ = h :=
      LinearEquiv.ext fun w => Subtype.ext ((coe_restrictFixed ⟨g, hgblock⟩ w).trans (e w).symm)
    rw [hres]
    exact hh
  · rintro ⟨hgb, hres⟩
    exact ⟨fun v hv => (mem_supportedBlock.mp hgb).2 v (hperp ▸ hv),
      restrictFixed Q x ⟨g, hgb⟩, hres, fun w => rfl⟩

end CFSG.RankThree.PartOne.KCOrthogonal
