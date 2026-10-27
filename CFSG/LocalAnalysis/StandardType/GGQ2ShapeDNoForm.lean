module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_shapeD_noForm {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hD : M.ShapeD) (hx : M.xV ≠ 0) :
    ¬ ∃ Q : QuadraticForm (ZMod 3) M.V, (QuadraticMap.polarBilin Q).Nondegenerate ∧
      ∀ φ ∈ ggAutomizer L Bs, ZS.IsIsom 3 Q (ggLin (p := 3) M.model φ) := by
  rintro ⟨Q, hQ, hiso⟩
  set B := QuadraticMap.polarBilin Q with hB
  have hQnd : B.Nondegenerate := by rw [hB]; exact hQ
  have hfix : ∀ φ ∈ ggAutomizer L Bs, ggLin (p := 3) M.model φ M.xV = M.xV := by
    have hmem : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
      rw [M.fixed_x]
      exact Submodule.mem_span_singleton_self M.xV
    exact mem_ggFixedSubmodule_iff.mp hmem
  have hBcoroot : ∀ i, B M.xV (M.coroot i) = 0 := by
    intro i
    set s : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model (M.simple i) with hs
    have hsi : M.simple i ∈ ggAutomizer L Bs := by
      rw [M.automizer_L]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    have hfixi : s M.xV = M.xV := by
      rw [hs]
      exact hfix (M.simple i) hsi
    have hisoi : ∀ v, Q (s v) = Q v := by
      intro v
      rw [hs]
      exact hiso (M.simple i) hsi v
    have hpol : ∀ u v, B (s u) (s v) = B u v := by
      intro u v
      simp only [hB, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hisoi]
    have h1 : B M.xV (s (M.coroot i)) = B M.xV (M.coroot i) := by
      have h2 := hpol M.xV (M.coroot i)
      rw [hfixi] at h2
      exact h2
    have hstep : B M.xV (s (M.coroot i) - M.coroot i) = 0 := by
      rw [map_sub, h1, sub_self]
    rw [hs, M.simple_apply i (M.coroot i)] at hstep
    have harg : (M.coroot i - M.root i (M.coroot i) • M.coroot i) - M.coroot i =
        -(M.root i (M.coroot i) • M.coroot i) := by abel
    rw [harg, map_neg, map_smul, neg_eq_zero] at hstep
    rw [M.pairing i i, M.isCartan.1 i] at hstep
    push_cast at hstep
    rw [smul_eq_mul] at hstep
    exact (mul_eq_zero.mp hstep).resolve_left (by decide)
  have hkill : ∀ v, B M.xV v = 0 := by
    intro v
    have hspan : M.coSpan ≤ LinearMap.ker (B M.xV) := by
      rw [GGQ2LDatum.coSpan]
      exact Submodule.span_le.mpr (by
        rintro _ ⟨i, rfl⟩
        exact LinearMap.mem_ker.mpr (hBcoroot i))
    have hv : v ∈ M.coSpan := by rw [hD.2.2]; exact Submodule.mem_top
    exact LinearMap.mem_ker.mp (hspan hv)
  have hBx0 : B M.xV = 0 := LinearMap.ext hkill
  have hx0 : M.xV = 0 :=
    (LinearMap.separatingLeft_iff_linear_nontrivial.mp hQnd.1) M.xV hBx0
  exact hx hx0

end CFSG.StandardType

end
