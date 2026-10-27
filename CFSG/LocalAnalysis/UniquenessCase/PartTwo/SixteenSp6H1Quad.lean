module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6H1Cohom

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {G : Type*} [Group G] {M E : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup E] [Module (ZMod 2) E]

theorem s16sp_exists_invariant_quad [Finite G] [Finite M] [Finite E]
    (ρM : Representation (ZMod 2) G M) (ρE : Representation (ZMod 2) G E)
    (q : M →ₗ[ZMod 2] E) (hq : Function.Surjective q) (hqρ : ∀ g m, q (ρM g m) = ρE g (q m))
    (hZ : ∀ g m, q m = 0 → ρM g m = m)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ g m, ψ (ρM g m) = ψ m) → ψ = 0)
    {z : M} (hz : q z = 0) (hz0 : z ≠ 0) (q₀ : E → ZMod 2)
    (b₀ : E →ₗ[ZMod 2] E →ₗ[ZMod 2] ZMod 2) (hq₀ : ∀ x y, q₀ (x + y) = q₀ x + q₀ y + b₀ x y)
    (hb₀ : ∀ g x y, b₀ (ρE g x) (ρE g y) = b₀ x y)
    (hnoinv : ∀ l : Module.Dual (ZMod 2) E, ¬ ∀ g x, q₀ (ρE g x) + l (ρE g x) = q₀ x + l x)
    (hH1 : Module.finrank (ZMod 2) (H1 (Representation.dual ρE)) ≤ 1) :
    ∃ Q : M → ZMod 2, (∀ m m', Q (m + m') = Q m + Q m' + b₀ (q m) (q m')) ∧
      (∀ g m, Q (ρM g m) = Q m) ∧ Q z = 1 := by
  classical
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.mpr hq)
  have hsq : ∀ x, q (s x) = x := fun x => LinearMap.congr_fun hs x
  have hq00 : q₀ 0 = 0 := by
    have h := hq₀ 0 0
    simp only [zero_add, map_zero, LinearMap.zero_apply, add_zero] at h
    generalize h0 : q₀ 0 = a at h ⊢
    clear h0
    revert h a
    decide
  obtain ⟨ψ, hψz⟩ : ∃ ψ : M →ₗ[ZMod 2] ZMod 2, ψ z = 1 :=
    Module.Projective.exists_dual_eq_one (ZMod 2) hz0
  have hcWZ : extCocycle ρM ρE s ψ ∈ Z1 (Representation.dual ρE) :=
    s16sp_extCocycle_mem ρM ρE q s hqρ hsq hZ ψ
  have hcWB : extCocycle ρM ρE s ψ ∉ B1 (Representation.dual ρE) :=
    s16sp_extCocycle_not_mem_B1 ρM ρE q s hqρ hsq hZ hperf ψ hz hψz
  obtain ⟨c₀, hc₀, hc₀Z, hc₀B⟩ := s16sp_c0 ρE q₀ b₀ hq₀ hb₀ hnoinv
  obtain ⟨l, hl⟩ := s16sp_exists_coboundary ρE hH1 hcWZ hc₀Z hcWB hc₀B
  have hstar : ∀ g x, ψ (ρM g (s (ρE g⁻¹ x)) - s x) =
      q₀ (ρE g⁻¹ x) + q₀ x + (l (ρE g⁻¹ x) - l x) := by
    intro g x
    have h := LinearMap.congr_fun (hl g) x
    simpa [extCocycle, extTwist, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.add_apply, Representation.dual_apply, Module.Dual.transpose_apply,
      hc₀ g x] using h
  let Q : M → ZMod 2 := fun m => ψ (m - s (q m)) + q₀ (q m) + l (q m)
  refine ⟨Q, ?hadd, ?hinv, ?hz⟩
  · intro m m'
    dsimp only [Q]
    have h1 : q (m + m') = q m + q m' := map_add q m m'
    have h2 : (m + m') - s (q (m + m')) =
        (m - s (q m)) + (m' - s (q m')) := by
      rw [h1, map_add s (q m) (q m')]
      abel
    have h3 : q₀ (q (m + m')) = q₀ (q m) + q₀ (q m') + b₀ (q m) (q m') := by
      rw [h1]
      exact hq₀ (q m) (q m')
    rw [h2, h3, h1]
    simp only [map_add]
    abel
  · intro g m
    dsimp only [Q]
    have hrep : ρE g⁻¹ (ρE g (q m)) = q m := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hker : q (m - s (q m)) = 0 := by rw [map_sub, hsq, sub_self]
    have hfix : ρM g (m - s (q m)) = m - s (q m) := hZ g _ hker
    have hdecomp : ρM g m - s (ρE g (q m)) =
        (m - s (q m)) + (ρM g (s (q m)) - s (ρE g (q m))) := by
      have e : ρM g m = (m - s (q m)) + ρM g (s (q m)) := by
        conv_lhs => rw [show m = (m - s (q m)) + s (q m) by abel]
        rw [map_add, hfix]
      rw [e]
      abel
    have hg := hstar g (ρE g (q m))
    rw [hrep] at hg
    rw [hqρ g m, hdecomp, map_add, hg]
    generalize hA : ψ (m - s (q m)) = A
    generalize hB : q₀ (q m) = B
    generalize hC : l (q m) = C
    generalize hB' : q₀ (ρE g (q m)) = B'
    generalize hC' : l (ρE g (q m)) = C'
    clear hA hB hC hB' hC'
    revert A B C B' C'
    decide
  · dsimp only [Q]
    rw [hz, map_zero, hq00, map_zero, sub_zero, hψz]
    simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
