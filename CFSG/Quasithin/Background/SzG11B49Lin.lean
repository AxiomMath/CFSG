module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.G11.SzG11S

open Module CFSG.GroupTheory.GLnTwoSplitting

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure B49Hyp (B : LinearMap.BilinForm (ZMod 2) V) (H : Subgroup (GLV V))
    (U : Submodule (ZMod 2) V) : Prop where
  alt : ∀ v, B v v = 0
  nondeg : ∀ v, (∀ w, B v w = 0) → v = 0
  isom : ∀ h ∈ H, ∀ v w, B (h v) (h w) = B v w
  three : 3 ≤ finrank (ZMod 2) U
  iso : Isotropic B U
  dim : 2 * finrank (ZMod 2) U = finrank (ZMod 2) V
  inv : Invariant H U
  faith : FaithfulOn H U
  aut : AutAll H U

namespace B49Aux

theorem apply_inv_apply (g : GLV V) (x : V) : g (g⁻¹ x) = x := by
  change (g * g⁻¹) x = x
  rw [mul_inv_cancel]
  rfl

theorem inv_apply_apply (g : GLV V) (x : V) : g⁻¹ (g x) = x := by
  change (g⁻¹ * g) x = x
  rw [inv_mul_cancel]
  rfl

theorem span_pair_eq {z z' x : V} :
    x ∈ Submodule.span (ZMod 2) {z, z'} ↔ x = 0 ∨ x = z ∨ x = z' ∨ x = z + z' := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

end B49Aux

open B49Aux

namespace B49Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {H : Subgroup (GLV V)}
  {U : Submodule (ZMod 2) V} (hy : B49Hyp B H U)

include hy

theorem symm (x y : V) : B x y = B y x := by
  have h := hy.alt (x + y)
  simp only [map_add, LinearMap.add_apply, hy.alt] at h
  generalize B x y = a at *
  generalize B y x = b at *
  revert a b
  decide

theorem nondegenerate : B.Nondegenerate :=
  ⟨hy.nondeg, fun y h => hy.nondeg y fun w => by rw [hy.symm]; exact h w⟩

theorem isRefl : B.IsRefl := fun x y h => by rw [hy.symm]; exact h

theorem exists_pair {x : V} (hx : x ≠ 0) : ∃ y, B x y = 1 := by
  by_contra h
  push Not at h
  refine hx (hy.nondeg x fun w => ?_)
  rcases zmod_two_eq_zero_or_one (B x w) with h0 | h1
  · exact h0
  · exact absurd h1 (h w)

theorem mem_of_orth [Finite V] {v : V} (h : ∀ u ∈ U, B v u = 0) : v ∈ U := by
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hle : U ≤ B.orthogonal U := fun u hu w hw => hy.iso w hw u hu
  have hr : finrank (ZMod 2) (B.orthogonal U) = finrank (ZMod 2) U := by
    rw [LinearMap.BilinForm.finrank_orthogonal hy.nondegenerate U]
    have := hy.dim
    omega
  have heq : U = B.orthogonal U := Submodule.eq_of_le_of_finrank_eq hle hr.symm
  rw [heq]
  intro n hn
  rw [hy.symm]
  exact h n (heq ▸ hn)

theorem inv_apply_mem {g : GLV V} (hg : g ∈ H) {u : V} (hu : u ∈ U) : g⁻¹ u ∈ U :=
  hy.inv g⁻¹ (H.inv_mem hg) u hu

theorem apply_mem {g : GLV V} (hg : g ∈ H) {u : V} (hu : u ∈ U) : g u ∈ U :=
  hy.inv g hg u hu

theorem B_apply_left {g : GLV V} (hg : g ∈ H) (x y : V) : B (g x) y = B x (g⁻¹ y) := by
  have h := hy.isom g hg x (g⁻¹ y)
  rwa [apply_inv_apply] at h

theorem eq_of_eqOn {g g' : GLV V} (hg : g ∈ H) (hg' : g' ∈ H) (h : ∀ u ∈ U, g u = g' u) :
    g = g' := by
  have hs : g'⁻¹ * g ∈ centralizerOn H U := by
    refine ⟨H.mul_mem (H.inv_mem hg') hg, fun u hu => ?_⟩
    show g'⁻¹ (g u) = u
    rw [h u hu, inv_apply_apply]
  have hb : centralizerOn H U = ⊥ := hy.faith
  rw [hb] at hs
  have h1 : g'⁻¹ * g = 1 := Subgroup.mem_bot.1 hs
  calc g = g' * (g'⁻¹ * g) := (mul_inv_cancel_left g' g).symm
    _ = g' := by rw [h1, mul_one]

theorem eq_one_of_eqOn {g : GLV V} (hg : g ∈ H) (h : ∀ u ∈ U, g u = u) : g = 1 :=
  hy.eq_of_eqOn hg H.one_mem h

theorem exists_sep [Finite V] {z z' : V} (h : z' ∉ Submodule.span (ZMod 2) {z}) :
    ∃ x, B z x = 0 ∧ B z' x = 1 := by
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨χ, hχ, hχz'⟩ := exists_dual_eq_one_of_notMem h
  have key : ∀ y, B ((B.toDual hy.nondegenerate).symm χ) y = χ y := fun y => by
    have := LinearMap.BilinForm.toDual_def hy.nondegenerate
      (m := (B.toDual hy.nondegenerate).symm χ) (n := y)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨(B.toDual hy.nondegenerate).symm χ, ?_, ?_⟩
  · rw [hy.symm, key]
    exact hχ z (Submodule.mem_span_singleton_self z)
  · rw [hy.symm, key]
    exact hχz'

theorem mem_span_pair_of_orth [Finite V] {x z z' : V}
    (h : ∀ w, B z w = 0 → B z' w = 0 → B x w = 0) :
    x ∈ Submodule.span (ZMod 2) {z, z'} := by
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have := LinearMap.BilinForm.orthogonal_orthogonal hy.nondegenerate hy.isRefl
    (Submodule.span (ZMod 2) {z, z'})
  rw [← this]
  intro m hm
  have hz : B z m = 0 := hm z (Submodule.subset_span (by simp))
  have hz' : B z' m = 0 := hm z' (Submodule.subset_span (by simp))
  rw [hy.symm]
  exact h m hz hz'

theorem mem_span_single_of_orth [Finite V] {x z : V} (h : ∀ w, B z w = 0 → B x w = 0) :
    x ∈ Submodule.span (ZMod 2) {z} := by
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have := LinearMap.BilinForm.orthogonal_orthogonal hy.nondegenerate hy.isRefl
    (Submodule.span (ZMod 2) {z})
  rw [← this]
  intro m hm
  have hz : B z m = 0 := hm z (Submodule.mem_span_singleton_self z)
  rw [hy.symm]
  exact h m hz

end B49Hyp

end CFSG.Quasithin.G11.SzG11S
