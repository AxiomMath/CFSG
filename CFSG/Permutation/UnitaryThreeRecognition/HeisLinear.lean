module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.LittleWedderburn

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

section Complement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem isCompl_ker_range_sub_one (g : V →ₗ[K] V) (m : ℕ) (hm : g ^ m = 1)
    (hmK : (m : K) ≠ 0) : IsCompl (LinearMap.ker (g - 1)) (LinearMap.range (g - 1)) := by
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr ?_
  · have := LinearMap.finrank_range_add_finrank_ker (g - 1)
    omega
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx'
    have hgx : g ((g - 1) u) = (g - 1) u := by
      have := LinearMap.mem_ker.mp hx
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
    have hpow : ∀ i : ℕ, (g ^ i) ((g - 1) u) = (g - 1) u := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, Module.End.mul_apply, hgx, ih]
    have hN : (∑ i ∈ Finset.range m, g ^ i) ((g - 1) u) = 0 := by
      rw [← Module.End.mul_apply, geom_sum_mul, hm, sub_self, LinearMap.zero_apply]
    rw [LinearMap.sum_apply] at hN
    simp only [hpow, Finset.sum_const, Finset.card_range] at hN
    have h' : (m : K) • ((g - 1) u) = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hN
    exact (smul_eq_zero.mp h').resolve_left hmK

end Complement

section Schur

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def IsIrred (R : Set (Module.End K V)) : Prop :=
  ∀ U : Submodule K V, (∀ g ∈ R, ∀ v ∈ U, g v ∈ U) → U = ⊥ ∨ U = ⊤

variable [Finite V] {R : Set (Module.End K V)}

theorem bijective_of_mem_centralizer (hirr : IsIrred R) {a : Module.End K V}
    (ha : a ∈ Subalgebra.centralizer K R) (ha0 : a ≠ 0) : Function.Bijective a := by
  have hinv : ∀ g ∈ R, ∀ v ∈ LinearMap.ker a, g v ∈ LinearMap.ker a := by
    intro g hg v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hag := (Subalgebra.mem_centralizer_iff K).mp ha g hg
    rw [← Module.End.mul_apply, ← hag, Module.End.mul_apply, hv, map_zero]
  rcases hirr _ hinv with h | h
  · exact (LinearMap.ker_eq_bot.mp h).bijective_of_finite
  · exact absurd (LinearMap.ker_eq_top.mp h) ha0

theorem isUnit_or_eq_zero_of_irred (hirr : IsIrred R) (a : Subalgebra.centralizer K R) :
    IsUnit a ∨ a = 0 := by
  by_cases ha : a = 0
  · exact Or.inr ha
  left
  have hbij := bijective_of_mem_centralizer hirr a.2 (fun h => ha (Subtype.ext h))
  let e := LinearEquiv.ofBijective (a : Module.End K V) hbij
  have hmem : (e.symm : Module.End K V) ∈ Subalgebra.centralizer K R := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    have hag := (Subalgebra.mem_centralizer_iff K).mp a.2 g hg
    ext v
    apply e.injective
    change (a : Module.End K V) (g (e.symm v)) = (a : Module.End K V) (e.symm (g v))
    rw [← Module.End.mul_apply, ← hag, Module.End.mul_apply]
    change g (e (e.symm v)) = e (e.symm (g v))
    rw [e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨⟨a, ⟨e.symm, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    ext v
    exact e.apply_symm_apply v
  · apply Subtype.ext
    ext v
    exact e.symm_apply_apply v

variable (R) in
@[expose] def SchurField (_hirr : IsIrred R) (_hV : Nontrivial V) : Type _ :=
  Subalgebra.centralizer K R

namespace SchurField

variable (hirr : IsIrred R) (hV : Nontrivial V)

instance instFinite : Finite (SchurField R hirr hV) :=
  haveI : Finite (Module.End K V) :=
    Finite.of_injective (fun f : Module.End K V => (f : V → V)) DFunLike.coe_injective
  inferInstanceAs (Finite (Subalgebra.centralizer K R))

noncomputable instance instField : Field (SchurField R hirr hV) :=
  letI : Ring (SchurField R hirr hV) := inferInstanceAs (Ring (Subalgebra.centralizer K R))
  letI : Nontrivial (SchurField R hirr hV) :=
    inferInstanceAs (Nontrivial (Subalgebra.centralizer K R))
  letI : DivisionRing (SchurField R hirr hV) :=
    DivisionRing.ofIsUnitOrEqZero (isUnit_or_eq_zero_of_irred hirr)
  littleWedderburn _

@[expose] noncomputable def toEnd : SchurField R hirr hV →+* Module.End K V where
  toFun a := Subtype.val (p := fun x => x ∈ Subalgebra.centralizer K R) a
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toEnd_injective : Function.Injective (toEnd hirr hV) := fun _ _ h => Subtype.ext h

theorem toEnd_mem (a : SchurField R hirr hV) :
    toEnd hirr hV a ∈ Subalgebra.centralizer K R :=
  Subtype.property (p := fun x => x ∈ Subalgebra.centralizer K R) a

@[expose] def mk (g : Module.End K V) (hg : ∀ g' ∈ R, g' * g = g * g') :
    SchurField R hirr hV :=
  (⟨g, (Subalgebra.mem_centralizer_iff K).mpr hg⟩ : Subalgebra.centralizer K R)

@[simp] theorem toEnd_mk (g : Module.End K V) (hg : ∀ g' ∈ R, g' * g = g * g') :
    toEnd hirr hV (mk hirr hV g hg) = g := rfl

noncomputable instance instModule : Module (SchurField R hirr hV) V :=
  Module.compHom V (toEnd hirr hV)

theorem smul_def (a : SchurField R hirr hV) (v : V) : a • v = toEnd hirr hV a v := rfl

theorem smul_smul_scalar (a : SchurField R hirr hV) (c : K) (v : V) :
    a • c • v = c • a • v :=
  map_smul (toEnd hirr hV a) c v

end SchurField

end Schur

end CFSG.UnitaryThreeRecognition.Heisenberg
