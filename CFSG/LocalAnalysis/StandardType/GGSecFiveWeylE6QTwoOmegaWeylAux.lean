module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoModelSpinor
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 3) V} {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}
  {hα : ∀ i, α i (h i) = 2}

noncomputable def rootRefl (v : V) (hv : B v v = 2) : V ≃ₗ[ZMod 3] V :=
  Module.reflection (x := v) (f := B v) hv

theorem rootRefl_apply (v : V) (hv : B v v = 2) (u : V) :
    rootRefl (B := B) v hv u = u - B v u • v :=
  Module.reflection_apply u hv

theorem rootRefl_involutive (v : V) (hv : B v v = 2) (u : V) :
    rootRefl (B := B) v hv (rootRefl (B := B) v hv u) = u :=
  Module.involutive_reflection hv u

theorem rootRefl_neg (v : V) (hv : B v v = 2) :
    rootRefl (B := B) (-v) (by
      rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg]; exact hv) =
      rootRefl (B := B) v hv := by
  apply LinearEquiv.ext
  intro u
  rw [rootRefl_apply, rootRefl_apply]
  simp only [LinearMap.BilinForm.neg_left, neg_smul, neg_neg]
  module

theorem rootRefl_isometry (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v)
    (hα : ∀ i, α i (h i) = 2) {v : V} (hv : B v v = 2) (u w : V) :
    B (rootRefl (B := B) v hv u) (rootRefl (B := B) v hv w) = B u w := by
  obtain ⟨g, hg, hgu⟩ := exists_mem_e6Weyl_reflection hP hV hB hα hv
  have hgv : g = rootRefl (B := B) v hv := by
    apply LinearEquiv.ext
    intro x
    rw [hgu x, rootRefl_apply]
  rw [← hgv]
  exact bilinForm_apply_e6Weyl hP hV hB hα hg u w

theorem rootRefl_mem_e6Weyl (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v)
    (hα : ∀ i, α i (h i) = 2) {v : V} (hv : B v v = 2) :
    rootRefl (B := B) v hv ∈ e6Weyl hα := by
  obtain ⟨g, hg, hgu⟩ := exists_mem_e6Weyl_reflection hP hV hB hα hv
  have hgv : g = rootRefl (B := B) v hv := by
    apply LinearEquiv.ext
    intro x
    rw [hgu x, rootRefl_apply]
  rwa [hgv] at hg

theorem rootRefl_conj (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v)
    (hα : ∀ i, α i (h i) = 2) {a b : V} (ha : B a a = 2) (hb : B b b = 2) (u : V) :
    (rootRefl (B := B) a ha * rootRefl (B := B) b hb * (rootRefl (B := B) a ha)⁻¹) u =
      u - B (rootRefl (B := B) a ha b) u • rootRefl (B := B) a ha b := by
  have hiso : ∀ x y : V, B (rootRefl (B := B) a ha x) (rootRefl (B := B) a ha y) = B x y :=
    rootRefl_isometry hP hV hB hα ha
  have hinv : (rootRefl (B := B) a ha)⁻¹ = rootRefl (B := B) a ha := rfl
  have hlin : rootRefl (B := B) a ha (rootRefl (B := B) b hb (rootRefl (B := B) a ha u)) =
      rootRefl (B := B) a ha (rootRefl (B := B) a ha u) -
        B b (rootRefl (B := B) a ha u) • rootRefl (B := B) a ha b := by
    conv_lhs => rw [rootRefl_apply (B := B) b hb (rootRefl (B := B) a ha u)]
    rw [map_sub, map_smul]
  rw [hinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hlin, rootRefl_involutive]
  have hkey : B b (rootRefl (B := B) a ha u) = B (rootRefl (B := B) a ha b) u := by
    have h := hiso b (rootRefl (B := B) a ha u)
    rw [rootRefl_involutive] at h
    exact h.symm
  rw [hkey]

theorem rootRefl_self_apply (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v)
    (hα : ∀ i, α i (h i) = 2) {a b : V} (ha : B a a = 2) (hb : B b b = 2) :
    B (rootRefl (B := B) a ha b) (rootRefl (B := B) a ha b) = 2 := by
  rw [rootRefl_isometry hP hV hB hα ha]
  exact hb

theorem exists_root_of_ggIsReflection {G : Type} [Group G] {Bs : Subgroup G}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v)
    (hα : ∀ i, α i (h i) = 2) (ι : Additive ↥Bs ≃+ V) {φ : MulAut ↥Bs}
    (hφ : GGIsReflection 3 φ) (hg : ggLin (p := 3) ι φ ∈ e6Weyl hα) :
    ∃ v : V, ∃ hv : B v v = 2, ggLin (p := 3) ι φ = rootRefl (B := B) v hv := by
  obtain ⟨x, f, hfx, hform⟩ := exists_of_ggIsReflection (p := 3) ι hφ
  have hxx : B x x = 2 :=
    bilinForm_self_eq_two_of_mem_e6Weyl hP hV hB hα hg hfx hform
  have hf : ∀ u, f u = B x u := by
    have hiso : ∀ u w : V, B (ggLin (p := 3) ι φ u) (ggLin (p := 3) ι φ w) = B u w :=
      bilinForm_apply_e6Weyl hP hV hB hα hg
    have hsym : ∀ u w : V, B u w = B w u := fun u w => bilinForm_symm hP hV hB u w
    have h2 : (2 : ZMod 3) * 2 = 1 := by decide
    intro u
    have hmul : f u * B x x = 2 * B x u := by
      have h := hiso u x
      rw [hform u, hform x, hfx] at h
      have hv2 : x - (2 : ZMod 3) • x = -x := by module
      rw [hv2] at h
      have hexp : B (u - f u • x) (-x) = -(B u x - f u * B x x) := by
        simp only [LinearMap.BilinForm.neg_right, LinearMap.BilinForm.sub_left,
          LinearMap.BilinForm.smul_left]
        rfl
      have h2' : -(B u x - f u * B x x) = B u x := hexp.symm.trans h
      have h3 : f u * B x x - B u x = B u x :=
        (neg_sub (B u x) (f u * B x x)).symm.trans h2'
      have h4 : f u * B x x = B u x + B u x := sub_eq_iff_eq_add.mp h3
      have h5 : B u x + B u x = 2 * B u x := by
        rw [show (2 : ZMod 3) * B u x = B u x + B u x from by ring]
      rw [h4, h5, hsym x u]
    have hfin : f u * 2 = 2 * B x u := by rwa [hxx] at hmul
    calc f u = f u * 1 := (mul_one _).symm
      _ = f u * ((2 : ZMod 3) * 2) := by rw [h2]
      _ = (f u * 2) * 2 := by ring
      _ = (2 * B x u) * 2 := by rw [hfin]
      _ = B x u * ((2 : ZMod 3) * 2) := by ring
      _ = B x u := by rw [h2, mul_one]
  refine ⟨x, hxx, ?_⟩
  apply LinearEquiv.ext
  intro u
  rw [hform u, hf u, rootRefl_apply]

section SOf

variable {G : Type} [Group G] {Bs : Subgroup G}

noncomputable def SOf (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs)) : Set V :=
  {v | ∃ hv : B v v = 2, rootRefl (B := B) v hv ∈ A.map (ggLin (p := 3) ι)}

theorem mem_SOf_iff {ι : Additive ↥Bs ≃+ V} {A : Subgroup (MulAut ↥Bs)} {v : V} :
    v ∈ SOf (B := B) ι A ↔ ∃ hv : B v v = 2,
      rootRefl (B := B) v hv ∈ A.map (ggLin (p := 3) ι) := Iff.rfl

end SOf

theorem exists_mem_e6Weyl_apply_eq_of_norm_two
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v)
    (hα : ∀ i, α i (h i) = 2) {u v : V} (hu : B u u = 2) (hv : B v v = 2) :
    ∃ g ∈ e6Weyl hα, g u = v := by
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0] at hu
    simp at hu
    exact absurd hu (by decide)
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp at hv
    exact absurd hv (by decide)
  exact exists_mem_e6Weyl_apply_eq hP hV hB hα hu0 hv0 (hu.trans hv.symm)

end CFSG.StandardType.E6QTwo

end
