module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open scoped Matrix

theorem lemmaH_alt {E V : Type} [Field E] [Finite E] [CharP E 2] [AddCommGroup V] [Module E V]
    [Module.Finite E V] (hdim : 3 ≤ Module.finrank E V) (A : Submodule E V)
    (hA : Module.finrank E A + 1 = Module.finrank E V) (b : LinearMap.BilinForm E V)
    (hb : b.Nondegenerate) (halt : b.IsAlt) :
    Nat.card {g : V ≃ₗ[E] V | (∀ v, g v - v ∈ A) ∧ (∀ a ∈ A, g a = a) ∧
      ∃ l : E, l ≠ 0 ∧ ∀ x y, b (g x) (g y) = l * b x y} ≤ Nat.card E := by
  classical
  haveI : Finite V := Module.finite_of_finite E
  have hA' : Module.finrank E V = Module.finrank E A + 1 := hA.symm
  have hfin : Module.finrank E (b.orthogonal A) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hb A, hA']
    omega
  have hA_ne_top : A ≠ ⊤ := by
    intro h
    have hh := hA
    rw [h, finrank_top] at hh
    omega
  have hx₀ : ∃ x₀ : V, x₀ ∉ A := by
    by_contra h
    exact hA_ne_top (Submodule.eq_top_iff'.mpr fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  obtain ⟨x₀, hx₀⟩ := hx₀
  have htop : A ⊔ Submodule.span E {x₀} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hx₀, hA]
  have hnotiso : ¬ (A ≤ b.orthogonal A) := by
    intro hle
    have h1 : Module.finrank E A ≤ Module.finrank E (b.orthogonal A) :=
      Submodule.finrank_mono hle
    rw [hfin] at h1
    omega
  obtain ⟨a, haA, ha_not⟩ : ∃ a ∈ A, a ∉ b.orthogonal A := by
    by_contra h
    exact hnotiso fun x hx => by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      by_contra hne
      exact h ⟨x, hx, fun hxmem =>
        hne ((LinearMap.BilinForm.mem_orthogonal_iff.mp hxmem) n hn)⟩
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at ha_not
  obtain ⟨n, hnotimp⟩ := not_forall.mp ha_not
  obtain ⟨hnA, hnne⟩ := not_imp.mp hnotimp
  have hc_mem : ∀ g : {g : V ≃ₗ[E] V // (∀ v, g v - v ∈ A) ∧ (∀ a ∈ A, g a = a) ∧
      ∃ l : E, l ≠ 0 ∧ ∀ x y, b (g x) (g y) = l * b x y},
      g.1 x₀ - x₀ ∈ b.orthogonal A := by
    intro g
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro a' ha'
    obtain ⟨l, _hlne, hl⟩ := g.2.2.2
    have hl1 : l = 1 := by
      have h := hl n a
      rw [g.2.2.1 n hnA, g.2.2.1 a haA] at h
      exact mul_right_cancel₀ hnne (by rw [one_mul]; exact h.symm)
    have h1 : b a' (g.1 x₀) = l * b a' x₀ := by
      rw [← g.2.2.1 a' ha', hl a' x₀, g.2.2.1 a' ha']
    calc b a' (g.1 x₀ - x₀) = b a' (g.1 x₀) - b a' x₀ := map_sub (b a') (g.1 x₀) x₀
      _ = l * b a' x₀ - b a' x₀ := by rw [h1]
      _ = 0 := by rw [hl1, one_mul, sub_self]
  let F : {g : V ≃ₗ[E] V // (∀ v, g v - v ∈ A) ∧ (∀ a ∈ A, g a = a) ∧
      ∃ l : E, l ≠ 0 ∧ ∀ x y, b (g x) (g y) = l * b x y} → b.orthogonal A :=
    fun g => ⟨g.1 x₀ - x₀, hc_mem g⟩
  have hF_inj : Function.Injective F := by
    intro g g' hgg'
    apply Subtype.ext
    refine LinearEquiv.ext fun v => ?_
    have hx : g.1 x₀ = g'.1 x₀ := by
      have h : g.1 x₀ - x₀ = g'.1 x₀ - x₀ := congrArg Subtype.val hgg'
      have h2 := congrArg (fun z : V => z + x₀) h
      simpa only [sub_add_cancel] using h2
    have hv : v ∈ A ⊔ Submodule.span E {x₀} := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hv
    obtain ⟨y, hyA, z, hz, hyz⟩ := hv
    rw [Submodule.mem_span_singleton] at hz
    obtain ⟨t, rfl⟩ := hz
    rw [← hyz]
    simp only [map_add, map_smul]
    rw [g.2.2.1 y hyA, g'.2.2.1 y hyA, hx]
  have hcard := Nat.card_le_card_of_injective F hF_inj
  haveI : Module.Finite E ↥(b.orthogonal A) := inferInstance
  have hcard_orth : Nat.card (b.orthogonal A) = Nat.card E := by
    rw [Module.natCard_eq_pow_finrank (K := E) (V := ↥(b.orthogonal A)), hfin, pow_one]
  rw [hcard_orth] at hcard
  exact hcard

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
