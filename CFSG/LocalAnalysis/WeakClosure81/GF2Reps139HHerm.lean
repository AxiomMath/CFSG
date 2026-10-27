module

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open scoped Matrix

theorem lemmaH_herm {E V : Type} [Field E] [Finite E] [CharP E 2] [AddCommGroup V] [Module E V]
    [Module.Finite E V] (θ : E →+* E) (hθ : ∀ e, θ (θ e) = e) (hθ1 : θ ≠ RingHom.id E)
    (hdim : 3 ≤ Module.finrank E V) (A : Submodule E V)
    (hA : Module.finrank E A + 1 = Module.finrank E V) (h : V →ₗ[E] V →ₛₗ[θ] E)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) (hherm : ∀ x y, h y x = θ (h x y)) :
    Nat.card {g : V ≃ₗ[E] V | (∀ v, g v - v ∈ A) ∧ (∀ a ∈ A, g a = a) ∧
      ∃ l : E, l ≠ 0 ∧ ∀ x y, h (g x) (g y) = l * h x y} ≤ Nat.card {c : E // θ c = c} := by
  classical
  haveI : Finite V := Module.finite_of_finite E
  have hsep_right : ∀ c : V, (∀ y, h y c = 0) → c = 0 := by
    intro c hc
    refine hnd c fun y => ?_
    have h1 : θ (h c y) = 0 := by rw [← hherm c y]; exact hc y
    exact (map_eq_zero_iff θ (RingHom.injective θ)).mp h1
  have hflip_inj : Function.Injective (fun c : V => h.flip c) := by
    intro c d hcd
    have h1 : h.flip c = h.flip d := hcd
    have h2 : ∀ y, h y c = h y d := by
      intro y
      have := congrArg (fun f => f y) h1
      simpa only [LinearMap.flip_apply] using this
    have hzero : c - d = 0 := by
      apply hsep_right
      intro y
      rw [map_sub, h2 y, sub_self]
    exact sub_eq_zero.mp hzero
  have hflip_surj : Function.Surjective (fun c : V => h.flip c) := by
    have hcard : Nat.card V = Nat.card (V →ₗ[E] E) := by
      rw [Module.natCard_eq_pow_finrank (K := E) (V := V →ₗ[E] E),
          Module.natCard_eq_pow_finrank (K := E) (V := V),
          Subspace.dual_finrank_eq]
    haveI : Finite (V → E) := by infer_instance
    haveI : Finite (V →ₗ[E] E) :=
      Finite.of_injective (fun f : V →ₗ[E] E => (f : V → E)) (fun f g h => by
        ext x; exact congrFun h x)
    haveI : Fintype V := Fintype.ofFinite V
    haveI : Fintype (V →ₗ[E] E) := Fintype.ofFinite _
    have hcardF : Fintype.card V = Fintype.card (V →ₗ[E] E) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard
    let e : V ≃ (V →ₗ[E] E) := Fintype.equivOfCardEq hcardF
    have hcomp : Function.Injective (fun c : V => e.symm (h.flip c)) := by
      intro c d hcd
      apply hflip_inj
      exact e.symm.injective hcd
    have hsurj : Function.Surjective (fun c : V => e.symm (h.flip c)) :=
      Finite.surjective_of_injective hcomp
    intro φ
    obtain ⟨c, hc⟩ := hsurj (e.symm φ)
    exact ⟨c, by simpa using congrArg e hc⟩
  have hA_ne_top : A ≠ ⊤ := by
    intro htop
    have hh := hA
    rw [htop, finrank_top] at hh
    omega
  obtain ⟨f, hfne, hAle⟩ := Submodule.exists_le_ker_of_lt_top A (lt_of_le_of_ne le_top hA_ne_top)
  obtain ⟨c₀, hc₀⟩ := hflip_surj f
  change h.flip c₀ = f at hc₀
  have hc₀_ne : c₀ ≠ 0 := by
    intro h0
    apply hfne
    rw [← hc₀, h0]
    simp
  have hker₀ : LinearMap.ker (h.flip c₀) = A := by
    have hle : A ≤ LinearMap.ker (h.flip c₀) := by
      intro a ha
      rw [LinearMap.mem_ker, hc₀]
      exact hAle ha
    have heq : A = LinearMap.ker (h.flip c₀) := by
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero (f := h.flip c₀)
        (by rw [hc₀]; exact hfne)
      omega
    exact heq.symm
  have hc₀_mem : c₀ ∈ Submodule.orthogonalBilin h A := by
    rw [Submodule.mem_orthogonalBilin]
    intro a ha
    show (h.flip c₀) a = 0
    rw [hc₀]
    exact hAle ha
  have hAperp_eq : Submodule.orthogonalBilin h A = Submodule.span E {c₀} := by
    refine le_antisymm ?_ ?_
    · intro w hw
      rw [Submodule.mem_span_singleton]
      have hker_le : A ≤ LinearMap.ker (h.flip w) := by
        intro a ha
        rw [LinearMap.mem_ker, LinearMap.flip_apply]
        exact (Submodule.mem_orthogonalBilin.mp hw) a ha
      by_cases hw0 : h.flip w = 0
      · have hwzero : w = 0 := hsep_right w (fun y => by
          have := congrArg (fun φ : V →ₗ[E] E => φ y) hw0
          simpa only [LinearMap.flip_apply, LinearMap.zero_apply] using this)
        exact ⟨0, by rw [hwzero, zero_smul]⟩
      · have hkerw : LinearMap.ker (h.flip w) = A := by
          have heq : A = LinearMap.ker (h.flip w) := by
            refine Submodule.eq_of_le_of_finrank_eq hker_le ?_
            have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero (f := h.flip w) hw0
            omega
          exact heq.symm
        have hle : LinearMap.ker (h.flip c₀) ≤ LinearMap.ker (h.flip w) := by
          rw [hker₀, hkerw]
        have hspan : h.flip w ∈ Submodule.span E (Set.range (fun _ : Unit => h.flip c₀)) :=
          mem_span_of_iInf_ker_le_ker (ι := Unit) (L := fun _ => h.flip c₀) (K := h.flip w)
            (by simpa using hle)
        rw [Set.range_const] at hspan
        obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hspan
        obtain ⟨ν, hν⟩ : ∃ ν : E, θ ν = μ :=
          (Finite.surjective_of_injective (RingHom.injective θ)) μ
        refine ⟨ν, ?_⟩
        apply sub_eq_zero.mp
        apply hsep_right
        intro y
        have h1 : h y (ν • c₀) = μ * h y c₀ := by
          rw [LinearMap.map_smulₛₗ, hν, smul_eq_mul]
        have h2 : h y w = μ * h y c₀ := by
          have := congrArg (fun φ : V →ₗ[E] E => φ y) hμ
          simpa only [LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul] using this.symm
        rw [map_sub, h2, h1, sub_self]
    · intro w hw
      rw [Submodule.mem_span_singleton] at hw
      obtain ⟨ν, rfl⟩ := hw
      rw [Submodule.mem_orthogonalBilin]
      intro a ha
      rw [LinearMap.map_smulₛₗ,
        show h a c₀ = 0 from (Submodule.mem_orthogonalBilin.mp hc₀_mem) a ha, smul_zero]
  have hnotiso : ¬ (A ≤ Submodule.orthogonalBilin h A) := by
    intro hle
    have h1 : Module.finrank E A ≤ Module.finrank E (Submodule.orthogonalBilin h A) :=
      Submodule.finrank_mono hle
    rw [hAperp_eq, finrank_span_singleton hc₀_ne] at h1
    omega
  obtain ⟨a, haA, a', ha'A, haa⟩ : ∃ a ∈ A, ∃ a' ∈ A, h a a' ≠ 0 := by
    by_contra hcon
    apply hnotiso
    intro x hx
    rw [Submodule.mem_orthogonalBilin]
    intro y hy
    by_contra hne
    exact hcon ⟨y, hy, x, hx, hne⟩
  obtain ⟨y, hyA⟩ : ∃ y : V, y ∉ A := by
    by_contra hcon
    apply hA_ne_top
    rw [Submodule.eq_top_iff']
    intro x
    by_contra hx
    exact hcon ⟨x, hx⟩
  let x₀ : V := (h y c₀)⁻¹ • y
  have hyc : h y c₀ ≠ 0 := by
    intro h0
    apply hyA
    rw [← hker₀, LinearMap.mem_ker, LinearMap.flip_apply, h0]
  have hx₀c : h x₀ c₀ = 1 := by
    dsimp [x₀]
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hyc]
  have hx₀ : x₀ ∉ A := by
    intro hx
    rw [← hker₀, LinearMap.mem_ker, LinearMap.flip_apply, hx₀c] at hx
    exact one_ne_zero hx
  have htop : A ⊔ Submodule.span E {x₀} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hx₀, hA]
  have hl1 : ∀ (g : V ≃ₗ[E] V) (l : E), (∀ a ∈ A, g a = a) →
      (∀ x y, h (g x) (g y) = l * h x y) → l = 1 := by
    intro g l hfix hl
    have h := hl a a'
    rw [hfix a haA, hfix a' ha'A] at h
    exact mul_right_cancel₀ haa (by rw [one_mul]; exact h.symm)
  have hgAperp : ∀ (g : V ≃ₗ[E] V), (∀ v, g v - v ∈ A) → (∀ a ∈ A, g a = a) →
      (∃ l : E, l ≠ 0 ∧ ∀ x y, h (g x) (g y) = l * h x y) →
      g x₀ - x₀ ∈ Submodule.orthogonalBilin h A := by
    intro g hgv hfix hl
    obtain ⟨l, hlne, hlxy⟩ := hl
    have hl1' : l = 1 := hl1 g l hfix hlxy
    rw [Submodule.mem_orthogonalBilin]
    intro a ha
    have h1 : h a (g x₀) = l * h a x₀ := by
      rw [← hfix a ha, hlxy a x₀, hfix a ha]
    rw [map_sub, h1, hl1', one_mul, sub_self]
  let P : (V ≃ₗ[E] V) → Prop := fun g => (∀ v, g v - v ∈ A) ∧ (∀ a ∈ A, g a = a) ∧
    ∃ l : E, l ≠ 0 ∧ ∀ x y, h (g x) (g y) = l * h x y
  change Nat.card {g : V ≃ₗ[E] V | P g} ≤ Nat.card {c : E // θ c = c}
  by_cases hcc : h c₀ c₀ = 0
  ·
    have hnormal : ∀ g : {g : V ≃ₗ[E] V | P g}, ∃ α : E,
        (∀ x, g.1 x = x + (α * h x c₀) • c₀) ∧ θ α = α := by
      intro g
      have hgA := hgAperp g.1 g.2.1 g.2.2.1 g.2.2.2
      have hmem : g.1 x₀ - x₀ ∈ Submodule.span E {c₀} := by
        rw [← hAperp_eq]; exact hgA
      obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hmem
      have hnormal_form : ∀ x, g.1 x = x + (α * h x c₀) • c₀ := by
        intro x
        have hxmem : x ∈ A ⊔ Submodule.span E {x₀} := by rw [htop]; trivial
        obtain ⟨a, ha, z, hz, hxz⟩ := Submodule.mem_sup.mp hxmem
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
        have hac₀ : h a c₀ = 0 := (Submodule.mem_orthogonalBilin.mp hc₀_mem) a ha
        have ht : t = h x c₀ := by
          have h1 : h x c₀ = t * h x₀ c₀ := by
            rw [← hxz, LinearMap.map_add₂, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
            rw [hac₀, zero_add, hx₀c, mul_one]
          rw [h1, hx₀c, mul_one]
        have hshape : g.1 x - x = t • (g.1 x₀ - x₀) := by
          rw [← hxz, map_add, map_smul, g.2.2.1 a ha, smul_sub]
          abel
        calc g.1 x = x + (g.1 x - x) := by abel
          _ = x + t • (g.1 x₀ - x₀) := by rw [hshape]
          _ = x + t • (α • c₀) := by rw [← hα]
          _ = x + (t * α) • c₀ := by rw [smul_smul]
          _ = x + (α * h x c₀) • c₀ := by rw [ht]; congr 1; rw [mul_comm]
      have htheta : θ α = α := by
        have hexp : ∀ x y, h (g.1 x) (g.1 y)
            = h x y + (θ α + α) * (h x c₀ * θ (h y c₀)) := by
          intro x y
          rw [hnormal_form x, hnormal_form y]
          simp only [map_add, LinearMap.map_add₂, LinearMap.add_apply, map_smulₛₗ,
            map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply]
          rw [hherm y c₀, hcc]
          ring
        have h1 : h (g.1 x₀) (g.1 x₀) = h x₀ x₀ := by
          obtain ⟨l, _, hlxy⟩ := g.2.2.2
          rw [hlxy x₀ x₀, hl1 g.1 l g.2.2.1 hlxy, one_mul]
        have h2 := hexp x₀ x₀
        rw [h1] at h2
        have h3 : (θ α + α) * (h x₀ c₀ * θ (h x₀ c₀)) = 0 :=
          (add_left_cancel (show h x₀ x₀ + 0 = h x₀ x₀ + (θ α + α) *
            (h x₀ c₀ * θ (h x₀ c₀)) from by rw [add_zero]; exact h2)).symm
        rw [hx₀c, map_one, mul_one, mul_one] at h3
        exact (CharTwo.add_eq_zero).mp h3
      exact ⟨α, hnormal_form, htheta⟩
    let F : {g : V ≃ₗ[E] V | P g} → {c : E // θ c = c} :=
      fun g => ⟨Classical.choose (hnormal g), (Classical.choose_spec (hnormal g)).2⟩
    have hF_inj : Function.Injective F := by
      intro g g' hgg
      have hαeq : Classical.choose (hnormal g) = Classical.choose (hnormal g') := by
        have := congrArg Subtype.val hgg
        simpa [F] using this
      apply Subtype.ext
      ext x
      rw [(Classical.choose_spec (hnormal g)).1 x, (Classical.choose_spec (hnormal g')).1 x,
        hαeq]
    exact Nat.card_le_card_of_injective F hF_inj
  ·
    have hSsub : ∀ g : {g : V ≃ₗ[E] V | P g}, g.1 = 1 := by
      intro g
      by_contra hg1
      have hgx₀ : g.1 x₀ ≠ x₀ := by
        intro hx
        apply hg1
        ext x
        have hxmem : x ∈ A ⊔ Submodule.span E {x₀} := by rw [htop]; trivial
        obtain ⟨a, ha, z, hz, hxz⟩ := Submodule.mem_sup.mp hxmem
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
        rw [← hxz, map_add, map_smul, g.2.2.1 a ha, hx]
        rfl
      have hwA : g.1 x₀ - x₀ ∈ A := g.2.1 x₀
      have hwAperp : g.1 x₀ - x₀ ∈ Submodule.orthogonalBilin h A :=
        hgAperp g.1 g.2.1 g.2.2.1 g.2.2.2
      have hww : h (g.1 x₀ - x₀) (g.1 x₀ - x₀) = 0 :=
        (Submodule.mem_orthogonalBilin.mp hwAperp) (g.1 x₀ - x₀) hwA
      have hmem : g.1 x₀ - x₀ ∈ Submodule.span E {c₀} := by
        rw [← hAperp_eq]; exact hwAperp
      obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp hmem
      have hνne : ν ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hν
        exact hgx₀ (sub_eq_zero.mp hν.symm)
      have hνθν : ν * θ ν ≠ 0 := mul_ne_zero hνne (fun h0 =>
        hνne ((map_eq_zero_iff θ (RingHom.injective θ)).mp h0))
      have hthis : (ν * θ ν) * h c₀ c₀ = 0 := by
        have hww' : h (ν • c₀) (ν • c₀) = 0 := by rw [hν]; exact hww
        rwa [show h (ν • c₀) (ν • c₀) = (ν * θ ν) * h c₀ c₀ from by
          simp only [map_smul, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]
          ring] at hww'
      exact hcc ((mul_eq_zero.mp hthis).resolve_left hνθν)
    have hcard1 : Nat.card {g : V ≃ₗ[E] V | P g} ≤ 1 := by
      have hinj : Function.Injective (fun _ : {g : V ≃ₗ[E] V | P g} => ()) :=
        fun a b _ => Subtype.ext (by rw [hSsub a, hSsub b])
      simpa using Nat.card_le_card_of_injective (fun _ : {g : V ≃ₗ[E] V | P g} => ()) hinj
    have hE₀ : 1 ≤ Nat.card {c : E // θ c = c} := by
      haveI : Nonempty {c : E // θ c = c} := ⟨⟨0, map_zero θ⟩⟩
      exact Nat.card_pos
    omega

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
