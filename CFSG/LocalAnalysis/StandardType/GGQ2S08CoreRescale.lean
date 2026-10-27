module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialRefl
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.GroupTheory.Perm.ClosureSwap
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2s08k3_index_eq {N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin N) (ZMod 3) V) {c d : ZMod 3} (hc : c ≠ 0)
    {i j : Fin N} (h : c • b i = d • b j) : i = j :=
  b.linearIndependent.eq_of_smul_apply_eq_smul_apply c d i j hc h

private lemma ggQ2s08k3_ext_basis {N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {b : Module.Basis (Fin N) (ZMod 3) V} {e₁ e₂ : V ≃ₗ[ZMod 3] V}
    (h : ∀ k, e₁ (b k) = e₂ (b k)) : e₁ = e₂ := by
  apply LinearEquiv.ext
  intro v
  have h' : (e₁ : V →ₗ[ZMod 3] V) = (e₂ : V →ₗ[ZMod 3] V) := by
    apply Module.Basis.ext
    exact h
  exact congrArg (fun f : V →ₗ[ZMod 3] V => f v) h'

private lemma ggQ2s08k3_coeff_fixed {N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin N) (ZMod 3) V) {xv : V}
    (x : Fin N → ZMod 3) (hx : xv = ∑ i, x i • b i)
    (w : V ≃ₗ[ZMod 3] V) (σ : Equiv.Perm (Fin N)) (c : Fin N → ZMod 3)
    (hw : w xv = xv) (hb : ∀ i, w (b i) = c i • b (σ i)) :
    ∀ j, x (σ j) = x j * c j := by
  have hwx : w xv = ∑ j, (x j * c j) • b (σ j) := by
    rw [hx, map_sum]
    congr 1
    ext j
    rw [LinearEquiv.map_smul, hb j, smul_smul]
  have hreindex : ∑ j, (x j * c j) • b (σ j) =
      ∑ k, (x (σ.symm k) * c (σ.symm k)) • b k := by
    simpa using (Equiv.sum_comp σ.symm (fun j => (x j * c j) • b (σ j))).symm
  have hxeq : ∑ k, (x (σ.symm k) * c (σ.symm k)) • b k = xv := by
    rw [← hreindex, ← hwx, hw]
  have hfun : (fun k => x (σ.symm k) * c (σ.symm k)) = x := by
    have h := congrArg (fun v => b.repr v) (hxeq.trans hx)
    have h1 := b.repr_sum_self (fun k => x (σ.symm k) * c (σ.symm k))
    have h2 := b.repr_sum_self x
    have h' := congrArg (fun f : Fin N →₀ ZMod 3 => (f : Fin N → ZMod 3)) h
    rw [h1, h2] at h'
    exact h'
  intro j
  have := congrFun hfun (σ j)
  simpa [Equiv.symm_apply_apply] using this.symm

private lemma ggQ2s08k3_prod_rescale {N : ℕ} (x : Fin N → ZMod 3) (hx : ∀ i, x i ≠ 0)
    (σ : Equiv.Perm (Fin N)) (ε : Fin N → ZMod 3) :
    ∏ i, (x i * ε i * (x (σ i))⁻¹) = ∏ i, ε i := by
  have hsq : ∀ b : ZMod 3, b ≠ 0 → b * b = 1 := by decide
  have hx_inv : ∀ i, (x i)⁻¹ = x i := by
    intro i
    have h := hsq (x i) (hx i)
    exact (eq_inv_of_mul_eq_one_right h).symm
  have hprod_x_inv : ∏ i, (x (σ i))⁻¹ = ∏ i, x i := by
    simp only [hx_inv]
    exact Equiv.prod_comp σ x
  have hx_sq : (∏ i, x i) * (∏ i, x i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    exact hsq (x i) (hx i)
  calc ∏ i, (x i * ε i * (x (σ i))⁻¹)
      = (∏ i, x i) * (∏ i, ε i) * (∏ i, (x (σ i))⁻¹) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, mul_assoc]
    _ = (∏ i, x i) * (∏ i, ε i) * (∏ i, x i) := by rw [hprod_x_inv]
    _ = (∏ i, x i) * (∏ i, x i) * (∏ i, ε i) := by rw [mul_right_comm]
    _ = 1 * (∏ i, ε i) := by rw [hx_sq]
    _ = ∏ i, ε i := by rw [one_mul]

private lemma ggQ2s08k3_mono_iff {N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin N) (ZMod 3) V) (x : Fin N → ZMod 3) (hx : ∀ i, x i ≠ 0)
    (f : Module.Basis (Fin N) (ZMod 3) V) (hf : ∀ i, f i = x i • b i)
    (a : V ≃ₗ[ZMod 3] V) :
    GGQ2S08Mono b a ↔ GGQ2S08Mono f a := by
  constructor
  · rintro ⟨σ, ε, hε, hεa⟩
    refine ⟨σ, fun i => x i * ε i * (x (σ i))⁻¹, ?_, ?_⟩
    · intro i
      exact mul_ne_zero (mul_ne_zero (hx i) (hε i)) (inv_ne_zero (hx (σ i)))
    · intro i
      have hb : b (σ i) = (x (σ i))⁻¹ • f (σ i) := by
        rw [hf (σ i), smul_smul, inv_mul_cancel₀ (hx (σ i)), one_smul]
      calc a (f i) = a (x i • b i) := by rw [hf i]
        _ = x i • a (b i) := by rw [LinearEquiv.map_smul]
        _ = x i • (ε i • b (σ i)) := by rw [hεa i]
        _ = (x i * ε i) • b (σ i) := by rw [smul_smul]
        _ = (x i * ε i) • ((x (σ i))⁻¹ • f (σ i)) := by rw [hb]
        _ = (x i * ε i * (x (σ i))⁻¹) • f (σ i) := by rw [smul_smul]
  · rintro ⟨σ, ε, hε, hεa⟩
    refine ⟨σ, fun i => (x i)⁻¹ * ε i * x (σ i), ?_, ?_⟩
    · intro i
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hx i)) (hε i)) (hx (σ i))
    · intro i
      have hb : b i = (x i)⁻¹ • f i := by
        rw [hf i, smul_smul, inv_mul_cancel₀ (hx i), one_smul]
      calc a (b i) = a ((x i)⁻¹ • f i) := by rw [hb]
        _ = (x i)⁻¹ • a (f i) := by rw [LinearEquiv.map_smul]
        _ = (x i)⁻¹ • (ε i • f (σ i)) := by rw [hεa i]
        _ = ((x i)⁻¹ * ε i) • f (σ i) := by rw [smul_smul]
        _ = ((x i)⁻¹ * ε i) • (x (σ i) • b (σ i)) := by rw [hf (σ i)]
        _ = ((x i)⁻¹ * ε i * x (σ i)) • b (σ i) := by rw [smul_smul]

private lemma ggQ2s08k3_monoEven_iff {N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin N) (ZMod 3) V) (x : Fin N → ZMod 3) (hx : ∀ i, x i ≠ 0)
    (f : Module.Basis (Fin N) (ZMod 3) V) (hf : ∀ i, f i = x i • b i)
    (a : V ≃ₗ[ZMod 3] V) :
    GGQ2S08MonoEven b a ↔ GGQ2S08MonoEven f a := by
  constructor
  · rintro ⟨σ, ε, hε, hprod, hεa⟩
    refine ⟨σ, fun i => x i * ε i * (x (σ i))⁻¹, ?_, ?_, ?_⟩
    · intro i
      exact mul_ne_zero (mul_ne_zero (hx i) (hε i)) (inv_ne_zero (hx (σ i)))
    · rw [ggQ2s08k3_prod_rescale x hx σ ε, hprod]
    · intro i
      have hb : b (σ i) = (x (σ i))⁻¹ • f (σ i) := by
        rw [hf (σ i), smul_smul, inv_mul_cancel₀ (hx (σ i)), one_smul]
      calc a (f i) = a (x i • b i) := by rw [hf i]
        _ = x i • a (b i) := by rw [LinearEquiv.map_smul]
        _ = x i • (ε i • b (σ i)) := by rw [hεa i]
        _ = (x i * ε i) • b (σ i) := by rw [smul_smul]
        _ = (x i * ε i) • ((x (σ i))⁻¹ • f (σ i)) := by rw [hb]
        _ = (x i * ε i * (x (σ i))⁻¹) • f (σ i) := by rw [smul_smul]
  · rintro ⟨σ, ε, hε, hprod, hεa⟩
    refine ⟨σ, fun i => (x i)⁻¹ * ε i * x (σ i), ?_, ?_, ?_⟩
    · intro i
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hx i)) (hε i)) (hx (σ i))
    · have hprod' : ∏ i, ((x i)⁻¹ * ε i * x (σ i)) = ∏ i, ε i := by
        have hsq : ∀ b : ZMod 3, b ≠ 0 → b * b = 1 := by decide
        have hx_inv : ∀ i, (x i)⁻¹ = x i := by
          intro i
          have h := hsq (x i) (hx i)
          exact (eq_inv_of_mul_eq_one_right h).symm
        have hprod_x_inv : ∏ i, (x i)⁻¹ = ∏ i, x i := by
          simp only [hx_inv]
        have hprod_x : ∏ i, x (σ i) = ∏ i, x i := Equiv.prod_comp σ x
        have hx_sq : (∏ i, x i) * (∏ i, x i) = 1 := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_eq_one
          intro i _
          exact hsq (x i) (hx i)
        calc ∏ i, ((x i)⁻¹ * ε i * x (σ i))
            = (∏ i, (x i)⁻¹) * (∏ i, ε i) * (∏ i, x (σ i)) := by
              rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, mul_assoc]
          _ = (∏ i, x i) * (∏ i, ε i) * (∏ i, x i) := by rw [hprod_x_inv, hprod_x]
          _ = (∏ i, x i) * (∏ i, x i) * (∏ i, ε i) := by rw [mul_right_comm]
          _ = 1 * (∏ i, ε i) := by rw [hx_sq]
          _ = ∏ i, ε i := by rw [one_mul]
      rw [hprod', hprod]
    · intro i
      have hb : b i = (x i)⁻¹ • f i := by
        rw [hf i, smul_smul, inv_mul_cancel₀ (hx i), one_smul]
      calc a (b i) = a ((x i)⁻¹ • f i) := by rw [hb]
        _ = (x i)⁻¹ • a (f i) := by rw [LinearEquiv.map_smul]
        _ = (x i)⁻¹ • (ε i • f (σ i)) := by rw [hεa i]
        _ = ((x i)⁻¹ * ε i) • f (σ i) := by rw [smul_smul]
        _ = ((x i)⁻¹ * ε i) • (x (σ i) • b (σ i)) := by rw [hf (σ i)]
        _ = ((x i)⁻¹ * ε i * x (σ i)) • b (σ i) := by rw [smul_smul]

theorem ggQ2s08core_rescale {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ} (hN : 4 ≤ N)
    (b : Module.Basis (Fin N) (ZMod 3) V) (R W : Subgroup (V ≃ₗ[ZMod 3] V))
    (hR : (∀ a, a ∈ R ↔ GGQ2S08Mono b a) ∨ (∀ a, a ∈ R ↔ GGQ2S08MonoEven b a))
    (hWR : W ≤ R) (hWgen : W = Subgroup.closure {s | s ∈ W ∧ GGLinRefl s})
    (xv : V) (hxall : ∀ i, b.repr xv i ≠ 0)
    (hWfix : ∀ w ∈ W, w xv = xv)
    (htrans : ∀ i j, ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b j) :
    ∃ f : Module.Basis (Fin N) (ZMod 3) V, xv = ∑ i, f i ∧
      (∀ a, a ∈ W ↔ ∃ σ : Equiv.Perm (Fin N), ∀ i, a (f i) = f (σ i)) ∧
      ((∀ a, a ∈ R ↔ GGQ2S08Mono f a) ∨ (∀ a, a ∈ R ↔ GGQ2S08MonoEven f a)) := by
  classical
  let x : Fin N → ZMod 3 := fun i => b.repr xv i
  have hx_ne : ∀ i, x i ≠ 0 := hxall
  let xu : Fin N → (ZMod 3)ˣ := fun i => Units.mk0 (x i) (hx_ne i)
  let f : Module.Basis (Fin N) (ZMod 3) V := b.unitsSMul xu
  have hf_apply : ∀ i, f i = x i • b i := by
    intro i
    rw [Module.Basis.unitsSMul_apply]
    simp [xu]
  have hx_sum : xv = ∑ i, x i • b i := by
    rw [← b.sum_repr xv]
  have hxv_f : xv = ∑ i, f i := by
    rw [hx_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hf_apply]
  have hmonW : ∀ a ∈ W, ∃ (σ : Equiv.Perm (Fin N)) (c : Fin N → ZMod 3),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i) := by
    intro a ha
    rcases hR with hR1 | hR2
    · exact (hR1 a).mp (hWR ha)
    · rcases (hR2 a).mp (hWR ha) with ⟨σ, c, hc, hprod, hcapply⟩
      exact ⟨σ, c, hc, hcapply⟩
  obtain ⟨π, hfirst, hsecond, hcomm, hprime⟩ := ggRC_monomial_hom (p := 3) b W hmonW
  let c : W → Fin N → ZMod 3 := fun w i => (hfirst w i).choose
  have hc_ne : ∀ (w : W) (i : Fin N), c w i ≠ 0 := fun w i => (hfirst w i).choose_spec.1
  have hc_apply : ∀ (w : W) (i : Fin N), (w : V ≃ₗ[ZMod 3] V) (b i) = c w i • b (π w i) :=
    fun w i => (hfirst w i).choose_spec.2
  have hcoeff : ∀ (w : W) (j : Fin N), x (π w j) = x j * c w j := by
    intro w j
    exact ggQ2s08k3_coeff_fixed b x hx_sum (w : V ≃ₗ[ZMod 3] V) (π w) (c w) (hWfix w w.2)
      (hc_apply w) j
  have hperm : ∀ (w : W) (i : Fin N), (w : V ≃ₗ[ZMod 3] V) (f i) = f (π w i) := by
    intro w i
    calc (w : V ≃ₗ[ZMod 3] V) (f i) = (w : V ≃ₗ[ZMod 3] V) (x i • b i) := by rw [hf_apply i]
      _ = x i • (w : V ≃ₗ[ZMod 3] V) (b i) := by rw [LinearEquiv.map_smul]
      _ = x i • (c w i • b (π w i)) := by rw [hc_apply w i]
      _ = (x i * c w i) • b (π w i) := by rw [smul_smul]
      _ = x (π w i) • b (π w i) := by rw [← hcoeff w i]
      _ = f (π w i) := by rw [hf_apply (π w i)]
  let G : Set (V ≃ₗ[ZMod 3] V) := {s | s ∈ W ∧ GGLinRefl s}
  have hG_gen : W = Subgroup.closure G := hWgen
  have hgen_swap : ∀ (w : W), (w : V ≃ₗ[ZMod 3] V) ∈ G → (π w).IsSwap := by
    intro w hw
    have hsRefl : GGLinRefl (w : V ≃ₗ[ZMod 3] V) := hw.2
    have hshape := ggRC_monomial_refl_shape (p := 3) (by decide) f (w : V ≃ₗ[ZMod 3] V) hsRefl (π w)
        (fun _ => 1) (fun _ => one_ne_zero) (fun i => by
          rw [one_smul]
          exact hperm w i)
    rcases hshape with ⟨i, hσ1, hcneg, hrest⟩ | ⟨i, j, hij, hswap, hprod, hrest⟩
    · exfalso
      exact absurd hcneg (by decide)
    · exact ⟨i, j, hij, hswap⟩
  have htrans_range : MulAction.IsPretransitive π.range (Fin N) := by
    refine ⟨fun i j => ?_⟩
    obtain ⟨w, hw, ε, hε, hwε⟩ := htrans i j
    refine ⟨⟨π ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩⟩, ?_⟩
    have hc := hc_apply ⟨w, hw⟩ i
    have heq : c ⟨w, hw⟩ i • b (π ⟨w, hw⟩ i) = ε • b j := by
      rw [← hc, hwε]
    have hidx : π ⟨w, hw⟩ i = j :=
      ggQ2s08k3_index_eq b (hc_ne ⟨w, hw⟩ i) heq
    change (π ⟨w, hw⟩) i = j
    exact hidx
  let G' : Set W := {w | (w : V ≃ₗ[ZMod 3] V) ∈ G}
  have hG'_gen : (⊤ : Subgroup W) = Subgroup.closure G' := by
    apply (Subgroup.map_injective (Subgroup.subtype_injective W))
    rw [Subgroup.map_top, MonoidHom.map_closure, Subgroup.range_subtype]
    have himg : Subgroup.subtype W '' G' = G := by
      ext s
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hs
        exact ⟨⟨s, hs.1⟩, hs, rfl⟩
    rw [himg, hG_gen]
  let S : Set (Equiv.Perm (Fin N)) := π '' G'
  have hS_swap : ∀ σ ∈ S, σ.IsSwap := by
    rintro σ ⟨w, hw, rfl⟩
    exact hgen_swap w hw
  have hS_closure : Subgroup.closure S = π.range := by
    change Subgroup.closure (π '' G') = π.range
    rw [← Subgroup.map_top π, hG'_gen, MonoidHom.map_closure]
  haveI : MulAction.IsPretransitive (Subgroup.closure S) (Fin N) := by
    rw [hS_closure]
    exact htrans_range
  have htop_closure : Subgroup.closure S = ⊤ :=
    closure_of_isSwap_of_isPretransitive hS_swap
  have hrange_top : π.range = ⊤ := by rw [← hS_closure, htop_closure]
  have hW_iff : ∀ a, a ∈ W ↔ ∃ σ : Equiv.Perm (Fin N), ∀ i, a (f i) = f (σ i) := by
    intro a
    constructor
    · intro ha
      refine ⟨π ⟨a, ha⟩, ?_⟩
      intro i
      exact hperm ⟨a, ha⟩ i
    · rintro ⟨σ, hσ⟩
      have hσ_mem : σ ∈ π.range := by rw [hrange_top]; exact Subgroup.mem_top σ
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hσ_mem
      have haeq : a = (w : V ≃ₗ[ZMod 3] V) := by
        apply ggQ2s08k3_ext_basis (b := f)
        intro i
        rw [hσ i, ← hw]
        exact (hperm w i).symm
      rw [haeq]
      exact w.2
  have hR_iff : (∀ a, a ∈ R ↔ GGQ2S08Mono f a) ∨ (∀ a, a ∈ R ↔ GGQ2S08MonoEven f a) := by
    rcases hR with hR1 | hR2
    · left
      intro a
      rw [hR1 a]
      exact ggQ2s08k3_mono_iff b x hx_ne f hf_apply a
    · right
      intro a
      rw [hR2 a]
      exact ggQ2s08k3_monoEven_iff b x hx_ne f hf_apply a
  exact ⟨f, hxv_f, hW_iff, hR_iff⟩

end CFSG.StandardType

end
