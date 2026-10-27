module

import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open Matrix
open scoped commutatorElement
open CFSG.Open
open Module QuadraticMap CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply coe_quadMinus)
open CFSG.ClassicalGroups.Orthogonal (reflect reflect_conj regular_quadMinus toLinEquiv
  toLinEquiv_apply statedOmega_eq_comap)

private theorem k328r3c_decomp {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (Z : V →ₗ[F] V) {ω : F} (h2 : (2 : F) = 0) (hω : ω ^ 2 + ω + 1 = 0)
    (hZ : ∀ v, Z (Z (Z v)) = v) (v : V) :
    ∃ a ∈ Module.End.eigenspace Z 1, ∃ u ∈ Module.End.eigenspace Z ω,
      ∃ w ∈ Module.End.eigenspace Z (ω ^ 2), v = a + u + w := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω4 : ω ^ 4 = ω := by linear_combination ω * hω3
  refine ⟨v + Z v + Z (Z v), ?_, v + ω ^ 2 • Z v + ω • Z (Z v), ?_,
    v + ω • Z v + ω ^ 2 • Z (Z v), ?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, one_smul, map_add, map_add, hZ]
    abel
  · rw [Module.End.mem_eigenspace_iff, map_add, map_add, map_smul, map_smul, hZ]
    linear_combination (norm := module) (-hω3) • Z v
  · rw [Module.End.mem_eigenspace_iff, map_add, map_add, map_smul, map_smul, hZ]
    linear_combination (norm := module) (-hω3) • Z v + (-hω4) • Z (Z v)
  · linear_combination (norm := module) (-h2) • v + (-hω) • Z v + (-hω) • Z (Z v)

private theorem k328r3c_polar_map {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (Z : V →ₗ[F] V) (hQ : ∀ v, Q (Z v) = Q v) (x y : V) :
    polar Q (Z x) (Z y) = polar Q x y := by
  rw [polar, polar, ← map_add, hQ, hQ, hQ]

private theorem k328r3c_polar_eig {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (Z : V →ₗ[F] V) (hQ : ∀ v, Q (Z v) = Q v) {α β : F}
    (hαβ : α * β ≠ 1) {x y : V} (hx : x ∈ Module.End.eigenspace Z α)
    (hy : y ∈ Module.End.eigenspace Z β) : polar Q x y = 0 := by
  have h := k328r3c_polar_map Q Z hQ x y
  rw [Module.End.mem_eigenspace_iff] at hx hy
  rw [hx, hy, polar_smul_left, polar_smul_right] at h
  have h' : (α * β - 1) * polar Q x y = 0 := by
    simp only [smul_eq_mul] at h
    linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hαβ)

private theorem k328r3c_map_eig {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (Z : V →ₗ[F] V) (hQ : ∀ v, Q (Z v) = Q v) {α : F}
    (hα : α ^ 2 ≠ 1) {x : V} (hx : x ∈ Module.End.eigenspace Z α) : Q x = 0 := by
  have h := hQ x
  rw [Module.End.mem_eigenspace_iff] at hx
  rw [hx, QuadraticMap.map_smul, smul_eq_mul] at h
  have h' : (α ^ 2 - 1) * Q x = 0 := by linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hα)

private theorem k328r3c_finrank_sum {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Z : V →ₗ[F] V) {ω : F} (h2 : (2 : F) = 0)
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hω2 : ω ^ 2 ≠ ω)
    (hZ : ∀ v, Z (Z (Z v)) = v) :
    finrank F V = finrank F (Module.End.eigenspace Z 1) + finrank F (Module.End.eigenspace Z ω) +
      finrank F (Module.End.eigenspace Z (ω ^ 2)) := by
  have hind := Module.End.eigenspaces_iSupIndep Z
  have hUW : Disjoint (Module.End.eigenspace Z ω) (Module.End.eigenspace Z (ω ^ 2)) :=
    hind.pairwiseDisjoint (Ne.symm hω2)
  have hP : Disjoint (Module.End.eigenspace Z 1)
      (Module.End.eigenspace Z ω ⊔ Module.End.eigenspace Z (ω ^ 2)) := by
    have := hind.disjoint_biSup (x := 1) (y := {ω, ω ^ 2}) (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨Ne.symm hω1, fun h => hω1 (by
        have : ω ^ 2 = 1 := h.symm
        have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
        linear_combination h3 - ω * this)⟩)
    rwa [iSup_insert, iSup_singleton] at this
  have htop : Module.End.eigenspace Z 1 ⊔
      (Module.End.eigenspace Z ω ⊔ Module.End.eigenspace Z (ω ^ 2)) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨a, ha, u, hu, w, hw, rfl⟩ := k328r3c_decomp Z h2 hω hZ v
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left ha)
      (Submodule.mem_sup_right (Submodule.mem_sup_left hu)))
      (Submodule.mem_sup_right (Submodule.mem_sup_right hw))
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Module.End.eigenspace Z ω)
    (Module.End.eigenspace Z (ω ^ 2))
  have h2' := Submodule.finrank_sup_add_finrank_inf_eq (Module.End.eigenspace Z 1)
    (Module.End.eigenspace Z ω ⊔ Module.End.eigenspace Z (ω ^ 2))
  rw [hUW.eq_bot, finrank_bot, add_zero] at h1
  rw [hP.eq_bot, finrank_bot, add_zero, htop, finrank_top] at h2'
  omega

private theorem k328r3c_eq_zero_of_perp {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (hnd : (polarBilin Q).Nondegenerate) (Z : V →ₗ[F] V)
    (hQ : ∀ v, Q (Z v) = Q v) {α β : F} (hα1 : α ≠ 1) (hαα : α * α ≠ 1)
    (hdec : ∀ y : V, ∃ a ∈ Module.End.eigenspace Z 1, ∃ s ∈ Module.End.eigenspace Z α,
      ∃ t ∈ Module.End.eigenspace Z β, y = a + s + t)
    {x : V} (hx : x ∈ Module.End.eigenspace Z α)
    (hperp : ∀ t ∈ Module.End.eigenspace Z β, polar Q t x = 0) : x = 0 := by
  refine hnd.1 x fun y => ?_
  obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hdec y
  rw [polarBilin_apply_apply, polar_add_right, polar_add_right,
    k328r3c_polar_eig Q Z hQ (by rwa [mul_one]) hx ha, k328r3c_polar_eig Q Z hQ hαα hx hs,
    polar_comm, hperp t ht]
  simp

private theorem k328r3c_finrank_le {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (A A' : Submodule F V)
    (h : ∀ w ∈ A', (∀ u ∈ A, polar Q u w = 0) → w = 0) : finrank F A' ≤ finrank F A := by
  let Φ : A' →ₗ[F] Module.Dual F A :=
    ((polarBilin Q).compl₁₂ A.subtype A'.subtype).flip
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply Subtype.ext
    refine h w w.2 fun u hu => ?_
    have := LinearMap.congr_fun hw ⟨u, hu⟩
    simpa [Φ] using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Subspace.dual_finrank_eq] at this

private theorem k328r3c_nondeg_fixed {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (hnd : (polarBilin Q).Nondegenerate) (Z : V →ₗ[F] V)
    (hQ : ∀ v, Q (Z v) = Q v) {ω : F} (hω1 : ω ≠ 1) (hω2 : ω ^ 2 ≠ 1)
    (hdec : ∀ y : V, ∃ a ∈ Module.End.eigenspace Z 1, ∃ u ∈ Module.End.eigenspace Z ω,
      ∃ w ∈ Module.End.eigenspace Z (ω ^ 2), y = a + u + w) :
    (polarBilin (Q.comp (Module.End.eigenspace Z 1).subtype)).Nondegenerate := by
  have key : ∀ x : Module.End.eigenspace Z 1,
      (∀ y : Module.End.eigenspace Z 1, polar Q (x : V) (y : V) = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    refine hnd.1 x fun y => ?_
    obtain ⟨a, ha, u, hu, w, hw, rfl⟩ := hdec y
    rw [polarBilin_apply_apply, polar_add_right, polar_add_right,
      k328r3c_polar_eig Q Z hQ (by rwa [one_mul]) x.2 hu,
      k328r3c_polar_eig Q Z hQ (by rwa [one_mul]) x.2 hw, hx ⟨a, ha⟩]
    simp
  have hpol : ∀ x y : Module.End.eigenspace Z 1,
      polarBilin (Q.comp (Module.End.eigenspace Z 1).subtype) x y = polar Q (x : V) (y : V) := by
    intro x y
    simp [polarBilin_apply_apply, polar, QuadraticMap.comp_apply]
  refine ⟨fun x hx => key x fun y => ?_, fun y hy => key y fun x => ?_⟩
  · rw [← hpol]; exact hx y
  · rw [polar_comm, ← hpol]; exact hy x

private theorem k328r3c_aniso_fixed {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (Z : V →ₗ[F] V)
    (hQ : ∀ v, Q (Z v) = Q v) {ω : F} (hω1 : ω ≠ 1) (hω2 : ω ^ 2 ≠ 1)
    (hdim : finrank F V = 8) (hU : finrank F (Module.End.eigenspace Z ω) = 3)
    (hnp : ¬ IsPlusType Q) {x : V} (hx : x ∈ Module.End.eigenspace Z 1) (hx0 : x ≠ 0)
    (hQx : Q x = 0) : False := by
  refine hnp ⟨Module.End.eigenspace Z ω ⊔ Submodule.span F {x}, ?_, ?_⟩
  · have hdisj : Disjoint (Module.End.eigenspace Z ω) (Submodule.span F {x}) := by
      rw [Submodule.disjoint_def]
      intro y hyU hyS
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hyS
      exact (Submodule.disjoint_def.1 ((Module.End.eigenspaces_iSupIndep Z).pairwiseDisjoint hω1)
        _ hyU (Submodule.smul_mem _ c hx))
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Module.End.eigenspace Z ω)
      (Submodule.span F {x})
    rw [hdisj.eq_bot, finrank_bot, finrank_span_singleton hx0, hU] at h
    omega
  · intro y hy
    obtain ⟨u, hu, s, hs, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQx, k328r3c_map_eig Q Z hQ hω2 hu,
      polar_smul_right, k328r3c_polar_eig Q Z hQ (by rwa [mul_one]) hu hx]
    simp

private theorem k328r3c_plane {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (P : Submodule F V)
    (hP : (polarBilin (Q.comp P.subtype)).Nondegenerate) (hdim : finrank F P = 2)
    (haniso : ∀ x ∈ P, x ≠ 0 → Q x ≠ 0) {b c : F} (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∃ pu ∈ P, ∃ pv ∈ P, ∀ s t : F, Q (s • pu + t • pv) = s ^ 2 + b * s * t + c * t ^ 2 := by
  have hnp : ¬ IsPlusType (Q.comp P.subtype) := by
    rintro ⟨W, hW, hWs⟩
    obtain ⟨w, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.1
      (show 0 < finrank F W by omega)
    exact haniso _ (w : P).2 (fun h => hw0 (Subtype.ext (Subtype.ext h))) (hWs w w.2)
  obtain ⟨e⟩ := nonempty_isometry_of_not_isPlusType hP (n := 1) le_rfl (by omega) hnp hbc
  set x₀ : Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → F := Pi.single (Sum.inr (Sum.inr 0)) 1 with hx₀
  set x₁ : Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → F := Pi.single (Sum.inr (Sum.inr 1)) 1 with hx₁
  refine ⟨((e.symm x₀ : P) : V), (e.symm x₀).2, ((e.symm x₁ : P) : V), (e.symm x₁).2,
    fun s t => ?_⟩
  have h := e.symm.map_app (s • x₀ + t • x₁)
  rw [map_add, map_smul, map_smul] at h
  have h' : (Q.comp P.subtype) (s • e.symm x₀ + t • e.symm x₁) =
      Q (s • ((e.symm x₀ : P) : V) + t • ((e.symm x₁ : P) : V)) := by
    simp [QuadraticMap.comp_apply]
  rw [← h', h, quadMinus_apply, Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega), zero_add]
  simp [x₀, x₁]

private theorem k328r3c_dual {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (A A' : Submodule F V)
    (hA : finrank F A = 3) (hA' : finrank F A' = 3)
    (h : ∀ w ∈ A', (∀ u ∈ A, polar Q u w = 0) → w = 0) :
    ∃ vv ww : Fin 3 → V, (∀ i, vv i ∈ A) ∧ (∀ i, ww i ∈ A') ∧
      ∀ i j, polar Q (vv i) (ww j) = if i = j then 1 else 0 := by
  let bA : Basis (Fin 3) F A := Module.finBasisOfFinrankEq F A hA
  let Φ : A' →ₗ[F] Module.Dual F A :=
    ((polarBilin Q).compl₁₂ A.subtype A'.subtype).flip
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply Subtype.ext
    refine h w w.2 fun u hu => ?_
    have := LinearMap.congr_fun hw ⟨u, hu⟩
    simpa [Φ] using this
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq, hA, hA'])).1 hinj
  choose w hw using fun j => hsurj (bA.dualBasis j)
  refine ⟨fun i => (bA i : V), fun j => (w j : V), fun i => (bA i).2, fun j => (w j).2,
    fun i j => ?_⟩
  have h1 : Φ (w j) (bA i) = if i = j then 1 else 0 := by
    rw [hw j, Basis.dualBasis_apply_self]
  have h2 : Φ (w j) (bA i) = polar Q (bA i : V) (w j : V) := by simp [Φ]
  rw [← h2, h1]

private theorem k328r3c_Q_sum {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (Z : V →ₗ[F] V) (hQ : ∀ v, Q (Z v) = Q v) {ω : F} (hω1 : ω ≠ 1)
    (hω2 : ω ^ 2 ≠ 1) (hω4 : (ω ^ 2) ^ 2 ≠ 1) {A B C : V}
    (hA : A ∈ Module.End.eigenspace Z ω) (hB : B ∈ Module.End.eigenspace Z (ω ^ 2))
    (hC : C ∈ Module.End.eigenspace Z 1) : Q (A + B + C) = polar Q A B + Q C := by
  rw [QuadraticMap.map_add Q (A + B) C, QuadraticMap.map_add Q A B, polar_add_left,
    k328r3c_map_eig Q Z hQ hω2 hA, k328r3c_map_eig Q Z hQ hω4 hB,
    k328r3c_polar_eig Q Z hQ (by rwa [mul_one]) hA hC,
    k328r3c_polar_eig Q Z hQ (by rwa [mul_one]) hB hC]
  ring

private theorem k328r3c_polar_sum {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (vv ww : Fin 3 → V)
    (hdual : ∀ i j, polar Q (vv i) (ww j) = if i = j then 1 else 0) (x y : Fin 3 → F) :
    polar Q (∑ i, x i • vv i) (∑ j, y j • ww j) = ∑ i, x i * y i := by
  rw [← polarBilin_apply_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, polarBilin_apply_apply,
    hdual, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem k328r3c_quadMinus_apply {F : Type} [Field F] (b c : F)
    (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    quadMinus 4 F b c x = ∑ i : Fin 3, x (.inl i) * x (.inr (.inl i)) + x (.inr (.inr 0)) ^ 2 +
      b * x (.inr (.inr 0)) * x (.inr (.inr 1)) + c * x (.inr (.inr 1)) ^ 2 :=
  quadMinus_apply 4 F b c x

private theorem k328r3c_comb_Q {F : Type} [Field F] (b c : F)
    (Z : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) →ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))
    (hQ : ∀ v, quadMinus 4 F b c (Z v) = quadMinus 4 F b c v) {ω : F}
    (hω1 : ω ≠ 1) (hω2 : ω ^ 2 ≠ 1) (hω4 : (ω ^ 2) ^ 2 ≠ 1)
    {vv ww : Fin 3 → Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F} {pu pv : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (hvv : ∀ i, vv i ∈ Module.End.eigenspace Z ω)
    (hww : ∀ i, ww i ∈ Module.End.eigenspace Z (ω ^ 2))
    (hpu : pu ∈ Module.End.eigenspace Z 1) (hpv : pv ∈ Module.End.eigenspace Z 1)
    (hdual : ∀ i j, polar (quadMinus 4 F b c) (vv i) (ww j) = if i = j then 1 else 0)
    (hplane : ∀ s t : F, quadMinus 4 F b c (s • pu + t • pv) = s ^ 2 + b * s * t + c * t ^ 2)
    (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    quadMinus 4 F b c (Fintype.linearCombination F (Sum.elim vv (Sum.elim ww ![pu, pv])) x) =
      quadMinus 4 F b c x := by
  have hMx : Fintype.linearCombination F (Sum.elim vv (Sum.elim ww ![pu, pv])) x =
      ∑ i, x (.inl i) • vv i + ∑ i, x (.inr (.inl i)) • ww i +
        (x (.inr (.inr 0)) • pu + x (.inr (.inr 1)) • pv) := by
    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, Fin.sum_univ_two, add_assoc]
  have hA : ∑ i, x (.inl i) • vv i ∈ Module.End.eigenspace Z ω :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvv i)
  have hB : ∑ i, x (.inr (.inl i)) • ww i ∈ Module.End.eigenspace Z (ω ^ 2) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hww i)
  have hC : x (.inr (.inr 0)) • pu + x (.inr (.inr 1)) • pv ∈ Module.End.eigenspace Z 1 :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hpu) (Submodule.smul_mem _ _ hpv)
  rw [hMx, k328r3c_Q_sum _ Z hQ hω1 hω2 hω4 hA hB hC, k328r3c_polar_sum _ vv ww hdual, hplane,
    k328r3c_quadMinus_apply b c x]
  ring

private theorem k328r3c_comb_Z {F : Type} [Field F] {ω : F}
    (Z : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) →ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))
    {vv ww : Fin 3 → Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F} {pu pv : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (hvv : ∀ i, vv i ∈ Module.End.eigenspace Z ω)
    (hww : ∀ i, ww i ∈ Module.End.eigenspace Z (ω ^ 2))
    (hpu : pu ∈ Module.End.eigenspace Z 1) (hpv : pv ∈ Module.End.eigenspace Z 1)
    (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    Z (Fintype.linearCombination F (Sum.elim vv (Sum.elim ww ![pu, pv])) x) =
      Fintype.linearCombination F (Sum.elim vv (Sum.elim ww ![pu, pv]))
        (Matrix.diagonal
          (Sum.elim (fun _ => ω) (Sum.elim (fun _ => ω ^ 2) fun _ => (1 : F))) *ᵥ x) := by
  have hcol : ∀ k, Z (Sum.elim vv (Sum.elim ww ![pu, pv]) k) =
      (Sum.elim (fun _ => ω) (Sum.elim (fun _ => ω ^ 2) fun _ => (1 : F)) :
        Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) k • Sum.elim vv (Sum.elim ww ![pu, pv]) k := by
    rintro (i | i | i)
    · exact Module.End.mem_eigenspace_iff.1 (hvv i)
    · exact Module.End.mem_eigenspace_iff.1 (hww i)
    · fin_cases i
      · exact Module.End.mem_eigenspace_iff.1 hpu
      · exact Module.End.mem_eigenspace_iff.1 hpv
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, hcol, Matrix.mulVec_diagonal,
    smul_smul]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]

private theorem k328r3c_frame {F : Type} [Field F] (b c : F) {ω : F}
    (hnd : (polarBilin (quadMinus 4 F b c)).Nondegenerate)
    (Z : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) →ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))
    (hQ : ∀ v, quadMinus 4 F b c (Z v) = quadMinus 4 F b c v)
    (hω1 : ω ≠ 1) (hω2 : ω ^ 2 ≠ 1) (hω4 : (ω ^ 2) ^ 2 ≠ 1)
    (vv ww : Fin 3 → Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) (pu pv : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (hvv : ∀ i, vv i ∈ Module.End.eigenspace Z ω)
    (hww : ∀ i, ww i ∈ Module.End.eigenspace Z (ω ^ 2))
    (hpu : pu ∈ Module.End.eigenspace Z 1) (hpv : pv ∈ Module.End.eigenspace Z 1)
    (hdual : ∀ i j, polar (quadMinus 4 F b c) (vv i) (ww j) = if i = j then 1 else 0)
    (hplane : ∀ s t : F, quadMinus 4 F b c (s • pu + t • pv) = s ^ 2 + b * s * t + c * t ^ 2) :
    ∃ M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F, IsUnit M ∧
      (∀ x, quadMinus 4 F b c (M *ᵥ x) = quadMinus 4 F b c x) ∧
      ∀ x, Z (M *ᵥ x) = M *ᵥ (Matrix.diagonal
        (Sum.elim (fun _ => ω) (Sum.elim (fun _ => ω ^ 2) fun _ => (1 : F))) *ᵥ x) := by
  classical
  let Mlin : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) →ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
    Fintype.linearCombination F (Sum.elim vv (Sum.elim ww ![pu, pv]))
  have hM : ∀ x, LinearMap.toMatrix' Mlin *ᵥ x = Mlin x := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have hiso : ∀ x, quadMinus 4 F b c (Mlin x) = quadMinus 4 F b c x := fun x =>
    k328r3c_comb_Q b c Z hQ hω1 hω2 hω4 hvv hww hpu hpv hdual hplane x
  have hinj : Function.Injective Mlin := by
    refine (injective_iff_map_eq_zero Mlin).2 fun x hx => ?_
    refine hnd.1 x fun y => ?_
    have e1 := hiso (x + y)
    have e2 := hiso x
    have e3 := hiso y
    rw [map_add, hx, zero_add] at e1
    rw [hx, QuadraticMap.map_zero] at e2
    rw [polarBilin_apply_apply, polar]
    linear_combination e3 - e1 + e2
  refine ⟨LinearMap.toMatrix' Mlin, Matrix.mulVec_injective_iff_isUnit.1 ?_, fun x => ?_,
    fun x => ?_⟩
  · have : (LinearMap.toMatrix' Mlin).mulVec = ⇑Mlin := funext hM
    rw [this]
    exact hinj
  · rw [hM, hiso]
  · rw [hM, hM]
    exact k328r3c_comb_Z Z hvv hww hpu hpv x

private theorem k328r3c_det_restrict_mul {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {U : Submodule F V} {f g h : V →ₗ[F] V} (hf : ∀ v ∈ U, f v ∈ U) (hg : ∀ v ∈ U, g v ∈ U)
    (hh : ∀ v ∈ U, h v ∈ U) (hfgh : f = g ∘ₗ h) :
    LinearMap.det (f.restrict hf) = LinearMap.det (g.restrict hg) * LinearMap.det (h.restrict hh) := by
  subst hfgh
  rw [← LinearMap.det_comp]
  rfl

private theorem k328r3c_det_restrict_one {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {U : Submodule F V} {f : V →ₗ[F] V} (hf : ∀ v ∈ U, f v ∈ U) (h : f = LinearMap.id) :
    LinearMap.det (f.restrict hf) = 1 := by
  subst h
  exact LinearMap.det_id

private theorem k328r3c_dvd {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] {ω : F}
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {z : GL ι F} {X : Subgroup (GL ι F)} (hzX : z ∈ X)
    (hXC : X ≤ Subgroup.centralizer {z}) (hperf : ⁅X, X⁆ = X) :
    3 ∣ finrank F (Module.End.eigenspace (Matrix.toLin' (z : Matrix ι ι F)) ω) := by
  set U := Module.End.eigenspace (Matrix.toLin' (z : Matrix ι ι F)) ω with hUdef
  have hU : ∀ x : X, ∀ v ∈ U, Matrix.toLin' ((x : GL ι F) : Matrix ι ι F) v ∈ U := by
    intro x v hv
    have hc := congrArg (fun g : GL ι F => (g : Matrix ι ι F))
      (Subgroup.mem_centralizer_singleton_iff.1 (hXC x.2))
    have hv' := Module.End.mem_eigenspace_iff.1 hv
    rw [Matrix.toLin'_apply] at hv'
    rw [hUdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec]
    simp only [Units.val_mul] at hc
    rw [← hc, ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_smul]
  let φ : ↥X →* F :=
    { toFun := fun x => LinearMap.det
        ((Matrix.toLin' ((x : GL ι F) : Matrix ι ι F)).restrict (hU x))
      map_one' := k328r3c_det_restrict_one _ (by simp)
      map_mul' := fun x y => k328r3c_det_restrict_mul _ _ _ (by
        rw [Subgroup.coe_mul, Units.val_mul, Matrix.toLin'_mul]) }
  have hinv : ∀ g, φ g * φ g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hker : ⁅X, X⁆ ≤ φ.ker.map X.subtype := by
    refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    refine ⟨⁅(⟨g₁, hg₁⟩ : ↥X), ⟨g₂, hg₂⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul]
    calc φ ⟨g₁, hg₁⟩ * φ ⟨g₂, hg₂⟩ * φ (⟨g₁, hg₁⟩ : ↥X)⁻¹ * φ (⟨g₂, hg₂⟩ : ↥X)⁻¹
        = (φ ⟨g₁, hg₁⟩ * φ (⟨g₁, hg₁⟩ : ↥X)⁻¹) * (φ ⟨g₂, hg₂⟩ * φ (⟨g₂, hg₂⟩ : ↥X)⁻¹) := by ring
      _ = 1 := by rw [hinv, hinv, one_mul]
  obtain ⟨k, hk, hkz⟩ := hker (hperf ▸ hzX)
  have hkz' : k = ⟨z, hzX⟩ := Subtype.ext hkz
  have hφ1 : φ ⟨z, hzX⟩ = 1 := hkz' ▸ hk
  have hφz : φ ⟨z, hzX⟩ = ω ^ finrank F U := by
    show LinearMap.det ((Matrix.toLin' (z : Matrix ι ι F)).restrict (hU ⟨z, hzX⟩)) = _
    have : (Matrix.toLin' (z : Matrix ι ι F)).restrict (hU ⟨z, hzX⟩) = ω • LinearMap.id := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      exact Module.End.mem_eigenspace_iff.1 v.2
    rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hpow : ω ^ finrank F U = 1 := hφz.symm.trans hφ1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← orderOf_eq_prime hω3 hω1]
  exact orderOf_dvd_of_pow_eq_one hpow

private theorem k328r3c_dickson {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [CharP K 2] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a : V} (ha : Q a ≠ 0) :
    g ∈ CFSG.RankThree.Classical2.orthDerived Q ∨
      g * CFSG.ClassicalGroups.Orthogonal.reflect Q a ∈ CFSG.RankThree.Classical2.orthDerived Q := by
  let _ : Invertible (Q a) := invertibleOfNonzero ha
  have hr := TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q a
  have hmul := CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hg hr
  rw [CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ a, Nat.cast_one] at hmul
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
  have hΩ := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
  by_cases hev : Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace g))
  · exact Or.inl (hΩ ⟨hg, hev⟩)
  · refine Or.inr (hΩ ⟨mul_mem hg hr, ?_⟩)
    rw [← ZMod.natCast_eq_zero_iff_even, hmul, ← Nat.cast_one, ← Nat.cast_add,
      ZMod.natCast_eq_zero_iff_even, Nat.even_add_one]
    exact hev

private theorem k328r3c_dims {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hnd : (polarBilin Q).Nondegenerate)
    (Z : V →ₗ[F] V) (hQ : ∀ v, Q (Z v) = Q v) {ω : F} (h2 : (2 : F) = 0)
    (hω : ω ^ 2 + ω + 1 = 0) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) (hω2 : ω ^ 2 ≠ ω)
    (hZ : ∀ v, Z (Z (Z v)) = v) (hdim : finrank F V = 8)
    (hdvd : 3 ∣ finrank F (Module.End.eigenspace Z ω)) (hne : ∃ v, Z v ≠ v) :
    finrank F (Module.End.eigenspace Z ω) = 3 ∧
      finrank F (Module.End.eigenspace Z (ω ^ 2)) = 3 ∧
      finrank F (Module.End.eigenspace Z 1) = 2 := by
  have hω21 : ω ^ 2 ≠ 1 := fun h => hω0 (by linear_combination hω - h - h2)
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hdecA := k328r3c_decomp Z h2 hω hZ
  have hdecB : ∀ y : V, ∃ a ∈ Module.End.eigenspace Z 1, ∃ s ∈ Module.End.eigenspace Z (ω ^ 2),
      ∃ t ∈ Module.End.eigenspace Z ω, y = a + s + t := fun y => by
    obtain ⟨a, ha, u, hu, w, hw, rfl⟩ := hdecA y
    exact ⟨a, ha, w, hw, u, hu, by abel⟩
  have hle1 : finrank F (Module.End.eigenspace Z (ω ^ 2)) ≤
      finrank F (Module.End.eigenspace Z ω) :=
    k328r3c_finrank_le Q _ _ fun w hw hperp => k328r3c_eq_zero_of_perp Q hnd Z hQ hω21
      (fun h => hω1 (by linear_combination h - ω * hω3)) hdecB hw fun t ht => hperp t ht
  have hle2 : finrank F (Module.End.eigenspace Z ω) ≤
      finrank F (Module.End.eigenspace Z (ω ^ 2)) :=
    k328r3c_finrank_le Q _ _ fun w hw hperp => k328r3c_eq_zero_of_perp Q hnd Z hQ hω1
      (by rw [← pow_two]; exact hω21) hdecA hw fun t ht => hperp t ht
  have hsum := k328r3c_finrank_sum Z h2 hω hω1 hω2 hZ
  have hpos : 0 < finrank F (Module.End.eigenspace Z ω) := by
    by_contra h0
    have hU0 : finrank F (Module.End.eigenspace Z ω) = 0 := by omega
    have hW0 : finrank F (Module.End.eigenspace Z (ω ^ 2)) = 0 := by omega
    rw [Submodule.finrank_eq_zero] at hU0 hW0
    obtain ⟨v, hv⟩ := hne
    obtain ⟨a, ha, u, hu, w, hw, rfl⟩ := hdecA v
    rw [hU0, Submodule.mem_bot] at hu
    rw [hW0, Submodule.mem_bot] at hw
    subst hu hw
    refine hv ?_
    rw [add_zero, add_zero]
    simpa using Module.End.mem_eigenspace_iff.1 ha
  omega

private theorem k328r3c_charTwo {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    CharP F 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)

private theorem k328r3c_two_eq_zero {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    (2 : F) = 0 := by
  have := k328r3c_charTwo hF
  exact_mod_cast CharP.cast_eq_zero F 2

private theorem k328r3c_omega_facts {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (ω : F) (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 ≠ ω ∧ ω ^ 3 = 1 := by
  have h2 := k328r3c_two_eq_zero (F := F) hF
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, by linear_combination (ω - 1) * hω⟩
  · rw [h] at hω
    exact one_ne_zero (by linear_combination hω)
  · rw [h] at hω
    exact one_ne_zero (by linear_combination hω - h2)
  · exact one_ne_zero (by linear_combination hω - h - ω * h2)

private theorem k328r3c_mem_orth {F : Type} [Field F] (b c : F)
    {g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F} (hg : g ∈ StatedOmega (StatedQuadMinus 4 F b c)) :
    toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F g ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 F b c) := by
  rw [statedOmega_eq_comap (coe_quadMinus 4 F b c), Subgroup.mem_comap] at hg
  refine (Subgroup.commutator_le.2 fun x hx y hy => ?_) hg
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

private theorem k328r3c_Z_facts {F : Type} [Field F] {z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz3 : orderOf z = 3)
    {Z : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) →ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)}
    (hZ : ∀ v, Z v = (z : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ v) :
    (∀ v, Z (Z (Z v)) = v) ∧ ∃ v, Z v ≠ v := by
  refine ⟨fun v => ?_, ?_⟩
  · have h := congrArg (fun g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F =>
      (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) (pow_orderOf_eq_one z)
    rw [hz3] at h
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h
    have h3 : (z : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *
        ((z : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *
          (z : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)) = 1 := by
      rw [← h]; noncomm_ring
    simp only [hZ, Matrix.mulVec_mulVec, h3, Matrix.one_mulVec]
  · by_contra h
    have hid : ∀ v, Z v = v := fun v => by_contra fun hv => h ⟨v, hv⟩
    have h1 : (z : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) = 1 :=
      Matrix.ext_of_mulVec_single fun i => by
        rw [Matrix.one_mulVec, ← hZ]
        exact hid _
    have hz1 : z = 1 := Units.ext h1
    rw [hz1, orderOf_one] at hz3
    omega

private theorem k328r3c_conj {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) {z : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hzO : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 F b c)) (hz3 : orderOf z = 3)
    {X : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)} (hzX : z ∈ X)
    (hXC : X ≤ Subgroup.centralizer {z}) (hperf : ⁅X, X⁆ = X) :
    ∃ M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F, IsUnit M ∧
      (∀ x, quadMinus 4 F b c (M *ᵥ x) = quadMinus 4 F b c x) ∧
      (z : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) * M = M *
        Matrix.diagonal
          (Sum.elim (fun _ => ω) (Sum.elim (fun _ => ω ^ 2) fun _ => (1 : F))) := by
  have h2 := k328r3c_two_eq_zero hF
  obtain ⟨hω0, hω1, hω2, hω3⟩ := k328r3c_omega_facts hF ω hω
  have hω21 : ω ^ 2 ≠ 1 := fun h => hω0 (by linear_combination hω - h - h2)
  have hω44 : (ω ^ 2) ^ 2 ≠ 1 := fun h => hω1 (by linear_combination h - ω * hω3)
  obtain ⟨hnd, -⟩ := regular_quadMinus (n := 4) (by norm_num) hbc
  set Z : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) →ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
    Matrix.toLin' (z : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) with hZdef
  have hQ : ∀ v, quadMinus 4 F b c (Z v) = quadMinus 4 F b c v := fun v => by
    simpa [Z, toLinEquiv_apply, Matrix.toLin'_apply] using
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hzO v
  obtain ⟨hZ3, hne⟩ := k328r3c_Z_facts hz3 (Z := Z) fun v => by
    simp [Z, Matrix.toLin'_apply]
  have hdim : finrank F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨hU, hW, hP⟩ := k328r3c_dims _ hnd Z hQ h2 hω hω0 hω1 hω2 hZ3 hdim
    (k328r3c_dvd hω1 hω3 hzX hXC hperf) hne
  have hdecA := k328r3c_decomp Z h2 hω hZ3
  have hnp : ¬ IsPlusType (quadMinus 4 F b c) :=
    not_isPlusType_quadMinus (n := 4) (by norm_num) hbc
  obtain ⟨pu, hpu, pv, hpv, hplane⟩ := k328r3c_plane _ (Module.End.eigenspace Z 1)
    (k328r3c_nondeg_fixed _ hnd Z hQ hω1 hω21 hdecA) hP
    (fun x hx hx0 hQx => k328r3c_aniso_fixed _ Z hQ hω1 hω21 hdim hU hnp hx hx0 hQx) hbc
  have hdecB : ∀ y : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F, ∃ a ∈ Module.End.eigenspace Z 1,
      ∃ s ∈ Module.End.eigenspace Z (ω ^ 2), ∃ t ∈ Module.End.eigenspace Z ω,
        y = a + s + t := fun y => by
    obtain ⟨a, ha, u, hu, w, hw, rfl⟩ := hdecA y
    exact ⟨a, ha, w, hw, u, hu, by abel⟩
  obtain ⟨vv, ww, hvv, hww, hdual⟩ := k328r3c_dual _ _ _ hU hW fun w hw hperp =>
    k328r3c_eq_zero_of_perp _ hnd Z hQ hω21 (fun h => hω1 (by linear_combination h - ω * hω3))
      hdecB hw fun t ht => hperp t ht
  obtain ⟨M, hM, hMQ, hMZ⟩ := k328r3c_frame b c hnd Z hQ hω1 hω21 hω44 vv ww pu pv hvv hww hpu hpv
    hdual hplane
  refine ⟨M, hM, hMQ, Matrix.toLin'.injective (LinearMap.ext fun x => ?_)⟩
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  exact hMZ x

private theorem k328r3c_comm_reflect {F : Type} [Field F] (b c : F) {ω : F}
    {z₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz₀ : (z₀ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) =
      Matrix.diagonal (Sum.elim (fun _ => ω) (Sum.elim (fun _ => ω ^ 2) fun _ => (1 : F))))
    (hz₀O : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z₀ ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 F b c))
    {u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F} (hu : u = Pi.single (Sum.inr (Sum.inr 0)) 1) :
    toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z₀ * reflect (quadMinus 4 F b c) u =
      reflect (quadMinus 4 F b c) u * toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z₀ := by
  have hz₀u : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z₀ u = u := by
    rw [toLinEquiv_apply, hz₀]
    funext i
    rw [Matrix.mulVec_diagonal]
    by_cases hi : i = Sum.inr (Sum.inr 0)
    · subst hi
      simp [hu]
    · simp [hu, hi]
  have h := reflect_conj hz₀O u
  rw [hz₀u, mul_inv_eq_iff_eq_mul] at h
  exact h

private theorem k328r3c_conclude {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {ω : F}
    {z z₀ g₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hz₀ : (z₀ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) =
      Matrix.diagonal (Sum.elim (fun _ => ω) (Sum.elim (fun _ => ω ^ 2) fun _ => (1 : F))))
    (hzO : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 F b c))
    (hg₀ : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F g₀ ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 F b c)) (hzg : z * g₀ = g₀ * z₀) :
    ∃ g ∈ StatedOmega (StatedQuadMinus 4 F b c), g * z * g⁻¹ = z₀ := by
  have := k328r3c_charTwo hF
  obtain ⟨hnd, hT⟩ := regular_quadMinus (n := 4) (by norm_num) hbc
  set u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := Pi.single (Sum.inr (Sum.inr 0)) 1 with hu
  have hQu : quadMinus 4 F b c u ≠ 0 := by
    rw [k328r3c_quadMinus_apply]
    simp [hu]
  have hconj : g₀⁻¹ * z * g₀ = z₀ := by
    rw [mul_assoc, hzg, inv_mul_cancel_left]
  have hz₀O : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F z₀ ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 F b c) := by
    rw [← hconj, map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (inv_mem hg₀) hzO) hg₀
  have hcomm := k328r3c_comm_reflect b c hz₀ hz₀O hu
  have hH : ∀ g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
      toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F g ∈
        CFSG.RankThree.Classical2.orthDerived (quadMinus 4 F b c) →
          g ∈ StatedOmega (StatedQuadMinus 4 F b c) := fun g hg => by
    rw [statedOmega_eq_comap (coe_quadMinus 4 F b c), Subgroup.mem_comap]
    exact hg
  rcases k328r3c_dickson hnd hT hg₀ hQu with h | h
  · refine ⟨g₀⁻¹, inv_mem (hH g₀ h), ?_⟩
    rw [inv_inv, hconj]
  · set r : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
      (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).symm (reflect (quadMinus 4 F b c) u) with hr
    have hrR : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F r = reflect (quadMinus 4 F b c) u :=
      (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).apply_symm_apply _
    have hgr : g₀ * r ∈ StatedOmega (StatedQuadMinus 4 F b c) :=
      hH _ (by rw [map_mul, hrR]; exact h)
    have hcomm' : z₀ * r = r * z₀ :=
      (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).injective (by
        rw [map_mul, map_mul, hrR]
        exact hcomm)
    refine ⟨(g₀ * r)⁻¹, inv_mem hgr, ?_⟩
    calc (g₀ * r)⁻¹ * z * (g₀ * r)⁻¹⁻¹ = r⁻¹ * (g₀⁻¹ * z * g₀) * r := by group
      _ = z₀ := by rw [hconj, mul_assoc, hcomm', ← mul_assoc, inv_mul_cancel, one_mul]

theorem row3_class (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])))
    (ht : (t₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] (Sum.elim ![ω ^ 2, ω, 1] ![1, 1]))) :
    ClassLeaf (StatedOmega (StatedQuadMinus 4 F b c)) z₀ := by
  have _ := ht
  have hd : (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1]) :
      Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) =
      Sum.elim (fun _ => ω) (Sum.elim (fun _ => ω ^ 2) fun _ => 1) := by
    funext i
    rcases i with i | i | i <;> fin_cases i <;> rfl
  rw [hd] at hz
  intro z hzH hz3 X _ hzX hXC hperf
  have hzO := k328r3c_mem_orth b c hzH
  obtain ⟨M, hM, hMQ, hMZ⟩ := k328r3c_conj hF b c hbc hω hzO hz3 hzX hXC hperf
  have hzg : z * hM.unit = hM.unit * z₀ := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hM.unit_spec, hz]
    exact hMZ
  have hg₀ : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F hM.unit ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 F b c) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => by
      simpa [toLinEquiv_apply, hM.unit_spec] using hMQ v
  obtain ⟨g, hg, hgz⟩ := k328r3c_conclude hF b c hbc hz hzO hg₀ hzg
  exact ⟨g, hg, Or.inl hgz⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
