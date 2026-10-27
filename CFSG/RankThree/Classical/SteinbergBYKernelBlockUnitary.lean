module

public import CFSG.LinearAlgebra.SteinbergBQKernelBlocks
public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField

public section

namespace CFSG.RankThree.Classical.SteinbergBY

open Module QuadraticMap CFSG.LinearAlgebra CFSG.LinearAlgebra.SteinbergBQ
open TauCeti.QuadraticMap (orthogonalGroup)

theorem omega_ne_zero : omega ≠ 0 := by
  intro h0
  have := omega_sq
  rw [h0] at this
  simp at this

theorem omega_ne_one : omega ≠ 1 := by
  intro h0
  have := omega_sq
  rw [h0, one_pow, one_add_one_eq_two, omegaField_two_eq_zero] at this
  exact one_ne_zero this

theorem algebraMap_add_omega_mul_eq_zero {a b : ZMod 2}
    (h : algebraMap (ZMod 2) OmegaField a + omega * algebraMap (ZMod 2) OmegaField b = 0) :
    a = 0 ∧ b = 0 := by
  have h3 : (1 : OmegaField) + omega ≠ 0 := by
    intro h0
    apply omega_ne_one
    have h2 : (2 : OmegaField) = 0 := omegaField_two_eq_zero
    linear_combination h0 - h2
  have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  revert h
  rcases key a with rfl | rfl <;> rcases key b with rfl | rfl <;> simp [omega_ne_zero, h3]

theorem omega_mul_omega : omega * omega = omega + 1 := by
  rw [← pow_two, omega_sq]

section CharTwo

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem zmod2_vec_eq_of_add_eq_zero {x y : W} (h : x + y = 0) : x = y := by
  rw [eq_neg_of_add_eq_zero_left h, neg_eq_of_add_eq_zero_right (zmod2_vec_add_self y)]

theorem sq_apply_of_add_add {z : W →ₗ[ZMod 2] W} (hz2 : ∀ v, v + z v + z (z v) = 0) (v : W) :
    z (z v) = v + z v :=
  (zmod2_vec_eq_of_add_eq_zero (hz2 v)).symm

theorem cube_apply_of_add_add {z : W →ₗ[ZMod 2] W} (hz2 : ∀ v, v + z v + z (z v) = 0) (v : W) :
    z (z (z v)) = v := by
  rw [sq_apply_of_add_add hz2 (z v), sq_apply_of_add_add hz2 v]
  calc z v + (v + z v) = v + (z v + z v) := by abel
    _ = v := by rw [zmod2_vec_add_self, add_zero]

end CharTwo

section Herm

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def omegaHerm (Q : QuadraticForm (ZMod 2) W) (z : W →ₗ[ZMod 2] W)
    (v w : W) : OmegaField :=
  algebraMap (ZMod 2) OmegaField (polar Q v (z w)) +
    omega * algebraMap (ZMod 2) OmegaField (polar Q v w)

variable {Q : QuadraticForm (ZMod 2) W} {z : W →ₗ[ZMod 2] W}

theorem polar_apply_apply (hzQ : ∀ v, Q (z v) = Q v) (v w : W) :
    polar Q (z v) (z w) = polar Q v w := by
  simp only [polar, ← map_add, hzQ]

theorem polar_apply_left (hzQ : ∀ v, Q (z v) = Q v) (hz2 : ∀ v, v + z v + z (z v) = 0)
    (v w : W) : polar Q (z v) w = polar Q v (z w) + polar Q v w := by
  conv_lhs => rw [← cube_apply_of_add_add hz2 w]
  rw [polar_apply_apply hzQ, sq_apply_of_add_add hz2, polar_add_right, add_comm]

theorem eq_polar_apply (hzQ : ∀ v, Q (z v) = Q v) (hz2 : ∀ v, v + z v + z (z v) = 0) (v : W) :
    Q v = polar Q v (z v) := by
  have h1 : Q (v + z v) = Q v := by rw [← sq_apply_of_add_add hz2, hzQ, hzQ]
  have h2 : Q (v + z v) = Q v + Q (z v) + polar Q v (z v) := by
    rw [polar]
    ring
  rw [hzQ] at h2
  calc Q v = Q (v + z v) := h1.symm
    _ = Q v + Q v + polar Q v (z v) := h2
    _ = polar Q v (z v) := by rw [zmod2_add_self, zero_add]

theorem omegaHerm_apply_left (hzQ : ∀ v, Q (z v) = Q v) (hz2 : ∀ v, v + z v + z (z v) = 0)
    (v w : W) : omegaHerm Q z (z v) w = omega * omegaHerm Q z v w := by
  unfold omegaHerm
  rw [polar_apply_apply hzQ, polar_apply_left hzQ hz2, map_add]
  linear_combination (-(algebraMap (ZMod 2) OmegaField) (polar Q v w)) * omega_mul_omega

theorem omegaHerm_apply_right (hz2 : ∀ v, v + z v + z (z v) = 0) (v w : W) :
    omegaHerm Q z v (z w) = omega ^ 2 * omegaHerm Q z v w := by
  unfold omegaHerm
  have h2 : (2 : OmegaField) = 0 := omegaField_two_eq_zero
  rw [sq_apply_of_add_add hz2, polar_add_right, map_add]
  linear_combination (-(algebraMap (ZMod 2) OmegaField) (polar Q v (z w)) -
    (omega + 1) * (algebraMap (ZMod 2) OmegaField) (polar Q v w)) * omega_mul_omega +
    (-(omega * (algebraMap (ZMod 2) OmegaField) (polar Q v w))) * h2

theorem omegaHerm_add_left (v v' w : W) :
    omegaHerm Q z (v + v') w = omegaHerm Q z v w + omegaHerm Q z v' w := by
  unfold omegaHerm
  rw [polar_add_left, polar_add_left, map_add, map_add]
  ring

theorem omegaHerm_smul_left (a : ZMod 2) (v w : W) :
    omegaHerm Q z (a • v) w = algebraMap (ZMod 2) OmegaField a * omegaHerm Q z v w := by
  unfold omegaHerm
  rw [polar_smul_left, polar_smul_left, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
  ring

theorem omegaHerm_add_right (v w w' : W) :
    omegaHerm Q z v (w + w') = omegaHerm Q z v w + omegaHerm Q z v w' := by
  unfold omegaHerm
  rw [map_add, polar_add_right, polar_add_right, map_add, map_add]
  ring

theorem omegaHerm_smul_right (a : ZMod 2) (v w : W) :
    omegaHerm Q z v (a • w) = algebraMap (ZMod 2) OmegaField a * omegaHerm Q z v w := by
  unfold omegaHerm
  rw [map_smul, polar_smul_right, polar_smul_right, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
  ring

theorem omegaHerm_swap (hzQ : ∀ v, Q (z v) = Q v) (hz2 : ∀ v, v + z v + z (z v) = 0)
    (v w : W) : omegaHerm Q z w v = omegaHerm Q z v w ^ 2 := by
  have e : omegaHerm Q z v w = algebraMap (ZMod 2) OmegaField (polar Q v (z w)) +
      algebraMap (ZMod 2) OmegaField (polar Q v w) * omega := by
    unfold omegaHerm
    ring
  rw [e, omegaField_sq]
  unfold omegaHerm
  rw [polar_comm Q w (z v), polar_apply_left hzQ hz2, polar_comm Q w v, map_add, omega_sq]
  ring

theorem omegaHerm_self (hzQ : ∀ v, Q (z v) = Q v) (hz2 : ∀ v, v + z v + z (z v) = 0) (v : W) :
    omegaHerm Q z v v = algebraMap (ZMod 2) OmegaField (Q v) := by
  unfold omegaHerm
  rw [← eq_polar_apply hzQ hz2, zmod2_polar_self, map_zero, mul_zero, add_zero]

theorem polar_eq_zero_of_omegaHerm_eq_zero {v w : W} (h : omegaHerm Q z v w = 0) :
    polar Q v w = 0 :=
  (algebraMap_add_omega_mul_eq_zero h).2

end Herm

section Unitary

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (Q : QuadraticForm (ZMod 2) W)
  (z : LinearMap.GeneralLinearGroup (ZMod 2) W) (hz : orderOf z = 3)
  (hfix : ∀ v, (z : W →ₗ[ZMod 2] W) v = v → v = 0)

@[expose] noncomputable def omegaUnitaryGroup : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {g | (∀ (x : OmegaField) (v : W),
      (letI := omegaModule z hz hfix; g (x • v)) = (letI := omegaModule z hz hfix; x • g v)) ∧
    ∀ v w, omegaHerm Q z (g v) (g w) = omegaHerm Q z v w}
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := fun {g g'} hg hg' => ⟨fun x v => by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg'.1, hg.1],
    fun v w => by rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg.2, hg'.2]⟩
  inv_mem' := fun {g} hg => ⟨fun x v => by
      let _ := omegaModule z hz hfix
      apply g.injective
      have h1 : ∀ u, g (g⁻¹ u) = u := fun u => by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]
        rfl
      rw [h1, hg.1, h1],
    fun v w => by
      have h1 : ∀ u, g (g⁻¹ u) = u := fun u => by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]
        rfl
      rw [← hg.2, h1, h1]⟩

variable {Q z hz hfix}

theorem mem_omegaUnitaryGroup_iff (hzQ : ∀ v, Q ((z : W →ₗ[ZMod 2] W) v) = Q v)
    {g : W ≃ₗ[ZMod 2] W} :
    g ∈ omegaUnitaryGroup Q z hz hfix ↔
      (∀ v, g ((z : W →ₗ[ZMod 2] W) v) = (z : W →ₗ[ZMod 2] W) (g v)) ∧
        ∀ v, Q (g v) = Q v := by
  have hz2 : ∀ v, v + (z : W →ₗ[ZMod 2] W) v +
      (z : W →ₗ[ZMod 2] W) ((z : W →ₗ[ZMod 2] W) v) = 0 := fun v => by
    have h := fpf_relation hz hfix
    have := LinearMap.congr_fun h v
    simp only [LinearMap.add_apply, pow_two, Module.End.mul_apply, Module.End.one_apply,
      LinearMap.zero_apply] at this
    rw [← this]
    abel
  constructor
  · rintro ⟨hlin, hherm⟩
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have h := hlin omega v
      rwa [omegaModule_omega_smul z hz hfix, omegaModule_omega_smul z hz hfix] at h
    · apply (algebraMap (ZMod 2) OmegaField).injective
      rw [← omegaHerm_self hzQ hz2, ← omegaHerm_self hzQ hz2, hherm]
  · rintro ⟨hcomm, hiso⟩
    have hpolar : ∀ x y, polar Q (g x) (g y) = polar Q x y := fun x y => by
      simp only [polar, ← map_add, hiso]
    refine ⟨fun x v => ?_, fun v w => ?_⟩
    · obtain ⟨a, b, rfl⟩ := omegaField_eq x
      rw [omegaModule_smul_eq z hz hfix, omegaModule_smul_eq z hz hfix, map_add, map_smul,
        map_smul, hcomm]
    · unfold omegaHerm
      rw [← hcomm, hpolar, hpolar]

theorem omegaHerm_semilinear (hzQ : ∀ v, Q ((z : W →ₗ[ZMod 2] W) v) = Q v)
    (hz2 : ∀ v, v + (z : W →ₗ[ZMod 2] W) v +
      (z : W →ₗ[ZMod 2] W) ((z : W →ₗ[ZMod 2] W) v) = 0) :
    letI := omegaModule z hz hfix
    (∀ (x : OmegaField) (v v' w : W), omegaHerm Q z (x • v + v') w =
      x * omegaHerm Q z v w + omegaHerm Q z v' w) ∧
    ∀ (x : OmegaField) (v w w' : W), omegaHerm Q z v (x • w + w') =
      x ^ 2 * omegaHerm Q z v w + omegaHerm Q z v w' := by
  let _ := omegaModule z hz hfix
  refine ⟨fun x v v' w => ?_, fun x v w w' => ?_⟩
  · obtain ⟨a, b, rfl⟩ := omegaField_eq x
    rw [omegaModule_smul_eq z hz hfix, omegaHerm_add_left, omegaHerm_add_left,
      omegaHerm_smul_left, omegaHerm_smul_left, omegaHerm_apply_left hzQ hz2]
    ring
  · obtain ⟨a, b, rfl⟩ := omegaField_eq x
    rw [omegaModule_smul_eq z hz hfix, omegaHerm_add_right, omegaHerm_add_right,
      omegaHerm_smul_right, omegaHerm_smul_right, omegaHerm_apply_right hz2, omegaField_sq]
    ring

end Unitary

section Global

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def polarIsometryGroup (q : QuadraticForm (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∀ x y, polar q (g x) (g y) = polar q x y}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh x y := (hg _ _).trans (hh x y)
  inv_mem' {g} hg x y := by
    have h1 : ∀ u, g (g⁻¹ u) = u := fun u => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    have h := hg (g⁻¹ x) (g⁻¹ y)
    rw [h1, h1] at h
    exact h.symm

theorem mem_polarIsometryGroup {q : QuadraticForm (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ polarIsometryGroup q ↔ ∀ x y, polar q (g x) (g y) = polar q x y :=
  Iff.rfl

theorem apply_inv_apply (g : V ≃ₗ[ZMod 2] V) (u : V) : g (g⁻¹ u) = u := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl

theorem inv_apply_apply (g : V ≃ₗ[ZMod 2] V) (u : V) : g⁻¹ (g u) = u := by
  rw [← LinearEquiv.mul_apply, inv_mul_cancel]
  rfl

open _root_.Classical in
@[expose] noncomputable def restrictEquiv (g : V ≃ₗ[ZMod 2] V) (P : Submodule (ZMod 2) V) :
    P ≃ₗ[ZMod 2] P :=
  if h : P.map (g : V →ₗ[ZMod 2] V) = P then g.ofSubmodules P P h else LinearEquiv.refl _ _

theorem restrictEquiv_apply {g : V ≃ₗ[ZMod 2] V} {P : Submodule (ZMod 2) V}
    (h : P.map (g : V →ₗ[ZMod 2] V) = P) (v : P) : (restrictEquiv g P v : V) = g v := by
  simp only [restrictEquiv, h, ↓reduceDIte, LinearEquiv.ofSubmodules_apply]

@[expose] noncomputable def blockGen (c : V ≃ₗ[ZMod 2] V) (N : Subgroup (V ≃ₗ[ZMod 2] V)) :
    LinearMap.GeneralLinearGroup (ZMod 2) (fixedSub N) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (restrictEquiv c (fixedSub N))

theorem blockGen_apply {c : V ≃ₗ[ZMod 2] V} {N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (h : (fixedSub N).map (c : V →ₗ[ZMod 2] V) = fixedSub N) (v : fixedSub N) :
    ((blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N) v : V) = c v :=
  restrictEquiv_apply h v

theorem map_fixedSub_eq {g : V ≃ₗ[ZMod 2] V} {N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hg : ∀ n ∈ N, n * g = g * n) : (fixedSub N).map (g : V →ₗ[ZMod 2] V) = fixedSub N := by
  have hmem : ∀ {h : V ≃ₗ[ZMod 2] V}, (∀ n ∈ N, n * h = h * n) → ∀ v ∈ fixedSub N,
      h v ∈ fixedSub N := by
    intro h hh v hv n hn
    rw [← LinearEquiv.mul_apply, hh n hn, LinearEquiv.mul_apply, hv n hn]
  have hg' : ∀ n ∈ N, n * g⁻¹ = g⁻¹ * n := fun n hn => by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hg n hn, inv_mul_cancel_left]
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hmem hg v hv
  · intro v hv
    exact ⟨g⁻¹ v, hmem hg' v hv, apply_inv_apply g v⟩

end Global

section Blocks

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
  {B : Subgroup (V ≃ₗ[ZMod 2] V)} {N : Subgroup (V ≃ₗ[ZMod 2] V)} {c : V ≃ₗ[ZMod 2] V}

theorem polar_comp_subtype (P : Submodule (ZMod 2) V) (x y : P) :
    polar (q.comp P.subtype) x y = polar q x y := by
  simp only [polar, QuadraticMap.comp_apply, Submodule.subtype_apply, Submodule.coe_add]

theorem map_fixedSub_of_mem (hB : KernelBlockHyp q B) (hNB : N ≤ B) (hcB : c ∈ B) :
    (fixedSub N).map (c : V →ₗ[ZMod 2] V) = fixedSub N :=
  map_fixedSub_eq fun n hn => hB.comm n (hNB hn) c hcB

theorem blockGen_apply_of_mem (hB : KernelBlockHyp q B) (hNB : N ≤ B) (hcB : c ∈ B)
    (v : fixedSub N) : ((blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N) v : V) = c v :=
  blockGen_apply (map_fixedSub_of_mem hB hNB hcB) v

theorem blockGen_fix (hB : KernelBlockHyp q B) (hNB : N ≤ B) (hidx : N.relIndex B = 3)
    (hcB : c ∈ B) (hcN : c ∉ N) (v : fixedSub N)
    (hv : (blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N) v = v) : v = 0 := by
  have h := congrArg Subtype.val hv
  rw [blockGen_apply_of_mem hB hNB hcB] at h
  exact Subtype.ext (hB.eq_zero_of_fixed hidx hcB hcN v.2 h)

theorem blockGen_add_add (hB : KernelBlockHyp q B) (hNB : N ≤ B) (hidx : N.relIndex B = 3)
    (hcB : c ∈ B) (hcN : c ∉ N) (v : fixedSub N) :
    v + (blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N) v +
      (blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N)
        ((blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N) v) = 0 := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_add, blockGen_apply_of_mem hB hNB hcB,
    blockGen_apply_of_mem hB hNB hcB, blockGen_apply_of_mem hB hNB hcB]
  exact hB.add_add_eq_zero hNB hidx hcB hcN v.2

theorem blockGen_isometry (hB : KernelBlockHyp q B) (hNB : N ≤ B) (hcB : c ∈ B)
    (v : fixedSub N) :
    q.comp (fixedSub N).subtype ((blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N) v) =
      q.comp (fixedSub N).subtype v := by
  rw [QuadraticMap.comp_apply, QuadraticMap.comp_apply, Submodule.subtype_apply,
    Submodule.subtype_apply, blockGen_apply_of_mem hB hNB hcB]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (hB.orth hcB) v

theorem orderOf_blockGen (hB : KernelBlockHyp q B) (hNB : N ≤ B) (hidx : N.relIndex B = 3)
    (hN0 : fixedSub N ≠ ⊥) (hcB : c ∈ B) (hcN : c ∉ N) : orderOf (blockGen c N) = 3 := by
  have hc3 : c ^ 3 = 1 := hB.cube c hcB
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have h3 : ∀ u : fixedSub N, ((blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N) u : V) =
        c u := blockGen_apply_of_mem hB hNB hcB
    change (((blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N) *
      (blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N) *
        (blockGen c N : fixedSub N →ₗ[ZMod 2] fixedSub N) *
          1) v : V) = v
    rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply,
      h3, h3, h3, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_three', hc3]
    rfl
  · intro h1
    apply hN0
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have := blockGen_fix hB hNB hidx hcB hcN ⟨v, hv⟩ (by rw [h1]; rfl)
    exact congrArg Subtype.val this

end Blocks

section OrthSum

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem map_add_eq (x y : V) : q (x + y) = q x + q y + polar q x y := by
  rw [polar]
  ring

theorem polar_sum_right {ι : Type*} (s : Finset ι) (x : V) (f : ι → V) :
    polar q x (∑ i ∈ s, f i) = ∑ i ∈ s, polar q x (f i) := by
  simp only [← polarBilin_apply_apply, map_sum]

theorem map_sum_of_polar_eq_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → V)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → polar q (f i) (f j) = 0) :
    q (∑ i ∈ s, f i) = ∑ i ∈ s, q (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add_eq, polar_sum_right,
      Finset.sum_eq_zero fun i hi => h a (Finset.mem_insert_self a s) i
        (Finset.mem_insert_of_mem hi) (fun hai => ha (hai ▸ hi)),
      ih fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij,
      add_zero]

end OrthSum

section Centralizer

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
  {B N : Subgroup (V ≃ₗ[ZMod 2] V)}

@[expose] noncomputable def centralizerRestrict (q : QuadraticForm (ZMod 2) V)
    (B N : Subgroup (V ≃ₗ[ZMod 2] V)) (hNB : N ≤ B) :
    ↥(Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q) →*
      (fixedSub N ≃ₗ[ZMod 2] fixedSub N) where
  toFun g := restrictEquiv g (fixedSub N)
  map_one' := LinearEquiv.ext fun v => Subtype.ext (by
    rw [restrictEquiv_apply (map_fixedSub_eq fun n _ => by simp)]
    rfl)
  map_mul' g g' := LinearEquiv.ext fun v => Subtype.ext (by
    have hmap : ∀ h : ↥(Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q),
        (fixedSub N).map ((h : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = fixedSub N := fun h =>
      map_fixedSub_eq fun n hn => Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp h.2).1 n (hNB hn)
    rw [LinearEquiv.mul_apply, restrictEquiv_apply (hmap (g * g')), restrictEquiv_apply (hmap g),
      restrictEquiv_apply (hmap g')]
    rfl)

theorem centralizerRestrict_apply (hNB : N ≤ B)
    (g : ↥(Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q))
    (v : fixedSub N) :
    ((centralizerRestrict q B N hNB g v : fixedSub N) : V) = (g : V ≃ₗ[ZMod 2] V) v :=
  restrictEquiv_apply (map_fixedSub_eq fun n hn => Subgroup.mem_centralizer_iff.mp
    (Subgroup.mem_inf.mp g.2).1 n (hNB hn)) v

end Centralizer

section Iso

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {B : Subgroup (V ≃ₗ[ZMod 2] V)}

attribute [local instance] KernelBlockHyp.finite_subgroup

omit [FiniteDimensional (ZMod 2) V] in
theorem block_action_cases (hB : KernelBlockHyp q B) {N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hidx : N.relIndex B = 3) {c : V ≃ₗ[ZMod 2] V} (hcB : c ∈ B) (hcN : c ∉ N)
    {b : V ≃ₗ[ZMod 2] V} (hb : b ∈ B) :
    (∀ x ∈ fixedSub N, b x = x) ∨ (∀ x ∈ fixedSub N, b x = c x) ∨
      (∀ x ∈ fixedSub N, b x = c (c x)) := by
  rcases mem_or_of_relIndex_eq_three hidx hcB hcN (hB.cube c hcB) hb with h | h | h
  · exact Or.inl fun x hx => hx b h
  · refine Or.inr (Or.inl fun x hx => ?_)
    have e : b = c * (c⁻¹ * b) := by group
    rw [e, LinearEquiv.mul_apply, hx _ h]
  · refine Or.inr (Or.inr fun x hx => ?_)
    have e : b = c ^ 2 * ((c ^ 2)⁻¹ * b) := by group
    rw [e, LinearEquiv.mul_apply, hx _ h, pow_two, LinearEquiv.mul_apply]

variable (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
  (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥)
  (c : I → V ≃ₗ[ZMod 2] V) (hc : ∀ N, c N ∈ B ∧ c N ∉ (N : Subgroup (V ≃ₗ[ZMod 2] V)))
  (h3 : ∀ N : I, orderOf (blockGen (c N) N) = 3)
  (hfp : ∀ (N : I) (v : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
    (blockGen (c N) N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2] _) v = v → v = 0)

omit [FiniteDimensional (ZMod 2) V] in
include hB hI hc in
theorem centralizerRestrict_mem (N : I)
    (g : ↥(Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q)) :
    centralizerRestrict q B N ((hI N).1 N.2).1 g ∈
      omegaUnitaryGroup (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
        (blockGen (c N) N) (h3 N) (hfp N) := by
  have hNB := ((hI N).1 N.2).1
  rw [mem_omegaUnitaryGroup_iff (blockGen_isometry hB hNB (hc N).1)]
  refine ⟨fun v => Subtype.ext ?_, fun v => ?_⟩
  · rw [centralizerRestrict_apply, blockGen_apply_of_mem hB hNB (hc N).1,
      blockGen_apply_of_mem hB hNB (hc N).1, centralizerRestrict_apply]
    have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp g.2).1 (c N) (hc N).1
    exact (LinearEquiv.congr_fun h v).symm
  · rw [QuadraticMap.comp_apply, QuadraticMap.comp_apply, Submodule.subtype_apply,
      Submodule.subtype_apply, centralizerRestrict_apply]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (Subgroup.mem_inf.mp g.2).2 v

@[expose] noncomputable def centralizerToPi :
    ↥(Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q) →*
      ((N : I) → omegaUnitaryGroup (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
        (blockGen (c N) N) (h3 N) (hfp N)) :=
  MonoidHom.pi fun N => (centralizerRestrict q B N ((hI N).1 N.2).1).codRestrict _
    (centralizerRestrict_mem hB hI c hc h3 hfp N)

omit [FiniteDimensional (ZMod 2) V] in
include hB in
theorem centralizerToPi_apply (N : I)
    (g : ↥(Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q))
    (v : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) :
    (((centralizerToPi hB hI c hc h3 hfp g N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≃ₗ[ZMod 2]
      fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) v : fixedSub _) : V) = (g : V ≃ₗ[ZMod 2] V) v :=
  centralizerRestrict_apply _ g v


include hB hI in
theorem eq_sum_avgMap_coe (v : V) :
    v = ∑ N : I, avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v := by
  rw [Finset.sum_coe_sort I fun N => avgMap N v]
  exact hB.eq_sum_avgMap_of_mem_iff hI v

open scoped _root_.Classical in
include hB hI in
theorem avgMap_block (N N' : I) {v : V} (hv : v ∈ fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V))) :
    avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v = if N = N' then v else 0 := by
  split_ifs with h
  · subst h
    exact hB.avgMap_eq_self ((hI N).1 N.2).1 hv
  · exact hB.avgMap_eq_zero ((hI N).1 N.2).1 ((hI N).1 N.2).2.1 ((hI N').1 N'.2).1
      ((hI N').1 N'.2).2.1 (fun h' => h (Subtype.ext h').symm) hv

include hB in
theorem centralizerToPi_injective : Function.Injective (centralizerToPi hB hI c hc h3 hfp) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [eq_sum_avgMap_coe hB hI v, map_sum]
  refine Finset.sum_congr rfl fun N _ => ?_
  have h1 : ((centralizerToPi hB hI c hc h3 hfp g N :
      omegaUnitaryGroup (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
        (blockGen (c N) N) (h3 N) (hfp N)) : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≃ₗ[ZMod 2]
          fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = 1 := by
    rw [hg]
    rfl
  have h2 := congrArg Subtype.val
    (LinearEquiv.congr_fun h1 ⟨avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v, avgMap_mem_fixedSub v⟩)
  rw [centralizerToPi_apply] at h2
  exact h2


@[expose] noncomputable def blockExtend (N : Subgroup (V ≃ₗ[ZMod 2] V))
    (e : fixedSub N →ₗ[ZMod 2] fixedSub N) : V →ₗ[ZMod 2] V :=
  (fixedSub N).subtype ∘ₗ e ∘ₗ (avgMap N).codRestrict (fixedSub N) fun v => avgMap_mem_fixedSub v

theorem blockExtend_apply (N : Subgroup (V ≃ₗ[ZMod 2] V))
    (e : fixedSub N →ₗ[ZMod 2] fixedSub N) (v : V) :
    blockExtend N e v = (e ⟨avgMap N v, avgMap_mem_fixedSub v⟩ : V) :=
  rfl

include hB hI in
theorem sum_blockExtend_apply (e : (N : I) → fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2]
      fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) (N : I)
    (x : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) :
    (∑ N' : I, blockExtend (N' : Subgroup (V ≃ₗ[ZMod 2] V)) (e N')) x = (e N x : V) := by
  classical
  rw [LinearMap.sum_apply, Finset.sum_eq_single N]
  · rw [blockExtend_apply]
    congr 2
    exact Subtype.ext (by
      change avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) (x : V) = x
      simp [avgMap_block hB hI N N x.2])
  · intro N' _ hne
    rw [blockExtend_apply]
    have h0 : (⟨avgMap (N' : Subgroup (V ≃ₗ[ZMod 2] V)) x, avgMap_mem_fixedSub (x : V)⟩ :
        fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V))) = 0 :=
      Subtype.ext (by
        change avgMap (N' : Subgroup (V ≃ₗ[ZMod 2] V)) (x : V) = 0
        simp [avgMap_block hB hI N' N x.2, hne])
    rw [h0, map_zero]
    rfl
  · intro h
    exact absurd (Finset.mem_univ N) h

@[expose] noncomputable def blockSum
    (e : (N : I) → fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≃ₗ[ZMod 2]
      fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) : V →ₗ[ZMod 2] V :=
  ∑ N : I, blockExtend (N : Subgroup (V ≃ₗ[ZMod 2] V)) (e N).toLinearMap

variable (e : (N : I) → fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≃ₗ[ZMod 2]
  fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)))

theorem blockSum_apply (v : V) : blockSum e v =
    ∑ N : I, (e N ⟨avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v, avgMap_mem_fixedSub v⟩ : V) := by
  rw [blockSum, LinearMap.sum_apply]
  rfl

include hB hI in
theorem blockSum_apply_block (N : I) (x : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) :
    blockSum e x = (e N x : V) :=
  sum_blockExtend_apply hB hI (fun N => (e N).toLinearMap) N x

include hB hI in
theorem blockSum_symm_apply (v : V) : blockSum e (blockSum (fun N => (e N).symm) v) = v := by
  rw [blockSum_apply (fun N => (e N).symm), map_sum]
  conv_rhs => rw [eq_sum_avgMap_coe hB hI v]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [blockSum_apply_block hB hI e N, LinearEquiv.apply_symm_apply]

include hB hI in
theorem symm_blockSum_apply (v : V) : blockSum (fun N => (e N).symm) (blockSum e v) = v := by
  have h := blockSum_symm_apply hB hI (fun N => (e N).symm) v
  simpa only [LinearEquiv.symm_symm] using h

include hB hI in
theorem blockSum_isometry
    (he : ∀ (N : I) (x : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))), q (e N x : V) = q x)
    (v : V) : q (blockSum e v) = q v := by
  classical
  have horth : ∀ (y : (N : I) → V), (∀ N : I, y N ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) →
      q (∑ N : I, y N) = ∑ N : I, q (y N) := fun y hy =>
    map_sum_of_polar_eq_zero _ _ fun N _ N' _ hne =>
      hB.polar_eq_zero_of_ne ((hI N).1 N.2).1 ((hI N).1 N.2).2.1 ((hI N').1 N'.2).1
        ((hI N').1 N'.2).2.1 (fun h => hne (Subtype.ext h).symm) (hy N) (hy N')
  rw [blockSum_apply, horth _ fun N => (e N _).2]
  conv_rhs => rw [eq_sum_avgMap_coe hB hI v, horth _ fun N => avgMap_mem_fixedSub v]
  exact Finset.sum_congr rfl fun N _ => he N _

include hB hI hc in
theorem blockSum_comm
    (he : ∀ (N : I) (x : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
      (e N ⟨c N x, hB.apply_mem_fixedSub ((hI N).1 N.2).1 (hc N).1 x.2⟩ : V) = c N (e N x : V))
    {b : V ≃ₗ[ZMod 2] V} (hb : b ∈ B) (v : V) : b (blockSum e v) = blockSum e (b v) := by
  rw [blockSum_apply, blockSum_apply, map_sum]
  refine Finset.sum_congr rfl fun N _ => ?_
  have hNB := ((hI N).1 N.2).1
  have hbN : ∀ x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)),
      b x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) :=
    fun x hx => hB.apply_mem_fixedSub hNB hb hx
  have hrw : (⟨avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) (b v), avgMap_mem_fixedSub (b v)⟩ :
      fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) =
        ⟨b (avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v), hbN _ (avgMap_mem_fixedSub v)⟩ :=
    Subtype.ext (hB.apply_avgMap_comm hNB hb v).symm
  rw [hrw]
  generalize hx : (⟨avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v, avgMap_mem_fixedSub v⟩ :
    fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = x
  have hxv : avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v = x := congrArg Subtype.val hx
  have e2 : (⟨b (avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v), hbN _ (avgMap_mem_fixedSub v)⟩ :
      fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = ⟨b x, hbN _ x.2⟩ := Subtype.ext (congrArg b hxv)
  rw [e2]
  have hex := (e N x).2
  rcases block_action_cases hB ((hI N).1 N.2).2.1 (hc N).1 (hc N).2 hb with h | h | h
  · have e1 : (⟨b x, hbN _ x.2⟩ : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = x :=
      Subtype.ext (h x x.2)
    rw [e1, h _ hex]
  · have e1 : (⟨b x, hbN _ x.2⟩ : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) =
        ⟨c N x, hB.apply_mem_fixedSub hNB (hc N).1 x.2⟩ := Subtype.ext (h x x.2)
    rw [e1, he, h _ hex]
  · have hcx := hB.apply_mem_fixedSub hNB (hc N).1 x.2
    have e1 : (⟨b x, hbN _ x.2⟩ : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) =
        ⟨c N (⟨c N x, hcx⟩ : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
          hB.apply_mem_fixedSub hNB (hc N).1 hcx⟩ := Subtype.ext (h x x.2)
    rw [e1, he, he, h _ hex]

include hB in
theorem centralizerToPi_surjective :
    Function.Surjective (centralizerToPi hB hI c hc h3 hfp) := by
  intro u
  have hNB : ∀ N : I, (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≤ B := fun N => ((hI N).1 N.2).1
  have hmem := fun N : I =>
    (mem_omegaUnitaryGroup_iff (blockGen_isometry hB (hNB N) (hc N).1)).mp (u N).2
  have hq : ∀ (N : I) (x : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
      q ((u N).1 x : V) = q x := fun N x => by
    have h := (hmem N).2 x
    rwa [QuadraticMap.comp_apply, QuadraticMap.comp_apply, Submodule.subtype_apply,
      Submodule.subtype_apply] at h
  have hcomm : ∀ (N : I) (x : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
      ((u N).1 ⟨c N x, hB.apply_mem_fixedSub (hNB N) (hc N).1 x.2⟩ : V) =
        c N ((u N).1 x : V) := fun N x => by
    have h := congrArg Subtype.val ((hmem N).1 x)
    rw [blockGen_apply_of_mem hB (hNB N) (hc N).1] at h
    rw [← h]
    congr 2
    exact Subtype.ext (blockGen_apply_of_mem hB (hNB N) (hc N).1 x).symm
  set e : (N : I) → fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≃ₗ[ZMod 2]
    fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) := fun N => (u N).1 with he
  let g : V ≃ₗ[ZMod 2] V := LinearEquiv.ofLinearMap (blockSum e) (blockSum fun N => (e N).symm)
    (LinearMap.ext fun v => blockSum_symm_apply hB hI e v)
    (LinearMap.ext fun v => symm_blockSum_apply hB hI e v)
  have hgv : ∀ v, g v = blockSum e v := fun v => rfl
  have hgC : g ∈ Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgv, hgv]
    exact blockSum_comm hB hI c hc e hcomm hb v
  have hgO : g ∈ orthogonalGroup q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hgv]
    exact blockSum_isometry hB hI e hq v
  refine ⟨⟨g, Subgroup.mem_inf.mpr ⟨hgC, hgO⟩⟩, ?_⟩
  funext N
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  rw [centralizerToPi_apply]
  exact blockSum_apply_block hB hI e N x


include hB hI in
theorem map_sum_blocks (y : (N : I) → V)
    (hy : ∀ N : I, y N ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) :
    q (∑ N : I, y N) = ∑ N : I, q (y N) := by
  classical
  exact map_sum_of_polar_eq_zero _ _ fun N _ N' _ hne =>
    hB.polar_eq_zero_of_ne ((hI N).1 N.2).1 ((hI N).1 N.2).2.1 ((hI N').1 N'.2).1
      ((hI N').1 N'.2).2.1 (fun h => hne (Subtype.ext h).symm) (hy N) (hy N')

omit [FiniteDimensional (ZMod 2) V] in
include hB in
theorem eq_polar_of_mem_block {N : Subgroup (V ≃ₗ[ZMod 2] V)} (hNB : N ≤ B)
    (hidx : N.relIndex B = 3) {c₀ : V ≃ₗ[ZMod 2] V} (hcB : c₀ ∈ B) (hcN : c₀ ∉ N) {y : V}
    (hy : y ∈ fixedSub N) : q y = polar q y (c₀ y) := by
  have h := eq_polar_apply (blockGen_isometry hB hNB hcB) (blockGen_add_add hB hNB hidx hcB hcN)
    ⟨y, hy⟩
  rwa [QuadraticMap.comp_apply, Submodule.subtype_apply, polar_comp_subtype,
    blockGen_apply_of_mem hB hNB hcB] at h

include hB hI hc in
theorem centralizer_inf_polarIsometryGroup :
    Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ polarIsometryGroup q =
      Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgC, hgS⟩ := Subgroup.mem_inf.mp hg
    refine Subgroup.mem_inf.mpr ⟨hgC, ?_⟩
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    have hgN : ∀ N : I, ∀ x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)),
        g x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) := fun N x hx n hn => by
      rw [← LinearEquiv.mul_apply, Subgroup.mem_centralizer_iff.mp hgC n (((hI N).1 N.2).1 hn),
        LinearEquiv.mul_apply, hx n hn]
    have hblk : ∀ N : I, ∀ x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)), q (g x) = q x := by
      intro N x hx
      have hNB := ((hI N).1 N.2).1
      have hidx := ((hI N).1 N.2).2.1
      rw [eq_polar_of_mem_block hB hNB hidx (hc N).1 (hc N).2 (hgN N x hx),
        eq_polar_of_mem_block hB hNB hidx (hc N).1 (hc N).2 hx]
      have hcg : c N (g x) = g (c N x) := by
        rw [← LinearEquiv.mul_apply, Subgroup.mem_centralizer_iff.mp hgC _ (hc N).1,
          LinearEquiv.mul_apply]
      rw [hcg, mem_polarIsometryGroup.mp hgS]
    conv_lhs => rw [eq_sum_avgMap_coe hB hI v, map_sum]
    conv_rhs => rw [eq_sum_avgMap_coe hB hI v]
    rw [map_sum_blocks hB hI _ fun N => hgN N _ (avgMap_mem_fixedSub v),
      map_sum_blocks hB hI _ fun N => avgMap_mem_fixedSub v]
    exact Finset.sum_congr rfl fun N _ => hblk N _ (avgMap_mem_fixedSub v)
  · refine inf_le_inf_left _ fun g hg => ?_
    exact mem_polarIsometryGroup.mpr fun x y => polar_map_of_mem_orthogonalGroup hg x y

@[expose] noncomputable def blockSumPerm (π : Equiv.Perm I)
    (e : (N : I) → fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2]
      fixedSub ((π N : I) : Subgroup (V ≃ₗ[ZMod 2] V))) : V →ₗ[ZMod 2] V :=
  ∑ N : I, (fixedSub ((π N : I) : Subgroup (V ≃ₗ[ZMod 2] V))).subtype ∘ₗ e N ∘ₗ
    (avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V))).codRestrict (fixedSub (N : Subgroup _))
      fun v => avgMap_mem_fixedSub v

section Perm

variable (π : Equiv.Perm I) (e : (N : I) → fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2]
  fixedSub ((π N : I) : Subgroup (V ≃ₗ[ZMod 2] V)))

theorem blockSumPerm_apply (v : V) : blockSumPerm π e v =
    ∑ N : I, (e N ⟨avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) v, avgMap_mem_fixedSub v⟩ : V) := by
  rw [blockSumPerm, LinearMap.sum_apply]
  rfl

include hB hI in
theorem blockSumPerm_apply_block (N : I) (x : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) :
    blockSumPerm π e x = (e N x : V) := by
  classical
  rw [blockSumPerm_apply, Finset.sum_eq_single N]
  · congr 2
    exact Subtype.ext (by
      change avgMap (N : Subgroup (V ≃ₗ[ZMod 2] V)) (x : V) = x
      simp [avgMap_block hB hI N N x.2])
  · intro N' _ hne
    have h0 : (⟨avgMap (N' : Subgroup (V ≃ₗ[ZMod 2] V)) x, avgMap_mem_fixedSub (x : V)⟩ :
        fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V))) = 0 :=
      Subtype.ext (by
        change avgMap (N' : Subgroup (V ≃ₗ[ZMod 2] V)) (x : V) = 0
        simp [avgMap_block hB hI N' N x.2, hne])
    rw [h0, map_zero]
    rfl
  · intro h
    exact absurd (Finset.mem_univ N) h

include hB hI in
theorem blockSumPerm_injective (he : ∀ N, Function.Injective (e N)) :
    Function.Injective (blockSumPerm π e) := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker, blockSumPerm_apply] at hv
  rw [Submodule.mem_bot]
  have hcomp : ∀ N₀ : I, avgMap (N₀ : Subgroup (V ≃ₗ[ZMod 2] V)) v = 0 := by
    intro N₀
    have h1 := congrArg (avgMap ((π N₀ : I) : Subgroup (V ≃ₗ[ZMod 2] V))) hv
    rw [map_sum, map_zero, Finset.sum_eq_single N₀] at h1
    · rw [avgMap_block hB hI (π N₀) (π N₀) (e N₀ _).2, ite_eq_left_of_eq_true _ _ (eq_self _)] at h1
      have h2 : e N₀ ⟨avgMap (N₀ : Subgroup (V ≃ₗ[ZMod 2] V)) v, avgMap_mem_fixedSub v⟩ = 0 :=
        Subtype.ext h1
      have h3 := he N₀ (h2.trans (map_zero _).symm)
      exact congrArg Subtype.val h3
    · intro N _ hne
      rw [avgMap_block hB hI (π N₀) (π N) (e N _).2,
        ite_eq_right_of_eq_false _ _ (eq_false fun h => hne (π.injective h).symm)]
    · intro h
      exact absurd (Finset.mem_univ N₀) h
  rw [eq_sum_avgMap_coe hB hI v]
  exact Finset.sum_eq_zero fun N _ => hcomp N

include hB hI in
theorem blockSumPerm_isometry
    (he : ∀ (N : I) (x : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))), q (e N x : V) = q x)
    (v : V) : q (blockSumPerm π e v) = q v := by
  classical
  rw [blockSumPerm_apply, map_sum_of_polar_eq_zero _ _ fun N _ N' _ hne =>
    hB.polar_eq_zero_of_ne ((hI (π N)).1 (π N).2).1 ((hI (π N)).1 (π N).2).2.1
      ((hI (π N')).1 (π N').2).1 ((hI (π N')).1 (π N').2).2.1
      (fun h => hne (π.injective (Subtype.ext h)).symm) (e N _).2 (e N' _).2]
  conv_rhs => rw [eq_sum_avgMap_coe hB hI v, map_sum_blocks hB hI _ fun N => avgMap_mem_fixedSub v]
  exact Finset.sum_congr rfl fun N _ => he N _

end Perm

end Iso

section Planes

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {B : Subgroup (V ≃ₗ[ZMod 2] V)}
  (hB : KernelBlockHyp q B) {N : Subgroup (V ≃ₗ[ZMod 2] V)} (hNB : N ≤ B)
  (hidx : N.relIndex B = 3) {c₀ : V ≃ₗ[ZMod 2] V} (hcB : c₀ ∈ B) (hcN : c₀ ∉ N)
  (h2 : finrank (ZMod 2) (fixedSub N) = 2)

include hB hNB hidx hcB hcN h2 in
theorem pair_basis {x : fixedSub N} (hx : x ≠ 0) :
    LinearIndependent (ZMod 2)
        ![x, (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) x] ∧
      Submodule.span (ZMod 2)
        (Set.range ![x, (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) x]) = ⊤ := by
  have hli : LinearIndependent (ZMod 2)
      ![x, (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have key : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    have hσx : (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) x ≠ 0 := by
      intro h0
      apply hx
      have h1 := congrArg Subtype.val h0
      rw [blockGen_apply_of_mem hB hNB hcB] at h1
      apply Subtype.ext
      have h2' : c₀ (x : V) = c₀ 0 := by rw [h1, map_zero]; rfl
      exact c₀.injective h2'
    rcases key s with rfl | rfl <;> rcases key t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, zero_add, one_smul] at hst
      exact absurd hst hσx
    · rw [zero_smul, add_zero, one_smul] at hst
      exact absurd hst hx
    · rw [one_smul, one_smul] at hst
      exact absurd (blockGen_fix hB hNB hidx hcB hcN x (zmod2_vec_eq_of_add_eq_zero hst).symm) hx
  refine ⟨hli, hli.span_eq_top_of_card_eq_finrank' ?_⟩
  rw [Fintype.card_fin, h2]

include hB hNB hidx hcB hcN h2 in
theorem q_eq_one_of_ne_zero (hnd : ∀ x ∈ fixedSub N, (∀ y ∈ fixedSub N, polar q x y = 0) → x = 0)
    {x : V} (hx : x ∈ fixedSub N) (hx0 : x ≠ 0) : q x = 1 := by
  have key : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rw [eq_polar_of_mem_block hB hNB hidx hcB hcN hx]
  rcases key (polar q x (c₀ x)) with h | h
  · exfalso
    apply hx0
    refine hnd x hx fun y hy => ?_
    have hx' : (⟨x, hx⟩ : fixedSub N) ≠ 0 := fun h' => hx0 (congrArg Subtype.val h')
    have hy' : (⟨y, hy⟩ : fixedSub N) ∈ Submodule.span (ZMod 2)
        (Set.range ![(⟨x, hx⟩ : fixedSub N),
          (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) ⟨x, hx⟩]) := by
      rw [(pair_basis hB hNB hidx hcB hcN h2 hx').2]
      exact Submodule.mem_top
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hy'
    obtain ⟨a, b, hab⟩ := hy'
    have hy2 := congrArg Subtype.val hab
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
      blockGen_apply_of_mem hB hNB hcB] at hy2
    change a • x + b • c₀ x = y at hy2
    rw [← hy2, polar_add_right, polar_smul_right, polar_smul_right, zmod2_polar_self, h,
      smul_zero, smul_zero, add_zero]
  · exact h

include hB hNB hidx hcB hcN h2 in
theorem eq_of_commute_of_apply_eq {x : fixedSub N} (hx : x ≠ 0)
    {f f' : fixedSub N →ₗ[ZMod 2] fixedSub N}
    (hf : ∀ y, f ((blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) y) =
      (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) (f y))
    (hf' : ∀ y, f' ((blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) y) =
      (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) (f' y))
    (hxx : f x = f' x) : f = f' := by
  refine LinearMap.ext_on_range (pair_basis hB hNB hidx hcB hcN h2 hx).2 fun i => ?_
  fin_cases i
  · exact hxx
  · change f ((blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) x) =
      f' ((blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) x)
    rw [hf, hf', hxx]

include hB hNB hidx hcB hcN h2 in
theorem eq_or_eq_sq_of_cube {τ : fixedSub N →ₗ[ZMod 2] fixedSub N}
    (hτ3 : ∀ y, τ (τ (τ y)) = y) (hτfix : ∀ y, τ y = y → y = 0) :
    τ = (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) ∨
      τ = (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) ∘ₗ
        (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) := by
  set σ := (blockGen c₀ N : fixedSub N →ₗ[ZMod 2] fixedSub N) with hσ
  have hσ2 : ∀ y, σ (σ y) = y + σ y :=
    sq_apply_of_add_add (blockGen_add_add hB hNB hidx hcB hcN)
  have hσ3 : ∀ y, σ (σ (σ y)) = y :=
    cube_apply_of_add_add (blockGen_add_add hB hNB hidx hcB hcN)
  have hnt : Nontrivial (fixedSub N) := Module.nontrivial_of_finrank_eq_succ h2
  obtain ⟨x, hx⟩ := exists_ne (0 : fixedSub N)
  have hτinj : ∀ y, τ y = 0 → y = 0 := fun y hy => by
    rw [← hτ3 y, hy, map_zero, map_zero]
  have key : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hspan : ∀ y : fixedSub N, ∃ a b : ZMod 2, a • x + b • σ x = y := fun y => by
    have hy : y ∈ Submodule.span (ZMod 2) (Set.range ![x, σ x]) := by
      rw [(pair_basis hB hNB hidx hcB hcN h2 hx).2]
      exact Submodule.mem_top
    rwa [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hy
  have hcases : ∀ y : fixedSub N, y = 0 ∨ y = x ∨ y = σ x ∨ y = x + σ x := fun y => by
    obtain ⟨a, b, rfl⟩ := hspan y
    rcases key a with rfl | rfl <;> rcases key b with rfl | rfl <;> simp
  have hτx0 : τ x ≠ 0 := fun h => hx (hτinj x h)
  have hτxx : τ x ≠ x := fun h => hx (hτfix x h)
  have hττ0 : τ (τ x) ≠ 0 := fun h => hτx0 (hτinj _ h)
  have hττx : τ (τ x) ≠ x := fun h => hτxx (by
    have h3 := hτ3 x
    rwa [h] at h3)
  have hττ1 : τ (τ x) ≠ τ x := fun h => hτx0 (hτfix _ h)
  have hσx : σ x ≠ x := fun h => hx (blockGen_fix hB hNB hidx hcB hcN x h)
  rcases hcases (τ x) with h | h | h | h
  · exact absurd h hτx0
  · exact absurd h hτxx
  ·
    left
    have hττ : τ (τ x) = x + σ x := by
      rcases hcases (τ (τ x)) with h' | h' | h' | h'
      · exact absurd h' hττ0
      · exact absurd h' hττx
      · exact absurd (h'.trans h.symm) hττ1
      · exact h'
    have hτσ : τ (σ x) = σ (σ x) := by
      calc τ (σ x) = τ (τ x) := by rw [h]
        _ = σ (σ x) := by rw [hττ, hσ2]
    refine LinearMap.ext_on_range (pair_basis hB hNB hidx hcB hcN h2 hx).2 fun i => ?_
    fin_cases i
    · exact h
    · exact hτσ
  ·
    right
    have hττ : τ (τ x) = σ x := by
      rcases hcases (τ (τ x)) with h' | h' | h' | h'
      · exact absurd h' hττ0
      · exact absurd h' hττx
      · exact h'
      · exact absurd (h'.trans h.symm) hττ1
    have hσxe : σ x = τ x + x := by
      rw [h, add_comm x, add_assoc, zmod2_vec_add_self, add_zero]
    refine LinearMap.ext_on_range (pair_basis hB hNB hidx hcB hcN h2 hx).2 fun i => ?_
    fin_cases i
    · change τ x = σ (σ x)
      rw [h, hσ2]
    · change τ (σ x) = σ (σ (σ x))
      rw [hσ3]
      calc τ (σ x) = τ (τ x + x) := by rw [← hσxe]
        _ = τ (τ x) + τ x := map_add _ _ _
        _ = σ x + τ x := by rw [hττ]
        _ = τ x + x + τ x := by rw [hσxe]
        _ = x := by rw [add_comm (τ x) x, add_assoc, zmod2_vec_add_self, add_zero]

theorem pair_basis_of_add_add {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 2) {τ : W →ₗ[ZMod 2] W}
    (hτ2 : ∀ y, y + τ y + τ (τ y) = 0)
    (hτfix : ∀ y, τ y = y → y = 0) {w : W} (hw : w ≠ 0) :
    LinearIndependent (ZMod 2) ![w, τ w] ∧ Submodule.span (ZMod 2) (Set.range ![w, τ w]) = ⊤ := by
  have hli : LinearIndependent (ZMod 2) ![w, τ w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have key : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    have hτw : τ w ≠ 0 := by
      intro h0
      apply hw
      have h := hτ2 w
      rw [h0, map_zero, add_zero, add_zero] at h
      exact h
    rcases key s with rfl | rfl <;> rcases key t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, zero_add, one_smul] at hst
      exact absurd hst hτw
    · rw [zero_smul, add_zero, one_smul] at hst
      exact absurd hst hw
    · rw [one_smul, one_smul] at hst
      exact absurd (hτfix w (zmod2_vec_eq_of_add_eq_zero hst).symm) hw
  refine ⟨hli, hli.span_eq_top_of_card_eq_finrank' ?_⟩
  rw [Fintype.card_fin, hW]

theorem exists_intertwining {W₁ W₂ : Type*} [AddCommGroup W₁] [Module (ZMod 2) W₁]
    [FiniteDimensional (ZMod 2) W₁] [AddCommGroup W₂] [Module (ZMod 2) W₂]
    [FiniteDimensional (ZMod 2) W₂] (h₁ : finrank (ZMod 2) W₁ = 2)
    (h₂ : finrank (ZMod 2) W₂ = 2) {σ : W₁ →ₗ[ZMod 2] W₁} (hσ2 : ∀ y, y + σ y + σ (σ y) = 0)
    (hσfix : ∀ y, σ y = y → y = 0) {τ : W₂ →ₗ[ZMod 2] W₂} (hτ2 : ∀ y, y + τ y + τ (τ y) = 0)
    (hτfix : ∀ y, τ y = y → y = 0) : ∃ φ : W₁ ≃ₗ[ZMod 2] W₂, ∀ y, φ (σ y) = τ (φ y) := by
  have : Nontrivial W₁ := Module.nontrivial_of_finrank_eq_succ h₁
  have : Nontrivial W₂ := Module.nontrivial_of_finrank_eq_succ h₂
  obtain ⟨v, hv⟩ := exists_ne (0 : W₁)
  obtain ⟨w, hw⟩ := exists_ne (0 : W₂)
  obtain ⟨hli₁, hsp₁⟩ := pair_basis_of_add_add h₁ hσ2 hσfix hv
  obtain ⟨hli₂, hsp₂⟩ := pair_basis_of_add_add h₂ hτ2 hτfix hw
  set b₁ := Module.Basis.mk hli₁ hsp₁.ge with hb₁
  set b₂ := Module.Basis.mk hli₂ hsp₂.ge with hb₂
  set φ := b₁.equiv b₂ (Equiv.refl _) with hφ
  have hb₁0 : b₁ 0 = v := by rw [hb₁, Module.Basis.mk_apply]; rfl
  have hb₁1 : b₁ 1 = σ v := by rw [hb₁, Module.Basis.mk_apply]; rfl
  have hb₂0 : b₂ 0 = w := by rw [hb₂, Module.Basis.mk_apply]; rfl
  have hb₂1 : b₂ 1 = τ w := by rw [hb₂, Module.Basis.mk_apply]; rfl
  have hφv : φ v = w := by
    rw [← hb₁0, hφ, Module.Basis.equiv_apply, Equiv.refl_apply, hb₂0]
  have hφσv : φ (σ v) = τ w := by
    rw [← hb₁1, hφ, Module.Basis.equiv_apply, Equiv.refl_apply, hb₂1]
  have key : (φ : W₁ →ₗ[ZMod 2] W₂) ∘ₗ σ = τ ∘ₗ (φ : W₁ →ₗ[ZMod 2] W₂) := by
    refine b₁.ext fun i => ?_
    fin_cases i
    · change φ (σ (b₁ 0)) = τ (φ (b₁ 0))
      rw [hb₁0, hφσv, hφv]
    · change φ (σ (b₁ 1)) = τ (φ (b₁ 1))
      rw [hb₁1, sq_apply_of_add_add hσ2, map_add, hφv, hφσv, sq_apply_of_add_add hτ2]
  exact ⟨φ, fun y => LinearMap.congr_fun key y⟩

end Planes

section Coord

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
  {B : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem exists_coordHom (hB : KernelBlockHyp q B) {N : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hidx : N.relIndex B = 3) {c : V ≃ₗ[ZMod 2] V} (hcB : c ∈ B) (hcN : c ∉ N) :
    ∃ ρ : ↥B →* Multiplicative (ZMod 3), (∀ b : B, ρ b = 1 ↔ (b : V ≃ₗ[ZMod 2] V) ∈ N) ∧
      ρ ⟨c, hcB⟩ = Multiplicative.ofAdd 1 := by
  have hc3 : c ^ 3 = 1 := hB.cube c hcB
  have hnormal : (N.subgroupOf B).Normal := ⟨fun n hn g => by
    have e : g * n * g⁻¹ = n := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subtype.ext (hB.comm _ g.2 _ n.2)
    rw [e]
    exact hn⟩
  have hQ : Nat.card (↥B ⧸ N.subgroupOf B) = 3 := hidx
  have key : ∀ x y : B, (QuotientGroup.mk x : ↥B ⧸ N.subgroupOf B) = QuotientGroup.mk y ↔
      (x : V ≃ₗ[ZMod 2] V)⁻¹ * y ∈ N := fun x y => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hgen : ∀ x : ↥B ⧸ N.subgroupOf B,
      x ∈ Subgroup.zpowers (QuotientGroup.mk ⟨c, hcB⟩ : ↥B ⧸ N.subgroupOf B) := by
    intro x
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective x
    rcases mem_or_of_relIndex_eq_three hidx hcB hcN hc3 hb with h | h | h
    · have e : (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ N.subgroupOf B) = QuotientGroup.mk 1 :=
        ((key _ _).2 (by simpa using h)).symm
      rw [e, QuotientGroup.mk_one]
      exact one_mem _
    · rw [← (key ⟨c, hcB⟩ ⟨b, hb⟩).2 h]
      exact Subgroup.mem_zpowers _
    · have e : (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ N.subgroupOf B) =
          QuotientGroup.mk (⟨c, hcB⟩ ^ 2) := ((key _ _).2 h).symm
      rw [e, QuotientGroup.mk_pow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  let e := zmodMulEquivOfGenerator hgen hQ
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf B)), fun b => ?_, ?_⟩
  · have h1 : (e.symm.toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf B))) b = 1 ↔
        (QuotientGroup.mk b : ↥B ⧸ N.subgroupOf B) = 1 := by
      simp
    rw [h1, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · change e.symm (QuotientGroup.mk ⟨c, hcB⟩) = _
    exact zmodMulEquivOfGenerator_symm_apply_generator hgen hQ

theorem apply_eq_pow_coord {N : Subgroup (V ≃ₗ[ZMod 2] V)} {c : V ≃ₗ[ZMod 2] V} (hcB : c ∈ B)
    {ρ : ↥B →* Multiplicative (ZMod 3)} (hρ : ∀ b : B, ρ b = 1 ↔ (b : V ≃ₗ[ZMod 2] V) ∈ N)
    (hρc : ρ ⟨c, hcB⟩ = Multiplicative.ofAdd 1) (b : B) {x : V} (hx : x ∈ fixedSub N) :
    (b : V ≃ₗ[ZMod 2] V) x = (c ^ (Multiplicative.toAdd (ρ b)).val) x := by
  set j := (Multiplicative.toAdd (ρ b)).val with hj
  have hρj : ρ (⟨c, hcB⟩ ^ j) = ρ b := by
    rw [map_pow, hρc, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, hj, ZMod.natCast_zmod_val]
    rfl
  have hmem : ((b⁻¹ * ⟨c, hcB⟩ ^ j : B) : V ≃ₗ[ZMod 2] V) ∈ N := by
    rw [← hρ, map_mul, map_inv, hρj, inv_mul_cancel]
  have h := hx _ hmem
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, LinearEquiv.mul_apply] at h
  calc (b : V ≃ₗ[ZMod 2] V) x = (b : V ≃ₗ[ZMod 2] V) ((b : V ≃ₗ[ZMod 2] V)⁻¹ ((c ^ j) x)) := by
        rw [h]
    _ = (c ^ j) x := apply_inv_apply _ _

end Coord

section MEqR

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {B : Subgroup (V ≃ₗ[ZMod 2] V)}
  (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
  (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥)
  (c : I → V ≃ₗ[ZMod 2] V) (hc : ∀ N, c N ∈ B ∧ c N ∉ (N : Subgroup (V ≃ₗ[ZMod 2] V)))

attribute [local instance] KernelBlockHyp.finite_subgroup

omit [FiniteDimensional (ZMod 2) V] in
include hB hI hc in
theorem exists_coordEquiv (hcard : Nat.card B = 3 ^ I.card) (hinf : B ⊓ ⨅ N ∈ I, N = ⊥) :
    ∃ κ : B ≃* Multiplicative (I → ZMod 3),
      (∀ (b : B) (N : I), Multiplicative.toAdd (κ b) N = 0 ↔
        (b : V ≃ₗ[ZMod 2] V) ∈ (N : Subgroup (V ≃ₗ[ZMod 2] V))) ∧
      (∀ N : I, Multiplicative.toAdd (κ ⟨c N, (hc N).1⟩) N = 1) ∧
      ∀ (b : B) (N : I) {x : V}, x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →
        (b : V ≃ₗ[ZMod 2] V) x = (c N ^ (Multiplicative.toAdd (κ b) N).val) x := by
  choose ρ hρ hρc using fun N : I => exists_coordHom hB ((hI N).1 N.2).2.1 (hc N).1 (hc N).2
  let κ₀ : ↥B →* Multiplicative (I → ZMod 3) :=
    { toFun := fun b => Multiplicative.ofAdd fun N => Multiplicative.toAdd (ρ N b)
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext N
        simp
      map_mul' := fun b b' => by
        apply Multiplicative.toAdd.injective
        funext N
        simp [toAdd_mul] }
  have hκ₀ : ∀ b N, Multiplicative.toAdd (κ₀ b) N = Multiplicative.toAdd (ρ N b) :=
    fun _ _ => rfl
  have hinj : Function.Injective κ₀ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hbN : ∀ N : I, (b : V ≃ₗ[ZMod 2] V) ∈ (N : Subgroup (V ≃ₗ[ZMod 2] V)) := fun N => by
      rw [← hρ]
      have h := congrFun (congrArg Multiplicative.toAdd hb) N
      rw [hκ₀] at h
      exact Multiplicative.toAdd.injective h
    have hmem : (b : V ≃ₗ[ZMod 2] V) ∈ B ⊓ ⨅ N ∈ I, N := Subgroup.mem_inf.mpr
      ⟨b.2, Subgroup.mem_iInf.mpr fun N => Subgroup.mem_iInf.mpr fun hN => hbN ⟨N, hN⟩⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hbij : Function.Bijective κ₀ := by
    refine hinj.bijective_of_nat_card_le ?_
    have h1 : Nat.card (Multiplicative (I → ZMod 3)) = 3 ^ I.card := by
      change Nat.card (I → ZMod 3) = _
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [h1, hcard]
  refine ⟨MulEquiv.ofBijective κ₀ hbij, fun b N => ?_, fun N => ?_, fun b N x hx => ?_⟩
  · change Multiplicative.toAdd (κ₀ b) N = 0 ↔ _
    rw [hκ₀, ← hρ, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff]
  · change Multiplicative.toAdd (κ₀ _) N = 1
    rw [hκ₀, hρc]
    rfl
  · change _ = (c N ^ (Multiplicative.toAdd (κ₀ b) N).val) x
    rw [hκ₀]
    exact apply_eq_pow_coord (hc N).1 (hρ N) (hρc N) b hx

theorem pow_mod_three {G : Type*} [Monoid G] {g : G} (hg : g ^ 3 = 1) (j : ℕ) :
    g ^ (j % 3) = g ^ j := by
  conv_rhs => rw [← Nat.mod_add_div j 3, pow_add, pow_mul, hg, one_pow, mul_one]

include hB hI hc in
theorem mem_of_block_pow {κ : B ≃* Multiplicative (I → ZMod 3)}
    (hκ3 : ∀ (b : B) (N : I) {x : V}, x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →
      (b : V ≃ₗ[ZMod 2] V) x = (c N ^ (Multiplicative.toAdd (κ b) N).val) x)
    {h : V ≃ₗ[ZMod 2] V}
    (hh : ∀ N : I, ∃ j : ℕ, ∀ x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)), h x = (c N ^ j) x) :
    h ∈ B := by
  choose j hj using hh
  set b := κ.symm (Multiplicative.ofAdd fun N => (j N : ZMod 3)) with hbdef
  have hbk : ∀ N, (Multiplicative.toAdd (κ b) N).val = j N % 3 := fun N => by
    rw [hbdef, MulEquiv.apply_symm_apply, toAdd_ofAdd, ZMod.val_natCast]
  have hb : (b : V ≃ₗ[ZMod 2] V) = h := by
    apply LinearEquiv.ext
    intro v
    rw [eq_sum_avgMap_coe hB hI v, map_sum, map_sum]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [hκ3 b N (avgMap_mem_fixedSub v), hj N _ (avgMap_mem_fixedSub v), hbk,
      pow_mod_three (hB.cube _ (hc N).1)]
  rw [← hb]
  exact b.2

include hB hI hc in
theorem natCard_omegaUnitaryGroup_le (N : I)
    (h2 : finrank (ZMod 2) (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = 2)
    (h3 : orderOf (blockGen (c N) N) = 3)
    (hfp : ∀ v : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)),
      (blockGen (c N) N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2] _) v = v → v = 0) :
    Nat.card (omegaUnitaryGroup (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
      (blockGen (c N) N) h3 hfp) ≤ 3 := by
  have hNB := ((hI N).1 N.2).1
  have hidx := ((hI N).1 N.2).2.1
  have hnt : Nontrivial (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) :=
    Module.nontrivial_of_finrank_eq_succ h2
  obtain ⟨x, hx⟩ := exists_ne (0 : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)))
  have hfin := finite_linearEquiv_zmod2 (V := fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)))
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) := Fintype.ofFinite _
  have : Fintype (omegaUnitaryGroup (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
      (blockGen (c N) N) h3 hfp) := Fintype.ofFinite _
  let f : omegaUnitaryGroup (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
      (blockGen (c N) N) h3 hfp → fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) := fun u => u.1 x
  have hf : Function.Injective f := by
    intro u u' huu
    have hcomm := fun (w : omegaUnitaryGroup (q.comp (fixedSub
      (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype) (blockGen (c N) N) h3 hfp) =>
      ((mem_omegaUnitaryGroup_iff (blockGen_isometry hB hNB (hc N).1)).mp w.2).1
    have h := eq_of_commute_of_apply_eq hB hNB hidx (hc N).1 (hc N).2 h2 hx (hcomm u) (hcomm u')
      huu
    exact Subtype.ext (LinearEquiv.toLinearMap_injective h)
  have hns : ¬ Function.Surjective f := by
    intro hsurj
    obtain ⟨u, hu⟩ := hsurj 0
    exact hx (u.1.injective (hu.trans (map_zero _).symm))
  have hlt := Fintype.card_lt_of_injective_not_surjective f hf hns
  have h4 : Fintype.card (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = 4 := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      h2]
    norm_num
  rw [Nat.card_eq_fintype_card]
  omega

include hB hI hc in
theorem centralizer_inf_orthogonalGroup_eq_of_two (hcard : Nat.card B = 3 ^ I.card)
    (h2 : ∀ N : I, finrank (ZMod 2) (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = 2)
    (h3 : ∀ N : I, orderOf (blockGen (c N) N) = 3)
    (hfp : ∀ (N : I) (v : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
      (blockGen (c N) N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2] _) v = v → v = 0) :
    Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q = B := by
  have hfin := finite_linearEquiv_zmod2 (V := V)
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · intro b hb
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun b' hb' =>
      hB.comm b' hb' b hb, hB.orth hb⟩
  · let e := MulEquiv.ofBijective (centralizerToPi hB hI c hc h3 hfp)
      ⟨centralizerToPi_injective hB hI c hc h3 hfp, centralizerToPi_surjective hB hI c hc h3 hfp⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_pi, hcard]
    calc ∏ N : I, Nat.card (omegaUnitaryGroup
          (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
          (blockGen (c N) N) (h3 N) (hfp N)) ≤ ∏ _N : I, 3 :=
        Finset.prod_le_prod fun N _ =>
          natCard_omegaUnitaryGroup_le hB hI c hc N (h2 N) (h3 N) (hfp N)
      _ = 3 ^ I.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

include hB hI in
theorem eq_of_fixedSub_eq {N₁ N₂ : Subgroup (V ≃ₗ[ZMod 2] V)} (h₁ : N₁ ∈ I) (h₂ : N₂ ∈ I)
    (h : fixedSub N₁ = fixedSub N₂) : N₁ = N₂ := by
  by_contra hne
  obtain ⟨hN₁B, hidx₁, hN₁0⟩ := (hI N₁).1 h₁
  obtain ⟨hN₂B, hidx₂, -⟩ := (hI N₂).1 h₂
  apply hN₁0
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hx2 : x ∈ fixedSub N₂ := h ▸ hx
  rw [← hB.avgMap_eq_self hN₁B hx]
  exact hB.avgMap_eq_zero hN₁B hidx₁ hN₂B hidx₂ (Ne.symm hne) hx2

include hB hI hc in
theorem conj_block_eq {N N' : I}
    (h2 : finrank (ZMod 2) (fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V))) = 2)
    {g : V ≃ₗ[ZMod 2] V}
    (hg : (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).map (g : V →ₗ[ZMod 2] V) =
      fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V))) :
    (∀ y ∈ fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)), g (c N (g⁻¹ y)) = c N' y) ∨
      ∀ y ∈ fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)), g (c N (g⁻¹ y)) = c N' (c N' y) := by
  have hNB := ((hI N).1 N.2).1
  have hN'B := ((hI N').1 N'.2).1
  have hidxN := ((hI N).1 N.2).2.1
  have hidxN' := ((hI N').1 N'.2).2.1
  have hginv : ∀ y ∈ fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)),
      g⁻¹ y ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) := fun y hy => by
    rw [← hg] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [LinearEquiv.coe_coe, inv_apply_apply]
    exact hx
  have hgN : ∀ x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)),
      g x ∈ fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)) := fun x hx => by
    rw [← hg]
    exact ⟨x, hx, rfl⟩
  have hmaps : ∀ y ∈ fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)),
      ((g * c N * g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) y ∈
        fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)) := fun y hy => by
    change g (c N (g⁻¹ y)) ∈ _
    exact hgN _ (hB.apply_mem_fixedSub hNB (hc N).1 (hginv y hy))
  set τ := LinearMap.restrict ((g * c N * g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) hmaps
    with hτ
  have hτapp : ∀ y : fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)),
      (τ y : V) = g (c N (g⁻¹ y)) := fun y => rfl
  have hτ3 : ∀ y, τ (τ (τ y)) = y := fun y => by
    apply Subtype.ext
    rw [hτapp, hτapp, hτapp, inv_apply_apply, inv_apply_apply]
    have h3 : c N (c N (c N (g⁻¹ y))) = g⁻¹ y := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_three', hB.cube _ (hc N).1]
      rfl
    rw [h3, apply_inv_apply]
  have hτfix : ∀ y, τ y = y → y = 0 := fun y hy => by
    have h1 := congrArg Subtype.val hy
    rw [hτapp] at h1
    have h2' : c N (g⁻¹ y) = g⁻¹ y := by
      calc c N (g⁻¹ y) = g⁻¹ (g (c N (g⁻¹ y))) := (inv_apply_apply _ _).symm
        _ = g⁻¹ y := by rw [h1]
    have h0 := hB.eq_zero_of_fixed hidxN (hc N).1 (hc N).2 (hginv y y.2) h2'
    apply Subtype.ext
    rw [← apply_inv_apply g (y : V), h0, map_zero]
    rfl
  rcases eq_or_eq_sq_of_cube hB hN'B hidxN' (hc N').1 (hc N').2 h2 hτ3 hτfix with h | h
  · left
    intro y hy
    have h1 := congrArg Subtype.val (LinearMap.congr_fun h ⟨y, hy⟩)
    rw [hτapp, blockGen_apply_of_mem hB hN'B (hc N').1] at h1
    exact h1
  · right
    intro y hy
    have h1 := congrArg Subtype.val (LinearMap.congr_fun h ⟨y, hy⟩)
    rw [hτapp, LinearMap.comp_apply, blockGen_apply_of_mem hB hN'B (hc N').1,
      blockGen_apply_of_mem hB hN'B (hc N').1] at h1
    exact h1

include hB hI hc in
theorem mem_normalizer_of_perm {κ : B ≃* Multiplicative (I → ZMod 3)}
    (hκ3 : ∀ (b : B) (N : I) {x : V}, x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →
      (b : V ≃ₗ[ZMod 2] V) x = (c N ^ (Multiplicative.toAdd (κ b) N).val) x)
    (h2 : ∀ N : I, finrank (ZMod 2) (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = 2)
    {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ N ∈ I, ∃ N' ∈ I, (fixedSub N).map (g : V →ₗ[ZMod 2] V) = fixedSub N') :
    g ∈ Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) := by
  classical
  choose! π hπI hπ using hg
  have hsurj : ∀ N' ∈ I, ∃ N ∈ I, (fixedSub N).map (g : V →ₗ[ZMod 2] V) = fixedSub N' := by
    intro N' hN'
    have hinj : ∀ (N₁ N₂ : Subgroup (V ≃ₗ[ZMod 2] V)) (h₁ : N₁ ∈ I) (h₂ : N₂ ∈ I),
        π N₁ = π N₂ → N₁ = N₂ := fun N₁ N₂ h₁ h₂ heq => by
      apply eq_of_fixedSub_eq hB hI h₁ h₂
      have h := (hπ N₁ h₁).trans ((congrArg fixedSub heq).trans (hπ N₂ h₂).symm)
      exact Submodule.map_injective_of_injective g.injective h
    obtain ⟨N, hN, hNN'⟩ := Finset.surj_on_of_inj_on_of_card_le (fun N _ => π N)
      (fun N hN => hπI N hN) hinj le_rfl N' hN'
    exact ⟨N, hN, (hπ N hN).trans (by rw [hNN'])⟩
  have hconj : ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
    intro b hb
    refine mem_of_block_pow hB hI c hc hκ3 fun N' => ?_
    obtain ⟨N, hN, hNN'⟩ := hsurj N' N'.2
    have hginv : ∀ y ∈ fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)), g⁻¹ y ∈ fixedSub N :=
      fun y hy => by
        rw [← hNN'] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [LinearEquiv.coe_coe, inv_apply_apply]
        exact hx
    have hcases := conj_block_eq hB hI c hc (N := ⟨N, hN⟩) (N' := N') (h2 N') hNN'
    have hbN := block_action_cases hB ((hI N).1 hN).2.1 (hc ⟨N, hN⟩).1 (hc ⟨N, hN⟩).2 hb
    have hgy : ∀ y : V, (g * b * g⁻¹) y = g (b (g⁻¹ y)) := fun y => rfl
    have hgc : ∀ y ∈ fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)),
        g (c ⟨N, hN⟩ (c ⟨N, hN⟩ (g⁻¹ y))) =
          g (c ⟨N, hN⟩ (g⁻¹ (g (c ⟨N, hN⟩ (g⁻¹ y))))) := fun y _ => by
      rw [inv_apply_apply]
    have hmem : ∀ y ∈ fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)),
        g (c ⟨N, hN⟩ (g⁻¹ y)) ∈ fixedSub (N' : Subgroup (V ≃ₗ[ZMod 2] V)) := fun y hy => by
      rw [← hNN']
      exact ⟨_, hB.apply_mem_fixedSub ((hI N).1 hN).1 (hc ⟨N, hN⟩).1 (hginv y hy), rfl⟩
    rcases hbN with hb1 | hb1 | hb1
    · refine ⟨0, fun y hy => ?_⟩
      rw [hgy, hb1 _ (hginv y hy), apply_inv_apply, pow_zero]
      rfl
    · rcases hcases with h | h
      · exact ⟨1, fun y hy => by rw [hgy, hb1 _ (hginv y hy), h y hy, pow_one]⟩
      · exact ⟨2, fun y hy => by rw [hgy, hb1 _ (hginv y hy), h y hy, pow_two]; rfl⟩
    · rcases hcases with h | h
      · refine ⟨2, fun y hy => ?_⟩
        rw [hgy, hb1 _ (hginv y hy), hgc y hy, h _ (hmem y hy), h y hy, pow_two]
        rfl
      · refine ⟨4, fun y hy => ?_⟩
        rw [hgy, hb1 _ (hginv y hy), hgc y hy, h _ (hmem y hy), h y hy]
        change _ = (c N' * c N' * c N' * c N') y
        rfl
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj h, fun hh => ?_⟩
  have hfin := finite_linearEquiv_zmod2 (V := V)
  let f : B → B := fun b => ⟨g * b * g⁻¹, hconj b b.2⟩
  have hfinj : Function.Injective f := fun b b' hbb' => by
    have h1 := congrArg Subtype.val hbb'
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective hfinj ⟨g * h * g⁻¹, hh⟩
  have h1 : g * (b : V ≃ₗ[ZMod 2] V) * g⁻¹ = g * h * g⁻¹ := congrArg Subtype.val hb
  rw [← mul_left_cancel (mul_right_cancel h1)]
  exact b.2

omit [FiniteDimensional (ZMod 2) V] in
include hB hI in
theorem coord_eq_of_block_action {κ : B ≃* Multiplicative (I → ZMod 3)}
    (hκ1 : ∀ (b : B) (N : I), Multiplicative.toAdd (κ b) N = 0 ↔
      (b : V ≃ₗ[ZMod 2] V) ∈ (N : Subgroup (V ≃ₗ[ZMod 2] V)))
    (hκ2 : ∀ N : I, Multiplicative.toAdd (κ ⟨c N, (hc N).1⟩) N = 1) (b : B) (N : I) (j : ℕ)
    (hb : ∀ y ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)), (b : V ≃ₗ[ZMod 2] V) y = (c N ^ j) y) :
    Multiplicative.toAdd (κ b) N = j := by
  set b' : B := b⁻¹ * ⟨c N, (hc N).1⟩ ^ j with hb'
  have hfix : ∀ y ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)), (b' : V ≃ₗ[ZMod 2] V) y = y := by
    intro y hy
    rw [hb', Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, LinearEquiv.mul_apply, ← hb y hy,
      inv_apply_apply]
  have hmem := hB.mem_of_fixes_block ((hI N).1 N.2).2.1 ((hI N).1 N.2).2.2 b'.2 hfix
  rw [← hκ1, hb', map_mul, map_inv, map_pow, toAdd_mul, toAdd_inv, toAdd_pow] at hmem
  have h1 := hκ2 N
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply] at hmem
  rw [h1, nsmul_eq_mul, mul_one] at hmem
  linear_combination -hmem

end MEqR

section ConjCoord

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : Subgroup (V ≃ₗ[ZMod 2] V)}

@[expose] noncomputable def conjB (g : V ≃ₗ[ZMod 2] V)
    (hg : g ∈ Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V))) : B ≃* B where
  toFun b := ⟨g * b * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg b).mp b.2⟩
  invFun b := ⟨g⁻¹ * b * g, by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) b).mp b.2
    rwa [inv_inv] at h⟩
  left_inv b := Subtype.ext (by simp only; group)
  right_inv b := Subtype.ext (by simp only; group)
  map_mul' b b' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjB_apply {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V))) (b : B) :
    ((conjB g hg b : B) : V ≃ₗ[ZMod 2] V) = g * b * g⁻¹ := rfl

variable {I : Type*} [Fintype I] [DecidableEq I]

@[expose] noncomputable def coordLin (κ : B ≃* Multiplicative (I → ZMod 3)) (α : B ≃* B) :
    (I → ZMod 3) →ₗ[ZMod 3] (I → ZMod 3) :=
  (AddMonoidHom.toMultiplicative.symm
    (κ.toMonoidHom.comp (α.toMonoidHom.comp κ.symm.toMonoidHom))).toZModLinearMap 3

omit [Fintype I] [DecidableEq I] in
theorem coordLin_apply (κ : B ≃* Multiplicative (I → ZMod 3)) (α : B ≃* B) (x : I → ZMod 3) :
    coordLin κ α x = Multiplicative.toAdd (κ (α (κ.symm (Multiplicative.ofAdd x)))) := rfl

@[expose] noncomputable def conjMatrix (κ : B ≃* Multiplicative (I → ZMod 3))
    (H : Subgroup (V ≃ₗ[ZMod 2] V)) :
    ↥(Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ H) →* GL I (ZMod 3) :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix' (coordLin κ (conjB g (Subgroup.mem_inf.mp g.2).1))
      map_one' := by
        rw [← LinearMap.toMatrix'_id]
        congr 1
        apply LinearMap.ext
        intro x
        rw [coordLin_apply, LinearMap.id_apply]
        have h : conjB ((1 : ↥(Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ H)) :
            V ≃ₗ[ZMod 2] V) (Subgroup.mem_inf.mp (1 : ↥(Subgroup.normalizer
              (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ H)).2).1 (κ.symm (Multiplicative.ofAdd x)) =
            κ.symm (Multiplicative.ofAdd x) :=
          Subtype.ext (by rw [conjB_apply]; simp)
        rw [h, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      map_mul' := fun g g' => by
        rw [← LinearMap.toMatrix'_comp]
        congr 1
        apply LinearMap.ext
        intro x
        rw [LinearMap.comp_apply, coordLin_apply, coordLin_apply, coordLin_apply, ofAdd_toAdd,
          MulEquiv.symm_apply_apply]
        congr 2 }

theorem conjMatrix_val (κ : B ≃* Multiplicative (I → ZMod 3)) (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (g : ↥(Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ H)) :
    ((conjMatrix κ H g : GL I (ZMod 3)) : Matrix I I (ZMod 3)) =
      LinearMap.toMatrix' (coordLin κ (conjB g (Subgroup.mem_inf.mp g.2).1)) := rfl

theorem conjMatrix_mulVec (κ : B ≃* Multiplicative (I → ZMod 3)) (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (g : ↥(Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ H)) (b b' : B)
    (hb : (b' : V ≃ₗ[ZMod 2] V) = g * b * g⁻¹) :
    Multiplicative.toAdd (κ b') =
      Matrix.mulVec ((conjMatrix κ H g : GL I (ZMod 3)) : Matrix I I (ZMod 3))
        (Multiplicative.toAdd (κ b)) := by
  rw [conjMatrix_val, LinearMap.toMatrix'_mulVec, coordLin_apply, ofAdd_toAdd,
    MulEquiv.symm_apply_apply]
  congr 2
  exact Subtype.ext hb

theorem conjMatrix_eq_one_iff (κ : B ≃* Multiplicative (I → ZMod 3))
    (H : Subgroup (V ≃ₗ[ZMod 2] V)) (g : ↥(Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ H)) :
    conjMatrix κ H g = 1 ↔ (g : V ≃ₗ[ZMod 2] V) ∈ Subgroup.centralizer (B : Set _) := by
  rw [Units.ext_iff, Units.val_one, conjMatrix_val, ← LinearMap.toMatrix'_id,
    LinearMap.toMatrix'.injective.eq_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    have h1 := LinearMap.congr_fun h (Multiplicative.toAdd (κ ⟨b, hb⟩))
    rw [coordLin_apply, LinearMap.id_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg Subtype.val (κ.injective (Multiplicative.toAdd.injective h1))
    rw [conjB_apply] at h2
    change (g : V ≃ₗ[ZMod 2] V) * b * (g : V ≃ₗ[ZMod 2] V)⁻¹ = b at h2
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  · intro h
    apply LinearMap.ext
    intro x
    rw [coordLin_apply, LinearMap.id_apply]
    have h1 : conjB (g : V ≃ₗ[ZMod 2] V) (Subgroup.mem_inf.mp g.2).1
        (κ.symm (Multiplicative.ofAdd x)) = κ.symm (Multiplicative.ofAdd x) := by
      apply Subtype.ext
      rw [conjB_apply, mul_inv_eq_iff_eq_mul]
      exact (h _ (κ.symm (Multiplicative.ofAdd x)).2).symm
    rw [h1, MulEquiv.apply_symm_apply, toAdd_ofAdd]

@[expose] def IsSignedPerm {I : Type*} [DecidableEq I] (M : Matrix I I (ZMod 3)) : Prop :=
  ∃ (π : Equiv.Perm I) (ε : I → ZMod 3), (∀ N, ε N ≠ 0) ∧ ∀ i N, M i N = if i = π N then ε N else 0

theorem isSignedPerm_iff {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I (ZMod 3)) :
    IsSignedPerm M ↔ (∀ i, ∃! j, M i j ≠ 0) ∧ (∀ j, ∃! i, M i j ≠ 0) ∧
      ∀ i j, M i j = 0 ∨ M i j = 1 ∨ M i j = -1 := by
  have h3 : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = -1 := by decide
  constructor
  · rintro ⟨π, ε, hε, hM⟩
    refine ⟨fun i => ⟨π.symm i, ?_, fun j hj => ?_⟩, fun j => ⟨π j, ?_, fun i hi => ?_⟩,
      fun i j => h3 _⟩
    · show M i (π.symm i) ≠ 0
      simpa [hM] using hε (π.symm i)
    · change M i j ≠ 0 at hj
      rw [hM] at hj
      split_ifs at hj with h
      · rw [h, Equiv.symm_apply_apply]
      · exact absurd rfl hj
    · show M (π j) j ≠ 0
      simpa [hM] using hε j
    · change M i j ≠ 0 at hi
      rw [hM] at hi
      split_ifs at hi with h
      · exact h
      · exact absurd rfl hi
  · rintro ⟨hrow, hcol, -⟩
    choose π hπ hπu using hcol
    have hinj : Function.Injective π := fun j j' hjj' => by
      obtain ⟨k, -, hk⟩ := hrow (π j)
      have h1 := hk j (hπ j)
      have h2 := hk j' (by rw [hjj']; exact hπ j')
      rw [h1, h2]
    let πe : Equiv.Perm I := Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj)
    refine ⟨πe, fun N => M (π N) N, fun N => hπ N, fun i N => ?_⟩
    change M i N = if i = π N then M (π N) N else 0
    split_ifs with h
    · rw [h]
    · by_contra hne
      exact h (hπu N i hne)

end ConjCoord

section NormalizerImage

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
  {B : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}

open _root_.Classical in
theorem conjMatrix_isSignedPerm {κ : B ≃* Multiplicative (I → ZMod 3)}
    (hκ1 : ∀ (b : B) (N : I), Multiplicative.toAdd (κ b) N = 0 ↔
      (b : V ≃ₗ[ZMod 2] V) ∈ (N : Subgroup (V ≃ₗ[ZMod 2] V)))
    (g : ↥(Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q))
    (hbij : Set.BijOn (fun N : Subgroup (V ≃ₗ[ZMod 2] V) =>
      N.map (MulAut.conj (g : V ≃ₗ[ZMod 2] V)).toMonoidHom) (I : Set (Subgroup (V ≃ₗ[ZMod 2] V)))
        (I : Set (Subgroup (V ≃ₗ[ZMod 2] V)))) :
    IsSignedPerm ((conjMatrix κ (orthogonalGroup q) g : GL I (ZMod 3)) : Matrix I I (ZMod 3)) := by
  set g₀ : V ≃ₗ[ZMod 2] V := (g : V ≃ₗ[ZMod 2] V) with hg₀
  let π₀ : I → I := fun N => ⟨(N : Subgroup (V ≃ₗ[ZMod 2] V)).map (MulAut.conj g₀).toMonoidHom,
    hbij.mapsTo N.2⟩
  have hπinj : Function.Injective π₀ := fun N N' h =>
    Subtype.ext (hbij.injOn N.2 N'.2 (congrArg Subtype.val h))
  let π : Equiv.Perm I := Equiv.ofBijective π₀ (Finite.injective_iff_bijective.mp hπinj)
  have hπ : ∀ N, ((π N : I) : Subgroup (V ≃ₗ[ZMod 2] V)) =
      (N : Subgroup (V ≃ₗ[ZMod 2] V)).map (MulAut.conj g₀).toMonoidHom := fun N => rfl
  have hentry : ∀ i N : I,
      ((conjMatrix κ (orthogonalGroup q) g : GL I (ZMod 3)) : Matrix I I (ZMod 3)) i N = 0 ↔
        i ≠ π N := by
    intro i N
    rw [conjMatrix_val, LinearMap.toMatrix'_apply, coordLin_apply, hκ1, conjB_apply]
    set ε := κ.symm (Multiplicative.ofAdd (Pi.single N 1)) with hε
    have hεmem : ∀ N' : I, (ε : V ≃ₗ[ZMod 2] V) ∈ (N' : Subgroup (V ≃ₗ[ZMod 2] V)) ↔ N' ≠ N := by
      intro N'
      rw [← hκ1, hε, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      by_cases h : N' = N
      · subst h
        simp
      · simp [h]
    obtain ⟨N', rfl⟩ := π.surjective i
    rw [hπ, KernelBlockHyp.mem_map_conj_iff, show g₀⁻¹ * (g₀ * ε * g₀⁻¹) * g₀ = ε by group,
      hεmem, ne_eq, ne_eq, π.injective.eq_iff]
  refine ⟨π, fun N => ((conjMatrix κ (orthogonalGroup q) g : GL I (ZMod 3)) :
    Matrix I I (ZMod 3)) (π N) N, fun N h => (hentry (π N) N).mp h rfl, fun i N => ?_⟩
  split_ifs with h
  · rw [h]
  · exact (hentry i N).mpr h

end NormalizerImage

section Realize

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {B : Subgroup (V ≃ₗ[ZMod 2] V)}
  (hB : KernelBlockHyp q B) {I : Finset (Subgroup (V ≃ₗ[ZMod 2] V))}
  (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥)
  (c : I → V ≃ₗ[ZMod 2] V) (hc : ∀ N, c N ∈ B ∧ c N ∉ (N : Subgroup (V ≃ₗ[ZMod 2] V)))

attribute [local instance] KernelBlockHyp.finite_subgroup

omit [FiniteDimensional (ZMod 2) V] in
include hB hI hc in
theorem exists_block_power (N : I) (k : ZMod 3) (hk : k ≠ 0) :
    ∃ τ : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2]
        fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)),
      (∀ y, y + τ y + τ (τ y) = 0) ∧ (∀ y, τ y = y → y = 0) ∧
        ∀ y, (τ y : V) = (c N ^ k.val) y := by
  have hNB := ((hI N).1 N.2).1
  have hidx := ((hI N).1 N.2).2.1
  set σ := (blockGen (c N) N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2]
    fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) with hσ
  have hσ2 := blockGen_add_add hB hNB hidx (hc N).1 (hc N).2
  have hσfix := blockGen_fix hB hNB hidx (hc N).1 (hc N).2
  have hσapp : ∀ y, (σ y : V) = c N y := blockGen_apply_of_mem hB hNB (hc N).1
  have hσ3 := cube_apply_of_add_add hσ2
  have hσsq := sq_apply_of_add_add hσ2
  have key : k = 1 ∨ k = 2 := by revert k; decide
  rcases key with rfl | rfl
  · exact ⟨σ, hσ2, hσfix, fun y => by rw [hσapp]; rfl⟩
  · refine ⟨σ ∘ₗ σ, fun y => ?_, fun y hy => ?_, fun y => ?_⟩
    · change y + σ (σ y) + σ (σ (σ (σ y))) = 0
      rw [hσ3, hσsq]
      calc y + (y + σ y) + σ y = (y + y) + (σ y + σ y) := by abel
        _ = 0 := by rw [zmod2_vec_add_self, zmod2_vec_add_self, add_zero]
    · change σ (σ y) = y at hy
      apply hσfix
      calc σ y = σ (σ (σ y)) := by rw [hy]
        _ = y := hσ3 y
    · change (σ (σ y) : V) = (c N ^ (2 : ZMod 3).val) y
      rw [hσapp, hσapp, show (2 : ZMod 3).val = 2 from rfl, pow_two, LinearEquiv.mul_apply]

open _root_.Classical in
include hB hI hc in
theorem exists_conjMatrix_eq {κ : B ≃* Multiplicative (I → ZMod 3)}
    (hκ1 : ∀ (b : B) (N : I), Multiplicative.toAdd (κ b) N = 0 ↔
      (b : V ≃ₗ[ZMod 2] V) ∈ (N : Subgroup (V ≃ₗ[ZMod 2] V)))
    (hκ2 : ∀ N : I, Multiplicative.toAdd (κ ⟨c N, (hc N).1⟩) N = 1)
    (hκ3 : ∀ (b : B) (N : I) {x : V}, x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →
      (b : V ≃ₗ[ZMod 2] V) x = (c N ^ (Multiplicative.toAdd (κ b) N).val) x)
    (h2 : ∀ N : I, finrank (ZMod 2) (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = 2)
    (hnd : ∀ N : I, ∀ x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)),
      (∀ y ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)), polar q x y = 0) → x = 0)
    {M : Matrix I I (ZMod 3)} (hM : IsSignedPerm M) :
    ∃ g : ↥(Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q),
      ((conjMatrix κ (orthogonalGroup q) g : GL I (ZMod 3)) : Matrix I I (ZMod 3)) = M := by
  classical
  obtain ⟨π, ε, hε, hMe⟩ := hM
  have hNB : ∀ N : I, (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≤ B := fun N => ((hI N).1 N.2).1
  have hidx : ∀ N : I, (N : Subgroup (V ≃ₗ[ZMod 2] V)).relIndex B = 3 :=
    fun N => ((hI N).1 N.2).2.1
  choose τ hτ2 hτfix hτapp using fun N : I => exists_block_power hB hI c hc (π N) (ε N) (hε N)
  have hφ : ∀ N : I, ∃ φ : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≃ₗ[ZMod 2]
      fixedSub ((π N : I) : Subgroup (V ≃ₗ[ZMod 2] V)),
      ∀ y, φ ((blockGen (c N) N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2]
        fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) y) = τ N (φ y) := fun N =>
    exists_intertwining (h2 N) (h2 (π N)) (blockGen_add_add hB (hNB N) (hidx N) (hc N).1 (hc N).2)
      (blockGen_fix hB (hNB N) (hidx N) (hc N).1 (hc N).2) (hτ2 N) (hτfix N)
  choose φ hφ using hφ
  have hinj := blockSumPerm_injective hB hI π (fun N => (φ N).toLinearMap)
    (fun N => (φ N).injective)
  set g : V ≃ₗ[ZMod 2] V := LinearEquiv.ofInjectiveEndo _ hinj with hg
  have hgx : ∀ (N : I) (x : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))), g x = (φ N x : V) :=
    fun N x => blockSumPerm_apply_block hB hI π _ N x
  have hφq : ∀ (N : I) (x : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))), q (φ N x : V) = q x := by
    intro N x
    by_cases hx : x = 0
    · rw [hx, map_zero, Submodule.coe_zero, Submodule.coe_zero]
    · have hφx : (φ N x : V) ≠ 0 := fun h => hx ((φ N).map_eq_zero_iff.mp (Subtype.ext h))
      rw [q_eq_one_of_ne_zero hB (hNB (π N)) (hidx (π N)) (hc (π N)).1 (hc (π N)).2 (h2 (π N))
          (hnd (π N)) (φ N x).2 hφx,
        q_eq_one_of_ne_zero hB (hNB N) (hidx N) (hc N).1 (hc N).2 (h2 N) (hnd N) x.2
          fun h => hx (Subtype.ext h)]
  have hgO : g ∈ orthogonalGroup q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    exact blockSumPerm_isometry hB hI π _ hφq
  have hgmap : ∀ N : I, (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).map (g : V →ₗ[ZMod 2] V) =
      fixedSub ((π N : I) : Subgroup (V ≃ₗ[ZMod 2] V)) := by
    intro N
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [LinearEquiv.coe_coe, hgx N ⟨x, hx⟩]
      exact (φ N _).2
    · intro y hy
      refine ⟨((φ N).symm ⟨y, hy⟩ : V), ((φ N).symm ⟨y, hy⟩).2, ?_⟩
      rw [LinearEquiv.coe_coe, hgx N, LinearEquiv.apply_symm_apply]
  have hgN : g ∈ Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) :=
    mem_normalizer_of_perm hB hI c hc hκ3 h2 fun N hN => ⟨_, (π ⟨N, hN⟩).2, hgmap ⟨N, hN⟩⟩
  refine ⟨⟨g, Subgroup.mem_inf.mpr ⟨hgN, hgO⟩⟩, ?_⟩
  ext i N
  rw [conjMatrix_val, LinearMap.toMatrix'_apply, coordLin_apply, hMe]
  set e₀ := κ.symm (Multiplicative.ofAdd (Pi.single N (1 : ZMod 3))) with he₀
  have he₀κ : ∀ N', Multiplicative.toAdd (κ e₀) N' = (Pi.single N (1 : ZMod 3) : I → ZMod 3) N' :=
    fun N' => by
    rw [he₀, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  obtain ⟨N', rfl⟩ := π.surjective i
  have hginv : ∀ y : fixedSub ((π N' : I) : Subgroup (V ≃ₗ[ZMod 2] V)),
      g⁻¹ y = ((φ N').symm y : V) := fun y => by
    have h := hgx N' ((φ N').symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [← h, inv_apply_apply]
  by_cases hNN : N' = N
  · subst hNN
    rw [ite_eq_left_of_eq_true _ _ (eq_self _)]
    have hact : ∀ y ∈ fixedSub ((π N' : I) : Subgroup (V ≃ₗ[ZMod 2] V)),
        ((conjB g hgN e₀ : B) : V ≃ₗ[ZMod 2] V) y = (c (π N') ^ (ε N').val) y := by
      intro y hy
      rw [conjB_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        hginv ⟨y, hy⟩, hκ3 e₀ N' ((φ N').symm ⟨y, hy⟩).2, he₀κ, Pi.single_eq_same,
        show (1 : ZMod 3).val = 1 from rfl, pow_one,
        ← blockGen_apply_of_mem hB (hNB N') (hc N').1, hgx N', hφ, LinearEquiv.apply_symm_apply,
        hτapp]
    have h := coord_eq_of_block_action hB hI c hc hκ1 hκ2 (conjB g hgN e₀) (π N') _ hact
    rw [h, ZMod.natCast_zmod_val]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hNN (π.injective h))]
    have hact : ∀ y ∈ fixedSub ((π N' : I) : Subgroup (V ≃ₗ[ZMod 2] V)),
        ((conjB g hgN e₀ : B) : V ≃ₗ[ZMod 2] V) y = (c (π N') ^ 0) y := by
      intro y hy
      rw [conjB_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        hginv ⟨y, hy⟩, hκ3 e₀ N' ((φ N').symm ⟨y, hy⟩).2, he₀κ, Pi.single_eq_of_ne hNN,
        ZMod.val_zero, pow_zero]
      change g ((φ N').symm ⟨y, hy⟩ : V) = y
      rw [hgx, LinearEquiv.apply_symm_apply]
    have h := coord_eq_of_block_action hB hI c hc hκ1 hκ2 (conjB g hgN e₀) (π N') 0 hact
    rw [h, Nat.cast_zero]

end Realize

section Main

open _root_.Classical in
theorem binary_three_kernel_block_unitary_centralizers {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)
    (hb : (polarBilin q).Nondegenerate) {m : ℕ} (hV : finrank (ZMod 2) V = 2 * m)
    (B : Subgroup (V ≃ₗ[ZMod 2] V)) [IsElementaryAbelian 3 B] (hBO : B ≤ orthogonalGroup q)
    {r : ℕ} (hBcard : Nat.card B = 3 ^ r) (hfix : fixedSub B = ⊥)
    (I : Finset (Subgroup (V ≃ₗ[ZMod 2] V)))
    (hI : ∀ N, N ∈ I ↔ N ≤ B ∧ N.relIndex B = 3 ∧ fixedSub N ≠ ⊥)
    (c : I → V ≃ₗ[ZMod 2] V) (hc : ∀ N, c N ∈ B ∧ c N ∉ (N : Subgroup (V ≃ₗ[ZMod 2] V))) :
    ∃ (d : I → ℕ) (h3 : ∀ N : I, orderOf (blockGen (c N) N) = 3)
      (hfp : ∀ (N : I) (v : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
        (blockGen (c N) N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2]
          fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) v = v → v = 0),
      (∀ (N : I) (v : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
        ((blockGen (c N) N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2]
          fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) v : V) = c N v) ∧
      (∀ N : I, finrank (ZMod 2) (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = 2 * d N) ∧
      ∑ N : I, d N = m ∧
      (∀ N : I, letI := omegaModule (blockGen (c N) N) (h3 N) (hfp N)
        IsScalarTower (ZMod 2) OmegaField (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) ∧
        (∀ v, omega • v = (blockGen (c N) N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2]
          fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) v) ∧
        finrank OmegaField (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = d N ∧
        (∀ v w, omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
            (blockGen (c N) N) v w =
          algebraMap (ZMod 2) OmegaField (polar q v (c N w)) +
            omega * algebraMap (ZMod 2) OmegaField (polar q v w)) ∧
        (∀ v, (∀ w, omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
            (blockGen (c N) N) v w = 0) → v = 0) ∧
        (∀ (x : OmegaField) (v v' w : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
          omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
              (blockGen (c N) N) (x • v + v') w =
            x * omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
                (blockGen (c N) N) v w +
              omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
                (blockGen (c N) N) v' w) ∧
        (∀ (x : OmegaField) (v w w' : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
          omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
              (blockGen (c N) N) v (x • w + w') =
            x ^ 2 * omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
                (blockGen (c N) N) v w +
              omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
                (blockGen (c N) N) v w') ∧
        (∀ v w, omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
            (blockGen (c N) N) w v =
          omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
            (blockGen (c N) N) v w ^ 2) ∧
        ∀ v, omegaHerm (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
            (blockGen (c N) N) v v = algebraMap (ZMod 2) OmegaField (q v)) ∧
      Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ polarIsometryGroup q =
        Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q ∧
      (∃ e : ↥(Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q) ≃*
          ((N : I) → omegaUnitaryGroup
            (q.comp (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))).subtype)
            (blockGen (c N) N) (h3 N) (hfp N)),
        ∀ g (N : I) (v : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
          (((e g N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≃ₗ[ZMod 2]
            fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) v : fixedSub _) : V) =
              (g : V ≃ₗ[ZMod 2] V) v) ∧
      (I = ∅ → Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q = ⊥) ∧
      (m = r →
        I.card = r ∧ (∀ N : I, d N = 1) ∧
        (∀ N : I, finrank (ZMod 2) (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = 2 ∧
          ∀ x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)), q x = 0 → x = 0) ∧
        Subgroup.centralizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q = B ∧
        (∀ g ∈ orthogonalGroup q, g ∈ Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ↔
          ∀ N ∈ I, ∃ N' ∈ I, (fixedSub N).map (g : V →ₗ[ZMod 2] V) = fixedSub N') ∧
        ∃ κ : B ≃* Multiplicative (I → ZMod 3),
          (∀ (b : B) (N : I), Multiplicative.toAdd (κ b) N = 0 ↔
            (b : V ≃ₗ[ZMod 2] V) ∈ (N : Subgroup (V ≃ₗ[ZMod 2] V))) ∧
          (∀ N : I, Multiplicative.toAdd (κ ⟨c N, (hc N).1⟩) N = 1) ∧
          ∃ ψ : ↥(Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q) →*
              GL I (ZMod 3),
            (∀ (g : ↥(Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q))
                (b b' : B), (b' : V ≃ₗ[ZMod 2] V) =
                  (g : V ≃ₗ[ZMod 2] V) * b * (g : V ≃ₗ[ZMod 2] V)⁻¹ →
              Multiplicative.toAdd (κ b') =
                Matrix.mulVec (ψ g : Matrix I I (ZMod 3)) (Multiplicative.toAdd (κ b))) ∧
            ψ.ker = B.subgroupOf
              (Subgroup.normalizer (B : Set (V ≃ₗ[ZMod 2] V)) ⊓ orthogonalGroup q) ∧
            ∀ M : GL I (ZMod 3), M ∈ ψ.range ↔
              (∀ i, ∃! j, (M : Matrix I I (ZMod 3)) i j ≠ 0) ∧
              (∀ j, ∃! i, (M : Matrix I I (ZMod 3)) i j ≠ 0) ∧
              ∀ i j, (M : Matrix I I (ZMod 3)) i j = 0 ∨ (M : Matrix I I (ZMod 3)) i j = 1 ∨
                (M : Matrix I I (ZMod 3)) i j = -1) := by
  have hcube : ∀ g ∈ B, g ^ 3 = 1 := fun g hg => elemPow_eq_one_of_isElementaryAbelian g hg
  have hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : B) ⟨h, hh⟩)
  have hodd : ∀ N ≤ B, Odd (Nat.card N) := by
    intro N hNB
    have h1 : Nat.card N ∣ 3 ^ r := hBcard ▸ Subgroup.card_dvd_of_le hNB
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    rw [hj]
    exact Odd.pow (by decide)
  have hB : KernelBlockHyp q B := ⟨hcomm, hcube, hodd, hBO, hfix⟩
  obtain ⟨I', d', hI', ⟨-, hsup, -⟩, hblocks, hsum, hinf, -, -, -, -, -, -, hnorm, -, hmr⟩ :=
    binary_quadratic_three_action_canonical_kernel_blocks q hb hV B hBO hBcard hfix
  obtain rfl : I' = I := Finset.ext fun N => (hI' N).trans (hI N).symm
  have hNB : ∀ N : I', (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≤ B := fun N => ((hI N).1 N.2).1
  have hidx : ∀ N : I', (N : Subgroup (V ≃ₗ[ZMod 2] V)).relIndex B = 3 :=
    fun N => ((hI N).1 N.2).2.1
  have hN0 : ∀ N : I', fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) ≠ ⊥ :=
    fun N => ((hI N).1 N.2).2.2
  have h3 : ∀ N : I', orderOf (blockGen (c N) N) = 3 := fun N =>
    orderOf_blockGen hB (hNB N) (hidx N) (hN0 N) (hc N).1 (hc N).2
  have hfp : ∀ (N : I') (v : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))),
      (blockGen (c N) N : fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) →ₗ[ZMod 2]
        fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) v = v → v = 0 := fun N =>
    blockGen_fix hB (hNB N) (hidx N) (hc N).1 (hc N).2
  have hzQ := fun N : I' => blockGen_isometry hB (hNB N) (hc N).1
  have hz2 := fun N : I' => blockGen_add_add hB (hNB N) (hidx N) (hc N).1 (hc N).2
  have hnd : ∀ N : I', ∀ x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)),
      (∀ y ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)), polar q x y = 0) → x = 0 :=
    fun N => (hblocks N N.2).1
  refine ⟨fun N => d' N, h3, hfp, fun N v => blockGen_apply_of_mem hB (hNB N) (hc N).1 v,
    fun N => (hblocks N N.2).2.1, (Finset.sum_coe_sort I' d').trans hsum, fun N => ?_,
    centralizer_inf_polarIsometryGroup hB hI c hc,
    ⟨MulEquiv.ofBijective (centralizerToPi hB hI c hc h3 hfp)
      ⟨centralizerToPi_injective hB hI c hc h3 hfp, centralizerToPi_surjective hB hI c hc h3 hfp⟩,
      fun g N v => centralizerToPi_apply hB hI c hc h3 hfp N g v⟩, fun hI0 => ?_, fun hmr' => ?_⟩
  ·
    let _ := omegaModule (blockGen (c N) N) (h3 N) (hfp N)
    have hTower := omegaModule_isScalarTower (blockGen (c N) N) (h3 N) (hfp N)
    have hω := omegaModule_omega_smul (blockGen (c N) N) (h3 N) (hfp N)
    refine ⟨hTower, hω, ?_, fun v w => ?_, fun v hv => ?_,
      (omegaHerm_semilinear (hzQ N) (hz2 N)).1, (omegaHerm_semilinear (hzQ N) (hz2 N)).2,
      fun v w => omegaHerm_swap (hzQ N) (hz2 N) v w, fun v => ?_⟩
    · have h := (omega_semilinear_structure (blockGen (c N) N) (h3 N) hω).1
      rw [(hblocks N N.2).2.1] at h
      show Module.finrank OmegaField (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = d' N
      omega
    · unfold omegaHerm
      rw [polar_comp_subtype, polar_comp_subtype, blockGen_apply_of_mem hB (hNB N) (hc N).1]
    · apply Subtype.ext
      refine hnd N v v.2 fun y hy => ?_
      have h := polar_eq_zero_of_omegaHerm_eq_zero (hv ⟨y, hy⟩)
      rwa [polar_comp_subtype] at h
    · rw [omegaHerm_self (hzQ N) (hz2 N), QuadraticMap.comp_apply, Submodule.subtype_apply]
  ·
    rw [eq_bot_iff]
    intro g _
    rw [Subgroup.mem_bot]
    have htop : (⊤ : Submodule (ZMod 2) V) = ⊥ := by
      rw [← hsup, hI0]
      simp
    apply LinearEquiv.ext
    intro v
    have hv : v ∈ (⊥ : Submodule (ZMod 2) V) := htop ▸ Submodule.mem_top
    rw [(Submodule.mem_bot _).mp hv, map_zero]
    rfl
  ·
    obtain ⟨hIcard, hd1, -, -⟩ := hmr hmr'
    have hcard : Nat.card B = 3 ^ I'.card := by rw [hBcard, hIcard]
    have h2 : ∀ N : I', finrank (ZMod 2) (fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V))) = 2 :=
      fun N => by rw [(hblocks N N.2).2.1, hd1 N N.2]
    have hcen := centralizer_inf_orthogonalGroup_eq_of_two hB hI c hc hcard h2 h3 hfp
    obtain ⟨κ, hκ1, hκ2, hκ3⟩ := exists_coordEquiv hB hI c hc hcard hinf
    have haniso : ∀ N : I', ∀ x ∈ fixedSub (N : Subgroup (V ≃ₗ[ZMod 2] V)), q x = 0 → x = 0 := by
      intro N x hx hqx
      by_contra hx0
      have h1 := q_eq_one_of_ne_zero hB (hNB N) (hidx N) (hc N).1 (hc N).2 (h2 N) (hnd N) hx hx0
      rw [hqx] at h1
      exact zero_ne_one h1
    refine ⟨hIcard, fun N => hd1 N N.2, fun N => ⟨h2 N, haniso N⟩, hcen,
      fun g hgO => ⟨fun hgN N hN => ?_,
      fun hperm => mem_normalizer_of_perm hB hI c hc hκ3 h2 hperm⟩, κ, hκ1, hκ2,
      conjMatrix κ (orthogonalGroup q), fun g b b' hb => conjMatrix_mulVec κ _ g b b' hb, ?_,
      fun M => ?_⟩
    · obtain ⟨hbij, hfixmap⟩ := hnorm g hgO hgN
      exact ⟨N.map (MulAut.conj g).toMonoidHom, hbij.mapsTo hN, (hfixmap N hN).1.symm⟩
    · ext g
      rw [MonoidHom.mem_ker, conjMatrix_eq_one_iff, Subgroup.mem_subgroupOf]
      have hg := SetLike.ext_iff.mp hcen (g : V ≃ₗ[ZMod 2] V)
      exact ⟨fun h => hg.mp (Subgroup.mem_inf.mpr ⟨h, (Subgroup.mem_inf.mp g.2).2⟩),
        fun h => (Subgroup.mem_inf.mp (hg.mpr h)).1⟩
    · rw [← isSignedPerm_iff]
      constructor
      · rintro ⟨g, rfl⟩
        exact conjMatrix_isSignedPerm hκ1 g
          (hnorm g (Subgroup.mem_inf.mp g.2).2 (Subgroup.mem_inf.mp g.2).1).1
      · intro hM
        obtain ⟨g, hg⟩ := exists_conjMatrix_eq hB hI c hc hκ1 hκ2 hκ3 h2 hnd hM
        exact ⟨g, Units.ext hg⟩

end Main

end CFSG.RankThree.Classical.SteinbergBY
