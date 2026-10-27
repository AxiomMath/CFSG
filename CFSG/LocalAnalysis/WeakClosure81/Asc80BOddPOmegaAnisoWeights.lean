module

public import CFSG.LieType.SeitzGeneration.OrthHyperRad
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZeroMulti

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open QuadraticMap CFSG.LieType.SeitzGeneration CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
private lemma mem_wt {A B : Module.End K V} {s t : K} {v : V} :
    v ∈ (Module.End.eigenspace A s ⊓ Module.End.eigenspace B t) ↔
      A v = s • v ∧ B v = t • v := by
  simp only [Submodule.mem_inf, Module.End.mem_eigenspace_iff]

omit [Finite K] [FiniteDimensional K V] in
private lemma polar_map_of_map {Q : QuadraticForm K V} {X : V →ₗ[K] V}
    (hX : ∀ v, Q (X v) = Q v) (u v : V) : polar Q (X u) (X v) = polar Q u v := by
  rw [polar, polar, ← map_add, hX, hX, hX]

omit [Finite K] [FiniteDimensional K V] in
private lemma wq_apply_mem {A B : Module.End K V} (hA2 : ∀ v, A (A v) = v)
    (hB2 : ∀ v, B (B v) = v) (hAB : ∀ v, A (B v) = B (A v))
    {s t : K} (hsq : s * s = 1) (htq : t * t = 1) (v : V) :
    (1 + s • A + t • B + (s * t) • (A * B)) v ∈
      (Module.End.eigenspace A s ⊓ Module.End.eigenspace B t) := by
  have hst : (s * t) * (s * t) = 1 := by
    rw [mul_mul_mul_comm, hsq, htq, one_mul]
  rw [mem_wt]
  constructor
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.mul_apply, map_add, map_smul, smul_add, smul_smul]
    rw [hA2 v, hA2 (B v), hAB v]
    have hsst : s * (s * t) = t := by rw [← mul_assoc, hsq, one_mul]
    rw [hsq, hsst, one_smul]
    abel
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.mul_apply, map_add, map_smul, smul_add, smul_smul]
    rw [show B (A v) = A (B v) from (hAB v).symm, hB2 v,
      show B (A (B v)) = A (B (B v)) from (hAB (B v)).symm, hB2 v]
    have hts : t * s = s * t := mul_comm t s
    have htst : t * (s * t) = s := by rw [← mul_assoc, hts, mul_assoc, htq, mul_one]
    rw [hts, htst, htq, one_smul]
    abel

omit [Finite K] [FiniteDimensional K V] in
private lemma wq_sum_apply {A B : Module.End K V} (s : K) (v : V) :
    (1 + s • A + (1 : K) • B + (s * (1 : K)) • (A * B)) v +
    (1 + s • A + (-1 : K) • B + (s * (-1 : K)) • (A * B)) v +
    (1 + (-s) • A + (1 : K) • B + ((-s) * (1 : K)) • (A * B)) v +
    (1 + (-s) • A + (-1 : K) • B + ((-s) * (-1 : K)) • (A * B)) v = (4 : K) • v := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply, LinearMap.neg_apply, one_smul, neg_one_smul, mul_neg,
    mul_one, neg_neg]
  module

omit [Finite K] [FiniteDimensional K V] in
private lemma wq_apply_eq_zero_of_A_eigen {A B : Module.End K V}
    (hAB : ∀ v, A (B v) = B (A v)) {s u t : K} {x : V} (hx : A x = s • x)
    (hu : u * s = -1) :
    (1 + u • A + t • B + (u * t) • (A * B)) x = 0 := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply]
  have h1 : u • A x = (u * s) • x := by rw [hx, smul_smul]
  have h2 : (u * t) • (A (B x)) = ((u * t) * s) • B x := by
    rw [hAB x, hx, map_smul, smul_smul]
  rw [h1, h2, hu, neg_one_smul, add_neg_cancel, zero_add]
  have h3 : (u * t) * s = -t := by
    rw [show (u * t) * s = t * (u * s) by ring, hu]
    ring
  rw [h3, ← add_smul]
  simp


private lemma finrank_wt_le_two {Q : QuadraticForm K V} {A B : Module.End K V}
    (hanis : ∀ v, (A v = v ∨ A v = -v) → (B v = v ∨ B v = -v) → Q v = 0 → v = 0)
    {s t : K} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    Module.finrank K ↥(Module.End.eigenspace A s ⊓ Module.End.eigenspace B t) ≤ 2 := by
  set W : Submodule K V := Module.End.eigenspace A s ⊓ Module.End.eigenspace B t with hW
  by_contra hle
  have h3 : 3 ≤ Module.finrank K W := by omega
  have hlt : 2 * 1 < Module.finrank K W := by omega
  obtain ⟨x, hx0, hxQ⟩ :=
    CFSG.FiniteField.exists_ne_zero_forall_eq_zero_of_quadraticForm
      (fun _ : Fin 1 => Q.comp W.subtype) hlt
  have hQx : Q (x : V) = 0 := by
    have := hxQ 0
    simpa using this
  have hxmem : A (x : V) = s • (x : V) ∧ B (x : V) = t • (x : V) :=
    (mem_wt (A := A) (B := B) (s := s) (t := t)).1 (show (x : V) ∈ W by simp [hW])
  have hAx : A (x : V) = (x : V) ∨ A (x : V) = -(x : V) := by
    rcases hs with rfl | rfl
    · left; simpa using hxmem.1
    · right; simpa using hxmem.1
  have hBx : B (x : V) = (x : V) ∨ B (x : V) = -(x : V) := by
    rcases ht with rfl | rfl
    · left; simpa using hxmem.2
    · right; simpa using hxmem.2
  have hxz : (x : V) = 0 := hanis (x : V) hAx hBx hQx
  exact hx0 (Subtype.ext hxz)

omit [Finite K] in
private lemma finrank_le_sum_wt {A B : Module.End K V} (hA2 : ∀ v, A (A v) = v)
    (hB2 : ∀ v, B (B v) = v) (hAB : ∀ v, A (B v) = B (A v)) (h4 : (4 : K) ≠ 0) :
    Module.finrank K V ≤
      Module.finrank K ↥(Module.End.eigenspace A 1 ⊓ Module.End.eigenspace B 1) +
      Module.finrank K ↥(Module.End.eigenspace A 1 ⊓ Module.End.eigenspace B (-1)) +
      Module.finrank K ↥(Module.End.eigenspace A (-1) ⊓ Module.End.eigenspace B 1) +
      Module.finrank K ↥(Module.End.eigenspace A (-1) ⊓ Module.End.eigenspace B (-1)) := by
  classical
  let W11 : Submodule K V := Module.End.eigenspace A 1 ⊓ Module.End.eigenspace B 1
  let W1m : Submodule K V := Module.End.eigenspace A 1 ⊓ Module.End.eigenspace B (-1)
  let Wm1 : Submodule K V := Module.End.eigenspace A (-1) ⊓ Module.End.eigenspace B 1
  let Wmm : Submodule K V := Module.End.eigenspace A (-1) ⊓ Module.End.eigenspace B (-1)
  let p11 : V →ₗ[K] W11 :=
    (1 + (1 : K) • A + (1 : K) • B + ((1 : K) * (1 : K)) • (A * B)).codRestrict W11
      (fun v => by
        have h := wq_apply_mem (A := A) (B := B) hA2 hB2 hAB (s := 1) (t := 1)
          (by norm_num) (by norm_num) v
        simpa [W11] using h)
  let p1m : V →ₗ[K] W1m :=
    (1 + (1 : K) • A + (-1 : K) • B + ((1 : K) * (-1 : K)) • (A * B)).codRestrict W1m
      (fun v => by
        have h := wq_apply_mem (A := A) (B := B) hA2 hB2 hAB (s := 1) (t := -1)
          (by norm_num) (by norm_num) v
        simpa [W1m] using h)
  let pm1 : V →ₗ[K] Wm1 :=
    (1 + (-1 : K) • A + (1 : K) • B + ((-1 : K) * (1 : K)) • (A * B)).codRestrict Wm1
      (fun v => by
        have h := wq_apply_mem (A := A) (B := B) hA2 hB2 hAB (s := -1) (t := 1)
          (by norm_num) (by norm_num) v
        simpa [Wm1] using h)
  let pmm : V →ₗ[K] Wmm :=
    (1 + (-1 : K) • A + (-1 : K) • B + ((-1 : K) * (-1 : K)) • (A * B)).codRestrict Wmm
      (fun v => by
        have h := wq_apply_mem (A := A) (B := B) hA2 hB2 hAB (s := -1) (t := -1)
          (by norm_num) (by norm_num) v
        simpa [Wmm] using h)
  let f : V →ₗ[K] (W11 × W1m) × (Wm1 × Wmm) :=
    { toFun := fun v => ((p11 v, p1m v), (pm1 v, pmm v))
      map_add' := fun x y => by ext <;> simp [map_add]
      map_smul' := fun c x => by ext <;> simp [map_smul] }
  have hinj : Function.Injective f := by
    intro x y hxy
    have h0 : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h11 : (1 + (1 : K) • A + (1 : K) • B + ((1 : K) * (1 : K)) • (A * B)) (x - y) = 0 := by
      have h := congrArg (fun z : (W11 × W1m) × (Wm1 × Wmm) => ((z.1.1 : W11) : V)) h0
      have h1 : ((p11 (x - y) : W11) : V) = 0 := by simpa [f] using h
      simpa only [p11, LinearMap.codRestrict_apply] using h1
    have h1m : (1 + (1 : K) • A + (-1 : K) • B + ((1 : K) * (-1 : K)) • (A * B)) (x - y) = 0 := by
      have h := congrArg (fun z : (W11 × W1m) × (Wm1 × Wmm) => ((z.1.2 : W1m) : V)) h0
      have h1 : ((p1m (x - y) : W1m) : V) = 0 := by simpa [f] using h
      simpa only [p1m, LinearMap.codRestrict_apply] using h1
    have hm1 : (1 + (-1 : K) • A + (1 : K) • B + ((-1 : K) * (1 : K)) • (A * B)) (x - y) = 0 := by
      have h := congrArg (fun z : (W11 × W1m) × (Wm1 × Wmm) => ((z.2.1 : Wm1) : V)) h0
      have h1 : ((pm1 (x - y) : Wm1) : V) = 0 := by simpa [f] using h
      simpa only [pm1, LinearMap.codRestrict_apply] using h1
    have hmm : (1 + (-1 : K) • A + (-1 : K) • B + ((-1 : K) * (-1 : K)) • (A * B))
        (x - y) = 0 := by
      have h := congrArg (fun z : (W11 × W1m) × (Wm1 × Wmm) => ((z.2.2 : Wmm) : V)) h0
      have h1 : ((pmm (x - y) : Wmm) : V) = 0 := by simpa [f] using h
      simpa only [pmm, LinearMap.codRestrict_apply] using h1
    have hsum := wq_sum_apply (A := A) (B := B) (s := 1) (x - y)
    rw [h11, h1m, hm1, hmm] at hsum
    simp only [add_zero] at hsum
    have h4xy : (4 : K) • (x - y) = 0 := hsum.symm
    have hxy0 : x - y = 0 := by
      have h := congrArg (fun z : V => (4 : K)⁻¹ • z) h4xy
      rwa [smul_smul, inv_mul_cancel₀ h4, one_smul, smul_zero] at h
    exact sub_eq_zero.mp hxy0
  have hfr := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_prod] at hfr
  have hfr' : Module.finrank K V ≤
      Module.finrank K W11 + Module.finrank K W1m + Module.finrank K Wm1 +
        Module.finrank K Wmm := by omega
  simpa [W11, W1m, Wm1, Wmm] using hfr'

omit [Finite K] [FiniteDimensional K V] in
private lemma planes_of_two_weights {Q : QuadraticForm K V} {A B : Module.End K V}
    (h2 : (2 : K) ≠ 0) (hA2 : ∀ v, A (A v) = v) (hB2 : ∀ v, B (B v) = v)
    (hAQ : ∀ v, Q (A v) = Q v) (hBQ : ∀ v, Q (B v) = Q v)
    (hAB : ∀ v, A (B v) = B (A v))
    (hanis : ∀ v, (A v = v ∨ A v = -v) → (B v = v ∨ B v = -v) → Q v = 0 → v = 0)
    {s : K} (hs : s = 1 ∨ s = -1) :
    (∀ x ∈ Module.End.eigenspace A s ⊓ Module.End.eigenspace B 1, Q x = 0 → x = 0) ∧
    (∀ x ∈ Module.End.eigenspace A s ⊓ Module.End.eigenspace B (-1), Q x = 0 → x = 0) ∧
    (∀ x ∈ Module.End.eigenspace A s ⊓ Module.End.eigenspace B 1,
      ∀ y ∈ Module.End.eigenspace A s ⊓ Module.End.eigenspace B (-1), polar Q x y = 0) ∧
    (∀ x ∈ (Module.End.eigenspace A s ⊓ Module.End.eigenspace B 1) ⊔
        (Module.End.eigenspace A s ⊓ Module.End.eigenspace B (-1)), (-s) • A x = -x) ∧
    ∀ x ∈ qPerp Q ((Module.End.eigenspace A s ⊓ Module.End.eigenspace B 1) ⊔
        (Module.End.eigenspace A s ⊓ Module.End.eigenspace B (-1))), (-s) • A x = x := by
  classical
  have hsq : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have h4 : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  set W1 : Submodule K V := Module.End.eigenspace A s ⊓ Module.End.eigenspace B 1 with hW1
  set W2 : Submodule K V := Module.End.eigenspace A s ⊓ Module.End.eigenspace B (-1) with hW2
  set P : Submodule K V := W1 ⊔ W2 with hP
  have memW1 : ∀ x, x ∈ W1 ↔ A x = s • x ∧ B x = x := by
    intro x
    simp only [hW1, mem_wt, one_smul]
  have memW2 : ∀ x, x ∈ W2 ↔ A x = s • x ∧ B x = -x := by
    intro x
    simp only [hW2, mem_wt, neg_one_smul]
  have han1 : ∀ x ∈ W1, Q x = 0 → x = 0 := by
    intro x hx hQ
    have hx' := (memW1 x).1 hx
    refine hanis x ?_ ?_ hQ
    · rcases hs with rfl | rfl
      · left; simpa using hx'.1
      · right; simpa using hx'.1
    · left; exact hx'.2
  have han2 : ∀ x ∈ W2, Q x = 0 → x = 0 := by
    intro x hx hQ
    have hx' := (memW2 x).1 hx
    refine hanis x ?_ ?_ hQ
    · rcases hs with rfl | rfl
      · left; simpa using hx'.1
      · right; simpa using hx'.1
    · right; exact hx'.2
  have hBpol : ∀ u v, polar Q (B u) (B v) = polar Q u v := polar_map_of_map hBQ
  have horth : ∀ x ∈ W1, ∀ y ∈ W2, polar Q x y = 0 := by
    intro x hx y hy
    have hxB : B x = x := ((memW1 x).1 hx).2
    have hyB : B y = -y := ((memW2 y).1 hy).2
    have h := hBpol x y
    rw [hxB, hyB, polar_neg_right] at h
    have h2p : (2 : K) * polar Q x y = 0 := by
      rw [two_mul]
      nth_rewrite 1 [← h]
      exact neg_add_cancel _
    exact (mul_eq_zero.mp h2p).resolve_left h2
  let C : Module.End K V := (-s) • A
  have hss : (-s) * (-s) = 1 := by rw [neg_mul_neg, hsq]
  have hC2 : ∀ v, C (C v) = v := by
    intro v
    simp only [C, LinearMap.smul_apply, map_smul, smul_smul, hA2 v, hss, one_smul]
  have hCQ : ∀ v, Q (C v) = Q v := by
    intro v
    rw [show C v = (-s) • A v from rfl, map_smul_eq_sq, hAQ]
    rw [show (-s) ^ 2 = 1 by rw [pow_two, hss], one_mul]
  have hCneg : ∀ (t : K) {x : V},
      x ∈ (Module.End.eigenspace A s ⊓ Module.End.eigenspace B t) → C x = -x := by
    intro t x hx
    have hAx : A x = s • x := (mem_wt.1 hx).1
    rw [show C x = (-s) • A x from rfl, hAx, smul_smul]
    rw [show (-s) * s = -1 by rw [neg_mul, hsq], neg_one_smul]
  have hCcap : ∀ x ∈ P, C x = -x := by
    intro x hx
    have hxsup : x ∈ W1 ⊔ W2 := by simpa [hP] using hx
    rw [Submodule.mem_sup] at hxsup
    obtain ⟨x1, hx1, x2, hx2, rfl⟩ := hxsup
    rw [map_add, hCneg 1 (by simpa [hW1] using hx1), hCneg (-1) (by simpa [hW2] using hx2)]
    abel
  have hPnd : ∀ x ∈ P, (∀ y ∈ P, polar Q x y = 0) → x = 0 := by
    intro x hx hxperp
    have hxsup : x ∈ W1 ⊔ W2 := by simpa [hP] using hx
    rw [Submodule.mem_sup] at hxsup
    obtain ⟨x1, hx1, x2, hx2, rfl⟩ := hxsup
    have hx1z : x1 = 0 := by
      apply han1 x1 hx1
      have h := hxperp x1 (by rw [hP]; exact Submodule.mem_sup_left hx1)
      rw [polar_add_left, polar_comm Q x2 x1, horth x1 hx1 x2 hx2, add_zero] at h
      rw [polar_self_eq_two_mul] at h
      exact (mul_eq_zero.mp h).resolve_left h2
    rw [hx1z, zero_add] at hxperp ⊢
    have hx2z : x2 = 0 := by
      apply han2 x2 hx2
      have h := hxperp x2 (by rw [hP]; exact Submodule.mem_sup_right hx2)
      rw [polar_self_eq_two_mul] at h
      exact (mul_eq_zero.mp h).resolve_left h2
    exact hx2z
  have hker : LinearMap.ker (C + 1) = P := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hx
      have hCx : C x = -x := by
        rw [eq_neg_iff_add_eq_zero]
        exact hx
      have hAx : A x = s • x := by
        have h2' : ((-s) * (-s)) • A x = ((-s) * (-1)) • x := by
          have h := congrArg (fun y => (-s) • y) hCx
          rw [show C x = (-s) • A x from rfl, smul_smul] at h
          rwa [show (-s) • (-x) = ((-s) * (-1)) • x by
            rw [show -x = (-1 : K) • x by rw [neg_one_smul], smul_smul]] at h
        rw [hss, show (-s) * (-1) = s by ring, one_smul] at h2'
        exact h2'
      have hsum := wq_sum_apply (A := A) (B := B) (s := s) x
      have hz1 : (1 + (-s) • A + (1 : K) • B + ((-s) * (1 : K)) • (A * B)) x = 0 :=
        wq_apply_eq_zero_of_A_eigen (A := A) (B := B) hAB (u := -s) (t := 1) hAx (by
          rw [neg_mul, hsq])
      have hz2 : (1 + (-s) • A + (-1 : K) • B + ((-s) * (-1 : K)) • (A * B)) x = 0 :=
        wq_apply_eq_zero_of_A_eigen (A := A) (B := B) hAB (u := -s) (t := -1) hAx (by
          rw [neg_mul, hsq])
      rw [hz1, hz2, add_zero, add_zero] at hsum
      have hxsplit : x = (4 : K)⁻¹ •
          ((1 + s • A + (1 : K) • B + (s * (1 : K)) • (A * B)) x +
           (1 + s • A + (-1 : K) • B + (s * (-1 : K)) • (A * B)) x) := by
        calc x = (4 : K)⁻¹ • ((4 : K) • x) := by rw [smul_smul, inv_mul_cancel₀ h4, one_smul]
          _ = (4 : K)⁻¹ • ((1 + s • A + (1 : K) • B + (s * (1 : K)) • (A * B)) x +
              (1 + s • A + (-1 : K) • B + (s * (-1 : K)) • (A * B)) x) := by
                rw [← hsum]
      rw [hxsplit, smul_add]
      exact P.add_mem
        (Submodule.mem_sup_left (W1.smul_mem _ (by
          have := wq_apply_mem (A := A) (B := B) hA2 hB2 hAB (s := s) (t := 1) hsq
            (by norm_num) x
          simpa [hW1] using this)))
        (Submodule.mem_sup_right (W2.smul_mem _ (by
          have := wq_apply_mem (A := A) (B := B) hA2 hB2 hAB (s := s) (t := -1) hsq
            (by norm_num) x
          simpa [hW2] using this)))
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, hCcap x hx]
      exact neg_add_cancel x
  have hCperp : ∀ x ∈ qPerp Q P, C x ∈ qPerp Q P := by
    intro x hx
    rw [mem_qPerp] at hx ⊢
    intro y hy
    rw [polar_comm Q y (C x)]
    have hyC : C y = -y := hCcap y hy
    have hxy : polar Q x y = 0 := by
      rw [polar_comm]
      exact hx y hy
    have h := polar_map_of_map hCQ x y
    rw [hyC, hxy, polar_neg_right, neg_eq_zero] at h
    exact h
  have hfinal : ∀ x ∈ qPerp Q P, C x = x := by
    intro x hx
    have hyperp : x - C x ∈ qPerp Q P := (qPerp Q P).sub_mem hx (hCperp x hx)
    have hyC : C (x - C x) = -(x - C x) := by
      rw [map_sub, hC2 x]
      abel
    have hyP : x - C x ∈ P := by
      rw [← hker, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, hyC]
      exact neg_add_cancel _
    have hy0 : x - C x = 0 := by
      apply hPnd (x - C x) hyP
      intro z hz
      rw [polar_comm]
      exact (mem_qPerp.1 hyperp) z hz
    have hCx : C x = x := (sub_eq_zero.mp hy0).symm
    exact hCx
  refine ⟨han1, han2, horth, ?_, ?_⟩
  · simpa [C] using hCcap
  · simpa [C] using hfinal

theorem exists_aniso_planes_of_commuting_involutions {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0)
    (hd7 : 7 ≤ Module.finrank K V) (hd8 : Module.finrank K V ≤ 8) {A B : V →ₗ[K] V}
    (hA2 : ∀ v, A (A v) = v) (hB2 : ∀ v, B (B v) = v) (hAQ : ∀ v, Q (A v) = Q v)
    (hBQ : ∀ v, Q (B v) = Q v) (hAB : ∀ v, A (B v) = B (A v))
    (hanis : ∀ v, (A v = v ∨ A v = -v) → (B v = v ∨ B v = -v) → Q v = 0 → v = 0) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∃ P₁ P₂ : Submodule K V, Module.finrank K P₁ = 2 ∧
      Module.finrank K P₂ = 2 ∧ (∀ x ∈ P₁, Q x = 0 → x = 0) ∧ (∀ x ∈ P₂, Q x = 0 → x = 0) ∧
      (∀ x ∈ P₁, ∀ y ∈ P₂, polar Q x y = 0) ∧ (∀ x ∈ P₁ ⊔ P₂, ε • A x = -x) ∧
      ∀ x ∈ qPerp Q (P₁ ⊔ P₂), ε • A x = x := by
  classical
  have h4 : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h2
  have hle := finrank_le_sum_wt (A := A) (B := B) hA2 hB2 hAB h4
  set d11 : ℕ := Module.finrank K ↥(Module.End.eigenspace A 1 ⊓ Module.End.eigenspace B 1)
    with hd11
  set d1m : ℕ := Module.finrank K ↥(Module.End.eigenspace A 1 ⊓ Module.End.eigenspace B (-1))
    with hd1m
  set dm1 : ℕ := Module.finrank K ↥(Module.End.eigenspace A (-1) ⊓ Module.End.eigenspace B 1)
    with hdm1
  set dmm : ℕ := Module.finrank K ↥(Module.End.eigenspace A (-1) ⊓ Module.End.eigenspace B (-1))
    with hdmm
  have hd : Module.finrank K V ≤ d11 + d1m + dm1 + dmm := by
    simpa [hd11, hd1m, hdm1, hdmm] using hle
  have h11 : d11 ≤ 2 := by
    have h := finrank_wt_le_two (Q := Q) (A := A) (B := B) hanis
      (s := 1) (t := 1) (Or.inl rfl) (Or.inl rfl)
    simpa [hd11] using h
  have h1m : d1m ≤ 2 := by
    have h := finrank_wt_le_two (Q := Q) (A := A) (B := B) hanis
      (s := 1) (t := -1) (Or.inl rfl) (Or.inr rfl)
    simpa [hd1m] using h
  have hm1 : dm1 ≤ 2 := by
    have h := finrank_wt_le_two (Q := Q) (A := A) (B := B) hanis
      (s := -1) (t := 1) (Or.inr rfl) (Or.inl rfl)
    simpa [hdm1] using h
  have hmm : dmm ≤ 2 := by
    have h := finrank_wt_le_two (Q := Q) (A := A) (B := B) hanis
      (s := -1) (t := -1) (Or.inr rfl) (Or.inr rfl)
    simpa [hdmm] using h
  have hpair : (dm1 = 2 ∧ dmm = 2) ∨ (d11 = 2 ∧ d1m = 2) := by
    rcases Nat.lt_or_ge dm1 2 with h | h
    · right; omega
    rcases Nat.lt_or_ge dmm 2 with h' | h'
    · right; omega
    left; omega
  rcases hpair with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
  · have hmain := planes_of_two_weights (Q := Q) (A := A) (B := B) h2 hA2 hB2 hAQ hBQ hAB
      hanis (s := -1) (Or.inr rfl)
    refine ⟨1, Or.inl rfl, ?_⟩
    refine ⟨Module.End.eigenspace A (-1) ⊓ Module.End.eigenspace B 1,
      Module.End.eigenspace A (-1) ⊓ Module.End.eigenspace B (-1), ?_, ?_,
      hmain.1, hmain.2.1, hmain.2.2.1, ?_, ?_⟩
    · simpa [hdm1] using h1
    · simpa [hdmm] using h2'
    · simpa using hmain.2.2.2.1
    · simpa using hmain.2.2.2.2
  · have hmain := planes_of_two_weights (Q := Q) (A := A) (B := B) h2 hA2 hB2 hAQ hBQ hAB
      hanis (s := 1) (Or.inl rfl)
    refine ⟨-1, Or.inr rfl, ?_⟩
    refine ⟨Module.End.eigenspace A 1 ⊓ Module.End.eigenspace B 1,
      Module.End.eigenspace A 1 ⊓ Module.End.eigenspace B (-1), ?_, ?_,
      hmain.1, hmain.2.1, hmain.2.2.1, ?_, ?_⟩
    · simpa [hd11] using h1
    · simpa [hd1m] using h2'
    · simpa using hmain.2.2.2.1
    · simpa using hmain.2.2.2.2

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
