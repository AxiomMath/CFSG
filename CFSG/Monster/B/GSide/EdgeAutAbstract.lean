module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open scoped commutatorElement

section Form

variable {N : Type*} [Group N] {xh : N} (hxh2 : xh * xh = 1) (hxhZ : xh ∈ Subgroup.center N)
  (hc : ∀ u v : N, ⁅u, v⁆ = 1 ∨ ⁅u, v⁆ = xh)
include hxhZ hc

theorem commutatorElement_mem_center (u v : N) : ⁅u, v⁆ ∈ Subgroup.center N := by
  rcases hc u v with h | h <;> rw [h]
  · exact Subgroup.one_mem _
  · exact hxhZ

theorem commutatorElement_mul_left' (u u' v : N) : ⁅u * u', v⁆ = ⁅u', v⁆ * ⁅u, v⁆ := by
  have h := Subgroup.mem_center_iff.1 (commutatorElement_mem_center hxhZ hc u' v) u
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def] at *
  calc u * u' * v * (u * u')⁻¹ * v⁻¹ = u * (u' * v * u'⁻¹ * v⁻¹) * u⁻¹ * (u * v * u⁻¹ * v⁻¹) := by
        group
    _ = u' * v * u'⁻¹ * v⁻¹ * (u * v * u⁻¹ * v⁻¹) := by rw [h, mul_inv_cancel_right]

theorem commutatorElement_mul_right' (u v v' : N) : ⁅u, v * v'⁆ = ⁅u, v⁆ * ⁅u, v'⁆ := by
  have h := Subgroup.mem_center_iff.1 (commutatorElement_mem_center hxhZ hc u v') v
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def] at *
  calc u * (v * v') * u⁻¹ * (v * v')⁻¹ = u * v * u⁻¹ * v⁻¹ * (v * (u * v' * u⁻¹ * v'⁻¹) * v⁻¹) := by
        group
    _ = u * v * u⁻¹ * v⁻¹ * (u * v' * u⁻¹ * v'⁻¹) := by rw [h, mul_inv_cancel_right]

end Form

section Duality

variable {N : Type*} [Group N] {xh : N}

open scoped _root_.Classical in
@[expose] def ind (g : N) : ZMod 2 := if g = 1 then 0 else 1

theorem ind_eq_zero_iff {g : N} : ind g = 0 ↔ g = 1 := by
  classical
  unfold ind
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun e => absurd e (by decide), fun e => absurd e h⟩

theorem ind_mul (hxh2 : xh * xh = 1) (hxh1 : xh ≠ 1) {a b : N} (ha : a = 1 ∨ a = xh)
    (hb : b = 1 ∨ b = xh) : ind (a * b) = ind a + ind b := by
  classical
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [ind, hxh2, hxh1]
  decide

variable (hxh2 : xh * xh = 1) (hxh1 : xh ≠ 1) (hxhZ : xh ∈ Subgroup.center N)
  (hc : ∀ u v : N, ⁅u, v⁆ = 1 ∨ ⁅u, v⁆ = xh)
include hxh2 hxh1 hxhZ hc

theorem ind_commutatorElement_mul_left (u u' v : N) :
    ind ⁅u * u', v⁆ = ind ⁅u, v⁆ + ind ⁅u', v⁆ := by
  rw [commutatorElement_mul_left' hxhZ hc, ind_mul hxh2 hxh1 (hc u' v) (hc u v), add_comm]

theorem ind_commutatorElement_mul_right (u v v' : N) :
    ind ⁅u, v * v'⁆ = ind ⁅u, v⁆ + ind ⁅u, v'⁆ := by
  rw [commutatorElement_mul_right' hxhZ hc, ind_mul hxh2 hxh1 (hc u v) (hc u v')]

omit hxh2 hxh1 hxhZ hc in
theorem commutatorElement_eq_one_of_mem_center_left {z : N} (hz : z ∈ Subgroup.center N)
    (v : N) : ⁅z, v⁆ = 1 := by
  rw [commutatorElement_def, (Subgroup.mem_center_iff.1 hz v).symm]
  group

omit hxh2 hxh1 hxhZ hc in
theorem commutatorElement_eq_one_of_mem_center_right {z : N} (hz : z ∈ Subgroup.center N)
    (u : N) : ⁅u, z⁆ = 1 := by
  rw [commutatorElement_def, (Subgroup.mem_center_iff.1 hz u)]
  group

theorem ind_commutatorElement_eq_of_left {u u' : N} (h : u⁻¹ * u' ∈ Subgroup.center N) (v : N) :
    ind ⁅u', v⁆ = ind ⁅u, v⁆ := by
  have e : u' = u * (u⁻¹ * u') := by group
  rw [e, ind_commutatorElement_mul_left hxh2 hxh1 hxhZ hc,
    commutatorElement_eq_one_of_mem_center_left h, ind_eq_zero_iff.2 rfl, add_zero]

theorem ind_commutatorElement_eq_of_right {v v' : N} (h : v⁻¹ * v' ∈ Subgroup.center N) (u : N) :
    ind ⁅u, v'⁆ = ind ⁅u, v⁆ := by
  have e : v' = v * (v⁻¹ * v') := by group
  rw [e, ind_commutatorElement_mul_right hxh2 hxh1 hxhZ hc,
    commutatorElement_eq_one_of_mem_center_right h, ind_eq_zero_iff.2 rfl, add_zero]

omit hxh2 hxh1 hxhZ hc in
theorem commutatorElement_comm_eq_one_iff (u v : N) : ⁅u, v⁆ = 1 ↔ ⁅v, u⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute, commutatorElement_eq_one_iff_commute]
  exact ⟨Commute.symm, Commute.symm⟩

theorem exists_eq_commutatorElement [Finite N] (hsq : ∀ n : N, n * n ∈ Subgroup.center N)
    (ζ : N →* N) (hζ : ∀ n, ζ n = 1 ∨ ζ n = xh) (hζZ : ∀ z ∈ Subgroup.center N, ζ z = 1) :
    ∃ v : N, ∀ n, ζ n = ⁅n, v⁆ := by
  classical
  have hcommQ : ∀ a b : N ⧸ Subgroup.center N, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := commutatorElement_mem_center hxhZ hc b⁻¹ a⁻¹
    rw [commutatorElement_def, inv_inv, inv_inv] at h
    rwa [mul_inv_rev, ← mul_assoc]
  let _ : CommGroup (N ⧸ Subgroup.center N) :=
    { (inferInstance : Group (N ⧸ Subgroup.center N)) with mul_comm := hcommQ }
  let _ : AddCommGroup (Additive (N ⧸ Subgroup.center N)) := Additive.addCommGroup
  have h2 : ∀ x : Additive (N ⧸ Subgroup.center N), (2 : ℕ) • x = 0 := by
    intro x
    induction x using Additive.rec with
    | ofMul q =>
    induction q using QuotientGroup.induction_on with
    | H a =>
    rw [two_nsmul, ← ofMul_mul, ← QuotientGroup.mk_mul, ← ofMul_one]
    congr 1
    exact (QuotientGroup.eq_one_iff _).2 (hsq a)
  let _ : Module (ZMod 2) (Additive (N ⧸ Subgroup.center N)) := AddCommGroup.zmodModule h2
  have hrep : ∀ a : N, (QuotientGroup.mk a : N ⧸ Subgroup.center N).out⁻¹ * a ∈
      Subgroup.center N := fun a => QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  have hrepmul : ∀ x y : N ⧸ Subgroup.center N, (x * y).out⁻¹ * (x.out * y.out) ∈
      Subgroup.center N := fun x y => QuotientGroup.eq.1 (by
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq',
      QuotientGroup.out_eq'])
  let f : Additive (N ⧸ Subgroup.center N) → Additive (N ⧸ Subgroup.center N) → ZMod 2 :=
    fun x y => ind ⁅(Additive.toMul x).out, (Additive.toMul y).out⁆
  have hf : ∀ u v : N, f (Additive.ofMul (u : N ⧸ Subgroup.center N))
      (Additive.ofMul (v : N ⧸ Subgroup.center N)) = ind ⁅u, v⁆ := fun u v => by
    change ind ⁅(u : N ⧸ Subgroup.center N).out, (v : N ⧸ Subgroup.center N).out⁆ = _
    rw [← ind_commutatorElement_eq_of_left hxh2 hxh1 hxhZ hc (hrep u),
      ← ind_commutatorElement_eq_of_right hxh2 hxh1 hxhZ hc (hrep v)]
  have hfl : ∀ x x' y, f (x + x') y = f x y + f x' y := fun x x' y => by
    change ind ⁅(Additive.toMul x * Additive.toMul x').out, _⁆ = _
    rw [← ind_commutatorElement_eq_of_left hxh2 hxh1 hxhZ hc (hrepmul _ _),
      ind_commutatorElement_mul_left hxh2 hxh1 hxhZ hc]
  have hfr : ∀ x y y', f x (y + y') = f x y + f x y' := fun x y y' => by
    change ind ⁅_, (Additive.toMul y * Additive.toMul y').out⁆ = _
    rw [← ind_commutatorElement_eq_of_right hxh2 hxh1 hxhZ hc (hrepmul _ _),
      ind_commutatorElement_mul_right hxh2 hxh1 hxhZ hc]
  let Bx : Additive (N ⧸ Subgroup.center N) →
      (Additive (N ⧸ Subgroup.center N) →ₗ[ZMod 2] ZMod 2) :=
    fun x => (AddMonoidHom.mk' (f x) (hfr x)).toZModLinearMap 2
  let B : LinearMap.BilinForm (ZMod 2) (Additive (N ⧸ Subgroup.center N)) :=
    (AddMonoidHom.mk' Bx fun x x' => LinearMap.ext fun y => hfl x x' y).toZModLinearMap 2
  have hB : ∀ x y, B x y = f x y := fun _ _ => rfl
  have hrad : ∀ a : N, (∀ u : N, ind ⁅a, u⁆ = 0) →
      Additive.ofMul (a : N ⧸ Subgroup.center N) = 0 := fun a ha => by
    have hcen : a ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro u
      have h := ha u
      rw [ind_eq_zero_iff, commutatorElement_eq_one_iff_commute] at h
      exact h.symm.eq
    rw [← ofMul_one]
    exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff a).2 hcen)
  have hnd : B.Nondegenerate := by
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · induction m using Additive.rec with
      | ofMul q =>
      induction q using QuotientGroup.induction_on with
      | H a =>
      refine hrad a fun u => ?_
      have h := hm (Additive.ofMul (u : N ⧸ Subgroup.center N))
      rwa [hB, hf] at h
    · induction m using Additive.rec with
      | ofMul q =>
      induction q using QuotientGroup.induction_on with
      | H a =>
      refine hrad a fun u => ?_
      have h := hm (Additive.ofMul (u : N ⧸ Subgroup.center N))
      rw [hB, hf, ind_eq_zero_iff, commutatorElement_comm_eq_one_iff] at h
      exact ind_eq_zero_iff.2 h
  have hζrep : ∀ a : N, ζ (QuotientGroup.mk a : N ⧸ Subgroup.center N).out = ζ a := fun a => by
    have h := hζZ _ (hrep a)
    rw [map_mul, map_inv, inv_mul_eq_one] at h
    exact h
  let g : Additive (N ⧸ Subgroup.center N) → ZMod 2 := fun x => ind (ζ (Additive.toMul x).out)
  have hg : ∀ x x', g (x + x') = g x + g x' := fun x x' => by
    change ind (ζ (Additive.toMul x * Additive.toMul x').out) = _
    have h := hζZ _ (hrepmul (Additive.toMul x) (Additive.toMul x'))
    rw [map_mul, map_inv, inv_mul_eq_one] at h
    rw [h, map_mul, ind_mul hxh2 hxh1 (hζ _) (hζ _)]
  obtain ⟨w, hw⟩ := (LinearMap.BilinForm.toDual (K := ZMod 2)
    (V := Additive (N ⧸ Subgroup.center N)) B hnd).surjective
    ((AddMonoidHom.mk' g hg).toZModLinearMap 2)
  refine ⟨(Additive.toMul w).out, fun n => ?_⟩
  have h1 : f w (Additive.ofMul (n : N ⧸ Subgroup.center N)) =
      g (Additive.ofMul (n : N ⧸ Subgroup.center N)) := by
    have h := congrArg (fun φ => φ (Additive.ofMul (n : N ⧸ Subgroup.center N))) hw
    exact h
  change ind ⁅(Additive.toMul w).out, (n : N ⧸ Subgroup.center N).out⁆ =
    ind (ζ (n : N ⧸ Subgroup.center N).out) at h1
  rw [← ind_commutatorElement_eq_of_right hxh2 hxh1 hxhZ hc (hrep n), hζrep] at h1
  have key : ζ n = 1 ↔ ⁅n, (Additive.toMul w).out⁆ = 1 := by
    rw [commutatorElement_comm_eq_one_iff, ← ind_eq_zero_iff, ← ind_eq_zero_iff, h1]
  rcases hζ n with h | h <;> rcases hc n (Additive.toMul w).out with h' | h'
  · rw [h, h']
  · exact absurd (key.1 h) (by rw [h']; exact hxh1)
  · exact absurd (key.2 h') (by rw [h]; exact hxh1)
  · rw [h, h']

end Duality

section Main

variable {A : Type*} [Group A]

theorem mulAut_mem_center {G : Type*} [Group G] (φ : MulAut G) {z : G}
    (hz : z ∈ Subgroup.center G) : φ z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  rw [← MulAut.apply_inv_self _ φ y, ← map_mul, ← map_mul, hz]

@[expose] def conjQuot (N : Subgroup A) [N.Normal] (a : A) :
    N ⧸ Subgroup.center N →* N ⧸ Subgroup.center N :=
  QuotientGroup.map (Subgroup.center N) (Subgroup.center N) (MulAut.conjNormal a).toMonoidHom
    fun _ hz => mulAut_mem_center (MulAut.conjNormal a) hz

theorem conjQuot_mk (N : Subgroup A) [N.Normal] (a : A) (n : N) :
    conjQuot N a (n : N ⧸ Subgroup.center N) =
      ((MulAut.conjNormal a n : N) : N ⧸ Subgroup.center N) :=
  QuotientGroup.map_mk _ _ _ _ n

theorem mulAut_eq_inner_mul_central [Finite A] (N : Subgroup A) [N.Normal]
    (hchar : ∀ τ : MulAut A, ∀ n ∈ N, τ n ∈ N)
    (hZ : ∀ z : N, z ∈ Subgroup.center N → ∀ a : A, a * z = z * a)
    {xh : A} (hxh2 : xh * xh = 1) (hxh1 : xh ≠ 1) (hcomm : ⁅N, N⁆ = Subgroup.zpowers xh)
    (hsq : ∀ n : N, n * n ∈ Subgroup.center N) (hNA : ⁅N, ⊤⁆ = N)
    (hEnd : ∀ ψ : N ⧸ Subgroup.center N →* N ⧸ Subgroup.center N,
      (∀ a : A, ψ.comp (conjQuot N a) = (conjQuot N a).comp ψ) → ψ = 1 ∨ ψ = MonoidHom.id _)
    (hout : ∀ σ : MulAut (A ⧸ N), ∃ g, σ = MulAut.conj g)
    (τ : MulAut A) (hτ : ∀ z : N, z ∈ Subgroup.center N → τ z = z) :
    ∃ (g : A) (μ : A →* A), (∀ x, ∃ z : N, z ∈ Subgroup.center N ∧ μ x = z) ∧
      (∀ x ∈ N, μ x = 1) ∧ ∀ x, τ x = g * x * g⁻¹ * μ x := by
  classical
  have hxhN : xh ∈ N := Subgroup.commutator_le_left N N (hcomm ▸ Subgroup.mem_zpowers xh)
  have hord : orderOf xh = 2 := orderOf_eq_prime (by rw [sq, hxh2]) hxh1
  have hzp : ∀ y ∈ Subgroup.zpowers xh, y = 1 ∨ y = xh := by
    rintro y ⟨k, rfl⟩
    change xh ^ k = 1 ∨ xh ^ k = xh
    rw [← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]
  have hc : ∀ u ∈ N, ∀ v ∈ N, ⁅u, v⁆ = 1 ∨ ⁅u, v⁆ = xh := fun u hu v hv =>
    hzp _ (hcomm ▸ Subgroup.commutator_mem_commutator hu hv)
  have hxhZN : (⟨xh, hxhN⟩ : N) ∈ Subgroup.center N := by
    rw [Subgroup.mem_center_iff]
    intro n
    have h1 : (n : A) * xh * (n : A)⁻¹ ∈ ⁅N, N⁆ :=
      (Subgroup.commutator_normal N N).conj_mem _ (hcomm ▸ Subgroup.mem_zpowers xh) n
    rcases hzp _ (hcomm ▸ h1) with h | h
    · exact absurd (by simpa using h) hxh1
    · exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact
        (eq_mul_inv_iff_mul_eq.1 h.symm).symm)
  have hxhA : ∀ a : A, a * xh = xh * a := hZ _ hxhZN
  have hZA : ∀ z : A, z ∈ (Subgroup.center N).map N.subtype → ∀ a : A, a * z = z * a := by
    rintro _ ⟨z, hz, rfl⟩ a
    exact hZ z hz a
  have hxhc : ∀ y, (y = 1 ∨ y = xh) → ∀ a : A, a * y = y * a := by
    rintro y (rfl | rfl) a
    · rw [one_mul, mul_one]
    · exact hxhA a
  have hmemZ : ∀ w : N, ((w : A) = 1 ∨ (w : A) = xh) → w ∈ Subgroup.center N := by
    rintro w (h | h)
    · rw [show w = 1 from Subtype.ext h]
      exact Subgroup.one_mem _
    · rw [show w = ⟨xh, hxhN⟩ from Subtype.ext h]
      exact hxhZN
  have hmapN : ∀ σ : MulAut A, N.map (σ : A →* A) = N := fun σ => by
    refine le_antisymm ?_ fun n hn => ⟨σ⁻¹ n, hchar σ⁻¹ n hn, MulAut.apply_inv_self _ σ n⟩
    rintro _ ⟨n, hn, rfl⟩
    exact hchar σ n hn
  obtain ⟨gq, hgq⟩ := hout (QuotientGroup.congr N N τ (hmapN τ))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gq
  set τ₁ : MulAut A := (MulAut.conj g)⁻¹ * τ with hτ₁
  have hτ₁x : ∀ x, τ₁ x = g⁻¹ * τ x * g := fun _ => rfl
  have hm : ∀ x : A, x⁻¹ * τ₁ x ∈ N := by
    intro x
    have h := congrArg (fun σ : MulAut (A ⧸ N) => σ (x : A ⧸ N)) hgq
    simp only [QuotientGroup.congr_mk, MulAut.conj_apply] at h
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq] at h
    have h' := (inferInstance : N.Normal).conj_mem _ (N.inv_mem h) g⁻¹
    rw [hτ₁x]
    convert h' using 1
    group
  have hτ₁N : ∀ n ∈ N, τ₁ n ∈ N := fun n hn => hchar τ₁ n hn
  have hτ₁Z : ∀ z : N, z ∈ Subgroup.center N → τ₁ z = z := fun z hz => by
    rw [hτ₁x, hτ z hz, hZ z hz g⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  let τN : N →* N := (τ₁.toMonoidHom.comp N.subtype).codRestrict N fun n => hτ₁N n n.2
  have hτN : ∀ n : N, (τN n : A) = τ₁ n := fun _ => rfl
  have hτNZ : ∀ z ∈ Subgroup.center N, τN z = z := fun z hz => Subtype.ext (hτ₁Z z hz)
  let ψ : N ⧸ Subgroup.center N →* N ⧸ Subgroup.center N :=
    QuotientGroup.map _ _ τN fun z hz => by
      rw [Subgroup.mem_comap, hτNZ z hz]
      exact hz
  have hψ : ∀ a : A, ψ.comp (conjQuot N a) = (conjQuot N a).comp ψ := by
    intro a
    refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun n => ?_)
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    change ((τN (MulAut.conjNormal a n) : N) : N ⧸ Subgroup.center N) =
      ((MulAut.conjNormal a (τN n) : N) : N ⧸ Subgroup.center N)
    rw [QuotientGroup.eq]
    have hma := hm a
    set m := a⁻¹ * τ₁ a with hmdef
    have hτa : τ₁ a = a * m := by rw [hmdef]; group
    apply hmemZ
    have hk := hc m hma ((τ₁ n)⁻¹) (N.inv_mem (hτ₁N n n.2))
    have e : (((τN (MulAut.conjNormal a n))⁻¹ * MulAut.conjNormal a (τN n) : N) : A) =
        ⁅m, (τ₁ n)⁻¹⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hτN, MulAut.conjNormal_apply,
        MulAut.conjNormal_apply, hτN, map_mul, map_mul, map_inv, hτa]
      have hcent := hxhc _ hk a
      rw [commutatorElement_def] at hcent ⊢
      calc (a * m * τ₁ ↑n * (a * m)⁻¹)⁻¹ * (a * τ₁ ↑n * a⁻¹)
          = a * (m * (τ₁ ↑n)⁻¹ * m⁻¹ * (τ₁ ↑n)⁻¹⁻¹) * a⁻¹ := by group
        _ = m * (τ₁ ↑n)⁻¹ * m⁻¹ * (τ₁ ↑n)⁻¹⁻¹ := by rw [hcent, mul_inv_cancel_right]
    rw [e]
    exact hk
  have hψid : ψ = MonoidHom.id _ := by
    rcases hEnd ψ hψ with h | h
    · exfalso
      have hall : ∀ n : N, n ∈ Subgroup.center N := by
        intro n
        have hn' : (⟨τ₁⁻¹ n, hchar τ₁⁻¹ n n.2⟩ : N) = ⟨τ₁⁻¹ n, hchar τ₁⁻¹ n n.2⟩ := rfl
        have h1 := congrArg (fun φ : N ⧸ Subgroup.center N →* N ⧸ Subgroup.center N =>
          φ ((⟨τ₁⁻¹ n, hchar τ₁⁻¹ n n.2⟩ : N) : N ⧸ Subgroup.center N)) h
        simp only [MonoidHom.one_apply] at h1
        have h2 : τN ⟨τ₁⁻¹ n, hchar τ₁⁻¹ n n.2⟩ = n :=
          Subtype.ext (MulAut.apply_inv_self _ τ₁ n)
        change ((τN ⟨τ₁⁻¹ n, hchar τ₁⁻¹ n n.2⟩ : N) : N ⧸ Subgroup.center N) = 1 at h1
        rw [h2, QuotientGroup.eq_one_iff] at h1
        exact h1
      have hbot : ⁅N, N⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro u hu v hv
        have h1 := Subgroup.mem_center_iff.1 (hall ⟨v, hv⟩) ⟨u, hu⟩
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact congrArg Subtype.val h1
      have h3 : xh ∈ ⁅N, N⁆ := hcomm ▸ Subgroup.mem_zpowers xh
      rw [hbot, Subgroup.mem_bot] at h3
      exact hxh1 h3
    · exact h
  have hζZ' : ∀ n : N, n⁻¹ * τN n ∈ Subgroup.center N := by
    intro n
    have h1 := congrArg (fun φ : N ⧸ Subgroup.center N →* N ⧸ Subgroup.center N =>
      φ (n : N ⧸ Subgroup.center N)) hψid
    change ((τN n : N) : N ⧸ Subgroup.center N) = (n : N ⧸ Subgroup.center N) at h1
    rw [QuotientGroup.eq] at h1
    have h2 := (Subgroup.center N).inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2
  have hζA : ∀ n : N, ∀ a : A, a * ((n : A)⁻¹ * τ₁ n) = ((n : A)⁻¹ * τ₁ n) * a := fun n a =>
    hZ ⟨_, N.mul_mem (N.inv_mem n.2) (hτ₁N n n.2)⟩ (hζZ' n) a
  let ζ : N →* N :=
    { toFun := fun n => n⁻¹ * τN n
      map_one' := by rw [map_one, inv_one, one_mul]
      map_mul' := fun n n' => Subtype.ext (by
        change ((n * n' : N) : A)⁻¹ * τ₁ (n * n' : N) =
          ((n : A)⁻¹ * τ₁ n) * ((n' : A)⁻¹ * τ₁ n')
        rw [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc (n' : A)⁻¹ * (n : A)⁻¹ * (τ₁ n * τ₁ n')
            = (n' : A)⁻¹ * ((n : A)⁻¹ * τ₁ n) * τ₁ n' := by group
          _ = (n : A)⁻¹ * τ₁ n * (n' : A)⁻¹ * τ₁ n' := by rw [hζA n]
          _ = _ := by group) }
  have hζ : ∀ n : N, (ζ n : A) = (n : A)⁻¹ * τ₁ n := fun _ => rfl
  have hζZ : ∀ z ∈ Subgroup.center N, ζ z = 1 := fun z hz => Subtype.ext (by
    rw [hζ, hτ₁Z z hz, inv_mul_cancel]
    rfl)
  have hζconj : ∀ (n : N) (a : A) (h : a * n * a⁻¹ ∈ N),
      (ζ ⟨a * n * a⁻¹, h⟩ : A) = ⁅(n : A)⁻¹, a⁻¹ * τ₁ a⁆ * ζ n := by
    intro n a h
    set m := a⁻¹ * τ₁ a with hmdef
    have hτa : τ₁ a = a * m := by rw [hmdef]; group
    have hk := hc _ (N.inv_mem n.2) m (hm a)
    have hcent := hxhc _ hk a
    rw [hζ, hζ, map_mul, map_mul, map_inv, hτa, commutatorElement_def]
    rw [commutatorElement_def] at hcent
    have e1 : τ₁ n = n * ((n : A)⁻¹ * τ₁ n) := by group
    set ζn := (n : A)⁻¹ * τ₁ n with hζn
    have e1 : τ₁ n = n * ζn := by rw [hζn]; group
    calc (a * n * a⁻¹)⁻¹ * (a * m * τ₁ n * (a * m)⁻¹)
        = a * ((n : A)⁻¹ * m * (n * ζn) * m⁻¹) * a⁻¹ := by rw [e1]; group
      _ = a * ((n : A)⁻¹ * m * n * (ζn * m⁻¹)) * a⁻¹ := by group
      _ = a * ((n : A)⁻¹ * m * n * (m⁻¹ * ζn)) * a⁻¹ := by rw [← hζA n m⁻¹]
      _ = a * ((n : A)⁻¹ * m * (n : A)⁻¹⁻¹ * m⁻¹) * (ζn * a⁻¹) := by rw [inv_inv]; group
      _ = a * ((n : A)⁻¹ * m * (n : A)⁻¹⁻¹ * m⁻¹) * (a⁻¹ * ζn) := by rw [← hζA n a⁻¹]
      _ = a * ((n : A)⁻¹ * m * (n : A)⁻¹⁻¹ * m⁻¹) * a⁻¹ * ζn := by group
      _ = (n : A)⁻¹ * m * (n : A)⁻¹⁻¹ * m⁻¹ * ζn := by rw [hcent, mul_inv_cancel_right]
  have hζx : ∀ n : N, (ζ n : A) = 1 ∨ (ζ n : A) = xh := by
    let K : Subgroup A := ((Subgroup.zpowers (⟨xh, hxhN⟩ : N)).comap ζ).map N.subtype
    have hK : ⁅N, ⊤⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro n hn a _
      have hc1 : a * n⁻¹ * a⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem _ (N.inv_mem hn) a
      have hcm' : ⁅n, a⁆ = n * (a * n⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
      have hcm : ⁅n, a⁆ ∈ N := by
        rw [hcm']
        exact N.mul_mem hn hc1
      refine ⟨⟨_, hcm⟩, ?_, rfl⟩
      have e : (⟨⁅n, a⁆, hcm⟩ : N) = ⟨n, hn⟩ * ⟨a * n⁻¹ * a⁻¹, hc1⟩ := Subtype.ext hcm'
      have h2 := hζconj ⟨n⁻¹, N.inv_mem hn⟩ a hc1
      have hk := hc _ (N.inv_mem (N.inv_mem hn)) _ (hm a)
      rw [SetLike.mem_coe, Subgroup.mem_comap, e, map_mul]
      have h3 : (ζ ⟨n, hn⟩ * ζ ⟨a * n⁻¹ * a⁻¹, hc1⟩ : N) =
          ⟨⁅(n⁻¹ : A)⁻¹, a⁻¹ * τ₁ a⁆, by
            rcases hk with h | h <;> rw [h]
            · exact N.one_mem
            · exact hxhN⟩ := by
        refine Subtype.ext ?_
        rw [Subgroup.coe_mul, h2]
        have hinv : (ζ ⟨n⁻¹, N.inv_mem hn⟩ : N) = (ζ ⟨n, hn⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [hinv, Subgroup.coe_inv]
        have hcz := hζA ⟨n, hn⟩ ⁅(n⁻¹ : A)⁻¹, a⁻¹ * τ₁ a⁆
        rw [← hζ] at hcz
        calc (ζ ⟨n, hn⟩ : A) * (⁅(n⁻¹ : A)⁻¹, a⁻¹ * τ₁ a⁆ * (ζ ⟨n, hn⟩ : A)⁻¹)
            = ⁅(n⁻¹ : A)⁻¹, a⁻¹ * τ₁ a⁆ * (ζ ⟨n, hn⟩ : A) * (ζ ⟨n, hn⟩ : A)⁻¹ := by
              rw [← mul_assoc, ← hcz]
          _ = _ := mul_inv_cancel_right _ _
      rw [h3]
      rcases hk with h | h
      · have : (⟨⁅(n⁻¹ : A)⁻¹, a⁻¹ * τ₁ a⁆, by rw [h]; exact N.one_mem⟩ : N) = 1 :=
          Subtype.ext h
        rw [this]
        exact Subgroup.one_mem _
      · have : (⟨⁅(n⁻¹ : A)⁻¹, a⁻¹ * τ₁ a⁆, by rw [h]; exact hxhN⟩ : N) = ⟨xh, hxhN⟩ :=
          Subtype.ext h
        rw [this]
        exact Subgroup.mem_zpowers _
    intro n
    obtain ⟨n', hn', e⟩ := (hNA ▸ hK) n.2
    obtain rfl : n' = n := Subtype.ext e
    rw [SetLike.mem_coe, Subgroup.mem_comap] at hn'
    obtain ⟨k, hk⟩ := hn'
    have hk' : (ζ n' : A) = xh ^ k := by
      rw [← hk, Subgroup.coe_zpow]
    exact hzp _ ⟨k, hk'.symm⟩
  have hxh2' : (⟨xh, hxhN⟩ : N) * ⟨xh, hxhN⟩ = 1 := Subtype.ext hxh2
  have hxh1' : (⟨xh, hxhN⟩ : N) ≠ 1 := fun h => hxh1 (congrArg Subtype.val h)
  have hc' : ∀ u v : N, ⁅u, v⁆ = 1 ∨ ⁅u, v⁆ = ⟨xh, hxhN⟩ := fun u v => by
    rcases hc u u.2 v v.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hζ' : ∀ n, ζ n = 1 ∨ ζ n = ⟨xh, hxhN⟩ := fun n => by
    rcases hζx n with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  obtain ⟨v, hv⟩ := exists_eq_commutatorElement hxh2' hxh1' hxhZN hc' hsq ζ hζ' hζZ
  have hτ₁v : ∀ n ∈ N, τ₁ n = v * n * (v : A)⁻¹ := by
    intro n hn
    have h1 : (n : A)⁻¹ * τ₁ n = ⁅n, (v : A)⁆ := congrArg Subtype.val (hv ⟨n, hn⟩)
    have hsq' : (v : A) * (n * n) = n * n * v :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 (hsq ⟨n, hn⟩) v)
    calc τ₁ n = n * ((n : A)⁻¹ * τ₁ n) := by group
      _ = n * n * v * n⁻¹ * (v : A)⁻¹ := by rw [h1, commutatorElement_def]; group
      _ = v * (n * n) * n⁻¹ * (v : A)⁻¹ := by rw [hsq']
      _ = v * n * (v : A)⁻¹ := by group
  set τ₂ : MulAut A := (MulAut.conj (v : A))⁻¹ * τ₁ with hτ₂
  have hτ₂x : ∀ x, τ₂ x = (v : A)⁻¹ * τ₁ x * v := fun _ => rfl
  have hτ₂N : ∀ n ∈ N, τ₂ n = n := fun n hn => by rw [hτ₂x, hτ₁v n hn]; group
  have hμN : ∀ x : A, x⁻¹ * τ₂ x ∈ N := by
    intro x
    have h1 : x⁻¹ * (v : A)⁻¹ * x ∈ N := by
      have h := (inferInstance : N.Normal).conj_mem _ (N.inv_mem v.2) x⁻¹
      rwa [inv_inv] at h
    have e : x⁻¹ * τ₂ x = (x⁻¹ * (v : A)⁻¹ * x) * (x⁻¹ * τ₁ x) * v := by rw [hτ₂x]; group
    rw [e]
    exact N.mul_mem (N.mul_mem h1 (hm x)) v.2
  have hμZ : ∀ x : A, (⟨x⁻¹ * τ₂ x, hμN x⟩ : N) ∈ Subgroup.center N := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    have hy : x * n * x⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem _ n.2 x
    have h1 := hτ₂N _ hy
    rw [map_mul, map_mul, map_inv, hτ₂N n n.2] at h1
    change (n : A) * (x⁻¹ * τ₂ x) = x⁻¹ * τ₂ x * n
    calc (n : A) * (x⁻¹ * τ₂ x) = x⁻¹ * (x * n * x⁻¹) * τ₂ x := by group
      _ = x⁻¹ * (τ₂ x * n * (τ₂ x)⁻¹) * τ₂ x := by rw [h1]
      _ = x⁻¹ * τ₂ x * n := by group
  have hμA : ∀ x a : A, a * (x⁻¹ * τ₂ x) = (x⁻¹ * τ₂ x) * a := fun x a => hZ _ (hμZ x) a
  let μ : A →* A :=
    { toFun := fun x => x⁻¹ * τ₂ x
      map_one' := by rw [map_one, inv_one, one_mul]
      map_mul' := fun x y => by
        rw [map_mul, mul_inv_rev]
        calc y⁻¹ * x⁻¹ * (τ₂ x * τ₂ y) = y⁻¹ * (x⁻¹ * τ₂ x) * τ₂ y := by group
          _ = (x⁻¹ * τ₂ x) * y⁻¹ * τ₂ y := by rw [hμA x y⁻¹]
          _ = _ := by group }
  refine ⟨g * v, μ, fun x => ⟨⟨_, hμN x⟩, hμZ x, rfl⟩, fun x hx => ?_, fun x => ?_⟩
  · change x⁻¹ * τ₂ x = 1
    rw [hτ₂N x hx, inv_mul_cancel]
  · change τ x = g * v * x * (g * v)⁻¹ * (x⁻¹ * τ₂ x)
    have e1 : τ x = g * τ₁ x * g⁻¹ := by rw [hτ₁x]; group
    have e2 : τ₁ x = v * τ₂ x * (v : A)⁻¹ := by rw [hτ₂x]; group
    rw [e1, e2]
    calc g * (↑v * τ₂ x * (↑v)⁻¹) * g⁻¹
        = g * ↑v * x * ((x⁻¹ * τ₂ x) * ((↑v)⁻¹ * g⁻¹)) := by group
      _ = g * ↑v * x * (((↑v)⁻¹ * g⁻¹) * (x⁻¹ * τ₂ x)) := by rw [← hμA x ((v : A)⁻¹ * g⁻¹)]
      _ = _ := by group

theorem commutator_le_ker_of_central (μ : A →* A) (hμ : ∀ x a : A, a * μ x = μ x * a) :
    commutator A ≤ μ.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
    ← hμ a (μ b)]
  group

open scoped _root_.Classical in
theorem mulAut_eq_inner_mul_beta [Finite A] (N : Subgroup A) [N.Normal]
    (hchar : ∀ τ : MulAut A, ∀ n ∈ N, τ n ∈ N)
    (hZ : ∀ z : N, z ∈ Subgroup.center N → ∀ a : A, a * z = z * a)
    {xh : A} (hxh2 : xh * xh = 1) (hxh1 : xh ≠ 1) (hcomm : ⁅N, N⁆ = Subgroup.zpowers xh)
    (hsq : ∀ n : N, n * n ∈ Subgroup.center N) (hNA : ⁅N, ⊤⁆ = N)
    (hEnd : ∀ ψ : N ⧸ Subgroup.center N →* N ⧸ Subgroup.center N,
      (∀ a : A, ψ.comp (conjQuot N a) = (conjQuot N a).comp ψ) → ψ = 1 ∨ ψ = MonoidHom.id _)
    (hout : ∀ σ : MulAut (A ⧸ N), ∃ g, σ = MulAut.conj g) (hidx : (commutator A).index = 2)
    (τ : MulAut A) (hτ : ∀ z : N, z ∈ Subgroup.center N → τ z = z) :
    ∃ (g : A) (w : A), (∃ z : N, z ∈ Subgroup.center N ∧ (z : A) = w) ∧
      ∀ x, τ x = g * (x * (if x ∈ commutator A then 1 else w)) * g⁻¹ := by
  obtain ⟨g, μ, hμZ, -, hτμ⟩ := mulAut_eq_inner_mul_central N hchar hZ hxh2 hxh1 hcomm hsq hNA
    hEnd hout τ hτ
  have hμc : ∀ x a : A, a * μ x = μ x * a := fun x a => by
    obtain ⟨z, hz, e⟩ := hμZ x
    rw [e]
    exact hZ z hz a
  have hker := commutator_le_ker_of_central μ hμc
  obtain ⟨s, hs⟩ : ∃ s, s ∉ commutator A := by
    by_contra h
    push Not at h
    have htop : commutator A = ⊤ := eq_top_iff.2 fun x _ => h x
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  refine ⟨g, μ s, hμZ s |>.imp fun z hz => ⟨hz.1, hz.2.symm⟩, fun x => ?_⟩
  have hμx : μ x = if x ∈ commutator A then 1 else μ s := by
    split_ifs with hx
    · exact hker hx
    · have h1 : x * s⁻¹ ∈ commutator A := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        exact iff_of_false hx fun h => hs (by simpa using (commutator A).inv_mem h)
      have h2 := hker h1
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h2
      exact h2
  rw [hτμ x, ← hμx]
  calc g * x * g⁻¹ * μ x = g * x * (g⁻¹ * μ x) := by group
    _ = g * x * (μ x * g⁻¹) := by rw [hμc x g⁻¹]
    _ = g * (x * μ x) * g⁻¹ := by group

open scoped _root_.Classical in
theorem exists_beta_mulEquiv (hidx : (commutator A).index = 2) {w : A}
    (hw : ∀ a : A, a * w = w * a) (hw2 : w * w = 1) (hwA : w ∈ commutator A) :
    ∃ β : MulAut A, ∀ x, β x = x * (if x ∈ commutator A then 1 else w) := by
  let f : A → A := fun x => x * (if x ∈ commutator A then 1 else w)
  have hmem : ∀ x, x * (if x ∈ commutator A then 1 else w) ∈ commutator A ↔
      x ∈ commutator A := fun x => by
    split_ifs
    · rw [mul_one]
    · exact (commutator A).mul_mem_cancel_right hwA
  have hff : ∀ x, f (f x) = x := fun x => by
    simp only [f, hmem]
    split_ifs <;> simp [mul_assoc, hw2]
  have hfmul : ∀ x y, f (x * y) = f x * f y := fun x y => by
    simp only [f]
    by_cases hx : x ∈ commutator A <;> by_cases hy : y ∈ commutator A
    · rw [ite_eq_left ((commutator A).mul_mem hx hy), ite_eq_left hx, ite_eq_left hy]
      group
    · rw [ite_eq_right (fun h => hy (((commutator A).mul_mem_cancel_left hx).1 h)),
        ite_eq_left hx, ite_eq_right hy]
      group
    · rw [ite_eq_right (fun h => hx (((commutator A).mul_mem_cancel_right hy).1 h)),
        ite_eq_right hx, ite_eq_left hy]
      calc x * y * w = x * (y * w) := mul_assoc _ _ _
        _ = x * (w * y) := by rw [hw y]
        _ = x * w * (y * 1) := by group
    · rw [ite_eq_left ((Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false hx hy)),
        ite_eq_right hx, ite_eq_right hy]
      calc x * y * 1 = x * (y * (w * w)) := by rw [hw2]; group
        _ = x * (y * w * w) := by group
        _ = x * (w * y * w) := by rw [hw y]
        _ = x * w * (y * w) := by group
  exact ⟨{ toFun := f
           invFun := f
           left_inv := hff
           right_inv := hff
           map_mul' := hfmul }, fun _ => rfl⟩

end Main

end CFSG.Monster.B.GSide
