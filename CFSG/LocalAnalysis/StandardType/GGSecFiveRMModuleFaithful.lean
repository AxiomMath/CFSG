module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank

public section

open scoped BigOperators

namespace CFSG.StandardType

section Module

private def linDiff
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (g : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V :=
  g.toLinearMap - LinearMap.id

private lemma linDiff_apply
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (g : V ≃ₗ[ZMod p] V) (v : V) : linDiff g v = g v - v := rfl

private lemma linDiff_one
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    : linDiff (1 : V ≃ₗ[ZMod p] V) = 0 := by
  ext v; simp [linDiff]

private def linFix
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (U : Submodule (ZMod p) V) : Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {g | ∀ u ∈ U, g u = u}
  one_mem' := by intro u _; simp
  mul_mem' := by
    intro g h hg hh u hu
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [LinearEquiv.mul_apply, hh u hu, hg u hu]
  inv_mem' := by
    intro g hg u hu
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h := hg u hu
    calc g⁻¹ u = g⁻¹ (g u) := by rw [h]
      _ = u := by simp

private def Nsub
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (U : Submodule (ZMod p) V) :
    Subgroup (V ≃ₗ[ZMod p] V) :=
  A ⊓ linFix U

private lemma mem_Nsub
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {A : Subgroup (V ≃ₗ[ZMod p] V)} {U : Submodule (ZMod p) V}
    {g : V ≃ₗ[ZMod p] V} : g ∈ Nsub A U ↔ g ∈ A ∧ ∀ u ∈ U, g u = u :=
  Subgroup.mem_inf

private lemma linDiff_mul
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (htriv : ∀ g ∈ A, ∀ v, g v - v ∈ U)
    {h k : V ≃ₗ[ZMod p] V} (hh : h ∈ Nsub A U) (hk : k ∈ Nsub A U) :
    linDiff (h * k) = linDiff h + linDiff k := by
  obtain ⟨hhA, hhU⟩ := (mem_Nsub.mp hh)
  obtain ⟨hkA, hkU⟩ := (mem_Nsub.mp hk)
  ext v
  have hmem : k v - v ∈ U := htriv k hkA v
  have hfix : h (k v - v) = k v - v := hhU (k v - v) hmem
  have h2 : h (k v) - h v = k v - v := by rw [← map_sub, hfix]
  simp only [linDiff_apply, LinearEquiv.mul_apply]
  rw [(sub_eq_iff_eq_add).mp h2]
  simp only [LinearMap.add_apply, linDiff_apply]
  abel

private lemma linDiff_pow
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (htriv : ∀ g ∈ A, ∀ v, g v - v ∈ U)
    {h : V ≃ₗ[ZMod p] V} (hh : h ∈ Nsub A U) (n : ℕ) :
    linDiff (h ^ n) = n • linDiff h := by
  induction n with
  | zero => simp [linDiff_one]
  | succ n ih =>
    rw [pow_succ, linDiff_mul htriv ((Nsub A U).pow_mem hh n) hh, ih, add_smul, one_smul]

private lemma exists_linDiff_of_mem_span
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V}
    {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (htriv : ∀ g ∈ A, ∀ v, g v - v ∈ U)
    (φ : V →ₗ[ZMod p] V)
    (hφ : φ ∈ Submodule.span (ZMod p) (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V)))) :
    ∃ h ∈ Nsub A U, linDiff h = φ := by
  refine Submodule.span_induction (p := fun φ _ => ∃ h ∈ Nsub A U, linDiff h = φ) ?_ ?_ ?_ ?_ hφ
  · rintro x ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · exact ⟨1, (Nsub A U).one_mem, linDiff_one⟩
  · rintro x y _ _ ⟨h, hh, rfl⟩ ⟨k, hk, rfl⟩
    exact ⟨h * k, (Nsub A U).mul_mem hh hk, linDiff_mul htriv hh hk⟩
  · rintro c x _ ⟨h, hh, rfl⟩
    refine ⟨h ^ c.val, (Nsub A U).pow_mem hh c.val, ?_⟩
    rw [linDiff_pow htriv hh c.val, ← Nat.cast_smul_eq_nsmul (ZMod p) c.val (linDiff h),
      ZMod.natCast_zmod_val]

private lemma exists_functionals
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {f : V →ₗ[ZMod p] V} {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod p) (LinearMap.range f)) :
    ∃ ξ : Fin m → (V →ₗ[ZMod p] ZMod p),
      (∀ (i : Fin m) (v : V),
        ξ i v = b.repr (f.codRestrict (LinearMap.range f)
          (fun c => LinearMap.mem_range_self f c) v) i) ∧
      f = ∑ i, (ξ i).smulRight ((b i : LinearMap.range f) : V) := by
  classical
  let coords : V →ₗ[ZMod p] (Fin m →₀ ZMod p) :=
    b.repr.comp (f.codRestrict (LinearMap.range f)
      (fun v => LinearMap.mem_range_self f v))
  let ξ : Fin m → (V →ₗ[ZMod p] ZMod p) := fun i => (Finsupp.lapply i).comp coords
  refine ⟨ξ, fun i v => rfl, ?_⟩
  ext v
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hsum : ∑ i, (b.repr ⟨f v, LinearMap.mem_range_self f v⟩) i • (b i : V) =
      f v := by
    have h := b.sum_repr ⟨f v, LinearMap.mem_range_self f v⟩
    have h2 := congrArg (Submodule.subtype (LinearMap.range f)) h
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using h2
  rw [← hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ξ, coords, LinearMap.comp_apply, Finsupp.lapply_apply]
  rfl

private lemma functionals_kill_U
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {f : V →ₗ[ZMod p] V} {m : ℕ}
    {b : Module.Basis (Fin m) (ZMod p) (LinearMap.range f)}
    {ξ : Fin m → (V →ₗ[ZMod p] ZMod p)}
    (hξ_coords : ∀ (i : Fin m) (v : V),
      ξ i v = b.repr (f.codRestrict (LinearMap.range f)
        (fun c => LinearMap.mem_range_self f c) v) i)
    (hker : ∀ u ∈ U, f u = 0) :
    ∀ i, ∀ u ∈ U, ξ i u = 0 := by
  intro i u hu
  have hfu : f u = 0 := hker u hu
  have hcoords : f.codRestrict (LinearMap.range f)
      (fun c => LinearMap.mem_range_self f c) u = 0 := by
    apply Subtype.ext
    exact hfu
  rw [hξ_coords, hcoords, map_zero]
  simp

private lemma exists_Phi
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {f : V →ₗ[ZMod p] V} {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod p) (LinearMap.range f))
    (ξ : Fin m → (V →ₗ[ZMod p] ZMod p))
    (hdecomp : f = ∑ i, (ξ i).smulRight ((b i : LinearMap.range f) : V))
    (hle : LinearMap.range f ≤ U) :
    ∃ (Φ : (Fin m → U) →ₗ[ZMod p] (V →ₗ[ZMod p] V)) (xf : Fin m → U),
      (∀ (x : Fin m → U) (v : V), Φ x v = ∑ i, ξ i v • ((x i : U) : V)) ∧
      Φ xf = f ∧ (∀ i, ((xf i : U) : V) = (b i : V)) := by
  classical
  let u : Fin m → V := fun i => (b i : V)
  let Φ : (Fin m → U) →ₗ[ZMod p] (V →ₗ[ZMod p] V) :=
    { toFun := fun x => ∑ i, (ξ i).smulRight ((x i : U) : V)
      map_add' := by
        intro x y
        ext v
        simp only [Pi.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
          LinearMap.add_apply, Submodule.coe_add, smul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext v
        simp only [Pi.smul_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
          LinearMap.smul_apply, Submodule.coe_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [RingHom.id_apply, smul_smul, smul_smul, mul_comm] }
  have hΦ_apply : ∀ (x : Fin m → U) (v : V),
      Φ x v = ∑ i, ξ i v • ((x i : U) : V) := by
    intro x v
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
      LinearMap.smulRight_apply]
  let xf : Fin m → U := fun i => ⟨u i, hle (b i).2⟩
  refine ⟨Φ, xf, hΦ_apply, ?_, fun i => rfl⟩
  rw [hdecomp]
  simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((xf i : U) : V) = u i from rfl]

private lemma Phi_eq_zero_of_zero_coord
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V]
    {U : Submodule (ZMod p) V} {M : Submodule (ZMod p) (V →ₗ[ZMod p] V)}
    {m : ℕ} (hm1 : 0 < m)
    {ξ : Fin m → (V →ₗ[ZMod p] ZMod p)}
    {Φ : (Fin m → U) →ₗ[ZMod p] (V →ₗ[ZMod p] V)}
    (hΦ_apply : ∀ (x : Fin m → U) (v : V), Φ x v = ∑ i, ξ i v • ((x i : U) : V))
    (hmin : ∀ g ∈ M, g ≠ 0 →
      m ≤ Module.finrank (ZMod p) (LinearMap.range g))
    {x : Fin m → U} (hxM : Φ x ∈ M) (hx0 : x ⟨0, hm1⟩ = 0) :
    Φ x = 0 := by
  classical
  let i0 : Fin m := ⟨0, hm1⟩
  have hx0' : x i0 = 0 := hx0
  by_contra hne
  let s : Finset V := (Finset.univ.erase i0).image (fun i => (((x i : U) : V)))
  have hrange_s : LinearMap.range (Φ x) ≤ Submodule.span (ZMod p) (↑s : Set V) := by
    rintro y ⟨v, rfl⟩
    have hsum_eq : (∑ i, ξ i v • (((x i : U) : V))) =
        ∑ i ∈ Finset.univ.erase i0, ξ i v • (((x i : U) : V)) := by
      refine (Finset.sum_subset (Finset.erase_subset i0 Finset.univ) ?_).symm
      intro i _ hi
      rw [Finset.mem_erase] at hi
      have hii : i = i0 := by simpa using hi
      rw [hii, hx0']
      simp
    rw [hΦ_apply x v, hsum_eq]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hmem : ((((x : Fin m → U) i : U) : V)) ∈ (s : Set V) :=
      Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hcard : s.card ≤ m - 1 := by
    calc s.card ≤ (Finset.univ.erase i0).card := Finset.card_image_le
      _ = m - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ,
          Fintype.card_fin]
  have hfin : Module.finrank (ZMod p) (LinearMap.range (Φ x)) ≤ m - 1 := by
    calc Module.finrank (ZMod p) (LinearMap.range (Φ x))
        ≤ Module.finrank (ZMod p) (Submodule.span (ZMod p) (↑s : Set V)) :=
          Submodule.finrank_mono hrange_s
      _ ≤ (↑s : Set V).toFinset.card := finrank_span_le_card _
      _ = s.card := by simp
      _ ≤ m - 1 := hcard
  have hh := hmin (Φ x) hxM hne
  omega

private lemma pi0_injective
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {M : Submodule (ZMod p) (V →ₗ[ZMod p] V)}
    {f : V →ₗ[ZMod p] V} {m : ℕ} (hm1 : 0 < m)
    {b : Module.Basis (Fin m) (ZMod p) (LinearMap.range f)}
    {ξ : Fin m → (V →ₗ[ZMod p] ZMod p)}
    (hξ_coords : ∀ (i : Fin m) (v : V),
      ξ i v = b.repr (f.codRestrict (LinearMap.range f)
        (fun c => LinearMap.mem_range_self f c) v) i)
    {Φ : (Fin m → U) →ₗ[ZMod p] (V →ₗ[ZMod p] V)}
    (hΦ_apply : ∀ (x : Fin m → U) (v : V), Φ x v = ∑ i, ξ i v • ((x i : U) : V))
    (hΦ_small : ∀ x : Fin m → U, Φ x ∈ M → x ⟨0, hm1⟩ = 0 → Φ x = 0)
    (π0 : (M.comap Φ) →ₗ[ZMod p] U)
    (hπ0 : ∀ x : M.comap Φ, π0 x = (x : Fin m → U) ⟨0, hm1⟩) :
    Function.Injective π0 := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx0 : (x : Fin m → U) ⟨0, hm1⟩ = 0 := by
    rw [← hπ0 x]
    exact LinearMap.mem_ker.mp hx
  have hΦ0 : Φ (x : Fin m → U) = 0 := hΦ_small (x : Fin m → U) x.2 hx0
  apply Subtype.ext
  funext i
  apply Subtype.ext
  obtain ⟨v, hv⟩ := (b i).2
  have heval : (((x : Fin m → U) i : U) : V) = (Φ (x : Fin m → U)) v := by
    rw [hΦ_apply (x : Fin m → U) v]
    have hξ : ∀ j, ξ j v = if i = j then 1 else 0 := by
      intro j
      have hv' : f.codRestrict (LinearMap.range f)
          (fun c => LinearMap.mem_range_self f c) v = b i := Subtype.ext hv
      rw [hξ_coords j v, hv']
      exact Module.Basis.repr_self_apply b i j
    simp only [hξ]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg (Ne.symm hj), zero_smul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hΦ0] at heval
  simpa using heval

private lemma exists_rho_action
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hUstab : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U)
    (htriv : ∀ a ∈ A, ∀ v : V, a v - v ∈ U)
    {m : ℕ} (hm1 : 0 < m)
    {M : Submodule (ZMod p) (V →ₗ[ZMod p] V)}
    {ξ : Fin m → (V →ₗ[ZMod p] ZMod p)}
    {Φ : (Fin m → U) →ₗ[ZMod p] (V →ₗ[ZMod p] V)}
    (hΦ_apply : ∀ (x : Fin m → U) (v : V), Φ x v = ∑ i, ξ i v • ((x i : U) : V))
    (hξkill : ∀ i, ∀ u ∈ U, ξ i u = 0)
    (hconj : ∀ a ∈ A, ∀ g ∈ M, a.toLinearMap.comp (g.comp a⁻¹.toLinearMap) ∈ M)
    {π0 : (M.comap Φ) →ₗ[ZMod p] U}
    (hπ0 : ∀ x : M.comap Φ, π0 x = (x : Fin m → U) ⟨0, hm1⟩) :
    ∃ (ρ : (a : V ≃ₗ[ZMod p] V) → a ∈ A → (Fin m → U) ≃ₗ[ZMod p] (Fin m → U))
      (hρM : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : Fin m → U),
        Φ x ∈ M → Φ (ρ a ha x) ∈ M),
      (∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : Fin m → U),
        Φ (ρ a ha x) = a.toLinearMap.comp ((Φ x).comp a⁻¹.toLinearMap)) ∧
      (∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : M.comap Φ),
        ((π0 ⟨ρ a ha (x : Fin m → U), hρM a ha _ x.2⟩ : U) : V) =
          a ((π0 x : U) : V)) ∧
      (∀ (i : Fin m) (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : M.comap Φ),
        (((ρ a ha (x : Fin m → U)) i : U) : V) = a (((x : Fin m → U) i : U) : V)) := by
  classical
  let ρ : (a : V ≃ₗ[ZMod p] V) → a ∈ A → (Fin m → U) ≃ₗ[ZMod p] (Fin m → U) :=
    fun a ha =>
    { toFun := fun x => fun i => ⟨a (x i : V), hUstab a ha (x i) (x i).2⟩
      invFun := fun x => fun i =>
        ⟨a⁻¹ (x i : V), hUstab a⁻¹ (A.inv_mem ha) (x i) (x i).2⟩
      left_inv := by intro x; ext i; simp
      right_inv := by intro x; ext i; simp
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro c x; ext i; simp }
  have hconj_eq : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : Fin m → U),
      Φ (ρ a ha x) = a.toLinearMap.comp ((Φ x).comp a⁻¹.toLinearMap) := by
    intro a ha x
    ext v
    simp only [LinearMap.comp_apply]
    have hξinv : ∀ i, ξ i (a⁻¹.toLinearMap v) = ξ i v := by
      intro i
      have hsub : a⁻¹.toLinearMap v - v ∈ U := htriv a⁻¹ (A.inv_mem ha) v
      have : a⁻¹.toLinearMap v = v + (a⁻¹.toLinearMap v - v) := by abel
      rw [this, map_add, hξkill i (a⁻¹.toLinearMap v - v) hsub, add_zero]
    have hL : Φ (ρ a ha x) v = ∑ i, ξ i v • a.toLinearMap ((x i : U) : V) := by
      rw [hΦ_apply (ρ a ha x) v]
      refine Finset.sum_congr rfl fun i _ => ?_
      rfl
    have hR : a.toLinearMap ((Φ x) (a⁻¹.toLinearMap v)) =
        ∑ i, ξ i (a⁻¹.toLinearMap v) • a.toLinearMap ((x i : U) : V) := by
      rw [hΦ_apply x (a⁻¹.toLinearMap v)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
    rw [hL, hR]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hξinv i]
  have hρM : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : Fin m → U),
      Φ x ∈ M → Φ (ρ a ha x) ∈ M := by
    intro a ha x hx
    rw [hconj_eq a ha x]
    exact hconj a ha (Φ x) hx
  refine ⟨ρ, hρM, hconj_eq, ?_, ?_⟩
  · intro a ha x
    rw [hπ0, hπ0]
    rfl
  · intro i a ha x
    rfl

private lemma pi0_surjective
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hirr : ∀ W : Submodule (ZMod p) V, W ≤ U →
      (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = U)
    {m : ℕ} (hm1 : 0 < m)
    {M : Submodule (ZMod p) (V →ₗ[ZMod p] V)}
    {Φ : (Fin m → U) →ₗ[ZMod p] (V →ₗ[ZMod p] V)}
    {xf : Fin m → U} (hxfM : Φ xf ∈ M)
    {u0 : V} (hxf0 : ((xf ⟨0, hm1⟩ : U) : V) = u0) (hu0 : u0 ≠ 0)
    {ρ : (a : V ≃ₗ[ZMod p] V) → a ∈ A → (Fin m → U) ≃ₗ[ZMod p] (Fin m → U)}
    (hρM : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : Fin m → U),
      Φ x ∈ M → Φ (ρ a ha x) ∈ M)
    {π0 : (M.comap Φ) →ₗ[ZMod p] U}
    (hπ0 : ∀ x : M.comap Φ, π0 x = (x : Fin m → U) ⟨0, hm1⟩)
    (hπ0_eq : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : M.comap Φ),
      ((π0 ⟨ρ a ha (x : Fin m → U), hρM a ha _ x.2⟩ : U) : V) =
        a ((π0 x : U) : V)) :
    Function.Surjective π0 := by
  let W : Submodule (ZMod p) V := Submodule.map U.subtype (LinearMap.range π0)
  have hWle : W ≤ U := by
    rintro y ⟨x, -, rfl⟩
    exact x.2
  have hWstab : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W := by
    intro a ha w hw
    obtain ⟨y, hy, rfl⟩ := hw
    obtain ⟨x, rfl⟩ := hy
    exact ⟨π0 ⟨ρ a ha (x : Fin m → U), hρM a ha _ x.2⟩,
      ⟨⟨ρ a ha (x : Fin m → U), hρM a ha _ x.2⟩, rfl⟩,
      hπ0_eq a ha x⟩
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hthis : U.subtype (π0 ⟨xf, hxfM⟩) ∈ W :=
      ⟨π0 ⟨xf, hxfM⟩, ⟨⟨xf, hxfM⟩, rfl⟩, rfl⟩
    rw [hbot] at hthis
    have hz : π0 ⟨xf, hxfM⟩ = 0 := by simpa using hthis
    have hz' : (xf ⟨0, hm1⟩ : U) = 0 := by
      simpa only [hπ0 ⟨xf, hxfM⟩] using hz
    exact hu0 (hxf0 ▸ congrArg Subtype.val hz')
  have hWU : W = U := by
    rcases hirr W hWle hWstab with h | h
    · exact absurd h hWne
    · exact h
  intro u
  have huW : (u : V) ∈ W := by rw [hWU]; exact u.2
  obtain ⟨y, hy, hy'⟩ := huW
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  rw [hx]
  exact Subtype.ext hy'

private lemma Ti_comm
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hUstab : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U)
    {m : ℕ}
    {M : Submodule (ZMod p) (V →ₗ[ZMod p] V)}
    {Φ : (Fin m → U) →ₗ[ZMod p] (V →ₗ[ZMod p] V)}
    {π0 : (M.comap Φ) →ₗ[ZMod p] U}
    {e : (M.comap Φ) ≃ₗ[ZMod p] U} (he : ∀ x, e x = π0 x)
    {ρ : (a : V ≃ₗ[ZMod p] V) → a ∈ A → (Fin m → U) ≃ₗ[ZMod p] (Fin m → U)}
    (hρM : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : Fin m → U),
      Φ x ∈ M → Φ (ρ a ha x) ∈ M)
    (hπ0_eq : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : M.comap Φ),
      ((π0 ⟨ρ a ha (x : Fin m → U), hρM a ha _ x.2⟩ : U) : V) =
        a ((π0 x : U) : V))
    (hπi_eq : ∀ (i : Fin m) (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (x : M.comap Φ),
      (((ρ a ha (x : Fin m → U)) i : U) : V) = a (((x : Fin m → U) i : U) : V))
    {Ti : Fin m → (U →ₗ[ZMod p] U)}
    (hTi : ∀ i uu, Ti i uu = (((e.symm uu : M.comap Φ) : Fin m → U) i)) :
    ∀ (i : Fin m) (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (uu : U),
      Ti i ⟨a (uu : V), hUstab a ha (uu : V) uu.2⟩ =
        ⟨a ((Ti i uu : U) : V),
          hUstab a ha ((Ti i uu : U) : V) (Ti i uu).2⟩ := by
  intro i a ha uu
  apply Subtype.ext
  have hsymm : e.symm ⟨a (uu : V), hUstab a ha (uu : V) uu.2⟩ =
      ⟨ρ a ha ((e.symm uu : M.comap Φ) : Fin m → U),
        hρM a ha ((e.symm uu : M.comap Φ) : Fin m → U) (e.symm uu).2⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [he, hπ0_eq]
    rw [← he (e.symm uu), e.apply_symm_apply]
  rw [hTi]
  rw [congrArg (fun x : M.comap Φ => ((x : Fin m → U) i)) hsymm]
  rw [hTi]
  exact hπi_eq i a ha (e.symm uu)

private lemma exists_extensions
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hUstab : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U)
    {m : ℕ} {Ti : Fin m → (U →ₗ[ZMod p] U)}
    (hTi_comm : ∀ (i : Fin m) (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (uu : U),
      Ti i ⟨a (uu : V), hUstab a ha (uu : V) uu.2⟩ =
        ⟨a ((Ti i uu : U) : V),
          hUstab a ha ((Ti i uu : U) : V) (Ti i uu).2⟩) :
    ∃ gi : Fin m → (V →ₗ[ZMod p] V),
      (∀ i, LinearMap.range (gi i) ≤ U) ∧
      (∀ i (uu : U), gi i (uu : V) = (Ti i uu : V)) ∧
      (∀ (i : Fin m) (a : V ≃ₗ[ZMod p] V) (_ha : a ∈ A) (uu : U),
        gi i (a (uu : V)) = a (gi i (uu : V))) := by
  classical
  have hTi_ext : ∀ i, ∃ gi : V →ₗ[ZMod p] V,
      LinearMap.range gi ≤ U ∧ (∀ uu : U, gi (uu : V) = (Ti i uu : V)) ∧
        (∀ a ∈ A, ∀ uu : U, gi (a (uu : V)) = a (gi (uu : V))) := by
    intro i
    obtain ⟨g', hg'⟩ := LinearMap.exists_extend (p := U) (Ti i)
    refine ⟨U.subtype.comp g', ?_, ?_, ?_⟩
    · exact le_trans (LinearMap.range_comp_le_range g' U.subtype)
        (le_of_eq (Submodule.range_subtype U))
    · intro uu
      have h1 : g' (uu : V) = Ti i uu := congrArg (fun ff : U →ₗ[ZMod p] U => ff uu) hg'
      change (g' (uu : V) : V) = (Ti i uu : V)
      rw [h1]
    · intro a ha uu
      have h1 : g' (uu : V) = Ti i uu := congrArg (fun ff : U →ₗ[ZMod p] U => ff uu) hg'
      have h2 : g' (a (uu : V)) =
          Ti i ⟨a (uu : V), hUstab a ha (uu : V) uu.2⟩ :=
        congrArg (fun ff : U →ₗ[ZMod p] U =>
          ff ⟨a (uu : V), hUstab a ha (uu : V) uu.2⟩) hg'
      change (g' (a (uu : V)) : V) = a (g' (uu : V))
      rw [h2, h1, hTi_comm i a ha uu]
  choose gi hgi_range hgi_apply hgi_comm using hTi_ext
  exact ⟨gi, hgi_range, hgi_apply, hgi_comm⟩

private lemma exists_scalars_coord
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    {m : ℕ} (hm1 : 0 < m)
    {M : Submodule (ZMod p) (V →ₗ[ZMod p] V)}
    {Φ : (Fin m → U) →ₗ[ZMod p] (V →ₗ[ZMod p] V)}
    {π0 : (M.comap Φ) →ₗ[ZMod p] U}
    (hπ0 : ∀ x : M.comap Φ, π0 x = (x : Fin m → U) ⟨0, hm1⟩)
    {e : (M.comap Φ) ≃ₗ[ZMod p] U} (he : ∀ x, e x = π0 x)
    {Ti : Fin m → (U →ₗ[ZMod p] U)}
    (hTi : ∀ i uu, Ti i uu = (((e.symm uu : M.comap Φ) : Fin m → U) i))
    {gi : Fin m → (V →ₗ[ZMod p] V)}
    (hgi_range : ∀ i, LinearMap.range (gi i) ≤ U)
    (hgi_apply : ∀ i (uu : U), gi i (uu : V) = (Ti i uu : V))
    (hgi_comm : ∀ (i : Fin m) (a : V ≃ₗ[ZMod p] V) (_ha : a ∈ A) (uu : U),
      gi i (a (uu : V)) = a (gi i (uu : V)))
    (hend : ∀ f : V →ₗ[ZMod p] V, LinearMap.range f ≤ U →
      (∀ a ∈ A, ∀ u ∈ U, f (a u) = a (f u)) →
      ∃ c : ZMod p, ∀ u ∈ U, f u = c • u) :
    ∃ c : Fin m → ZMod p, ∀ x : M.comap Φ, ∀ i,
      (((x : Fin m → U) i : U) : V) = c i • (((x : Fin m → U) ⟨0, hm1⟩ : U) : V) := by
  have hxscal : ∀ i, ∃ c : ZMod p, ∀ uu ∈ U, gi i uu = c • uu :=
    fun i => hend (gi i) (hgi_range i) (fun a ha u hu => hgi_comm i a ha ⟨u, hu⟩)
  choose c hc using hxscal
  refine ⟨c, ?_⟩
  intro x i
  have h1 : (x : Fin m → U) i = Ti i (π0 x) := by
    rw [hTi, ← he x, e.symm_apply_apply]
  have h2 : gi i (π0 x) = c i • (π0 x) := hc i (π0 x) (π0 x).2
  have h3 : gi i (π0 x) = ((Ti i (π0 x) : U) : V) := hgi_apply i (π0 x)
  have h4 : ((Ti i (π0 x) : U) : V) = (((x : Fin m → U) i : U) : V) := by
    rw [← h1]
  rw [← h4, ← h3, h2, hπ0]

private lemma finrank_le_one_of_proportional
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V]
    {f : V →ₗ[ZMod p] V} {m : ℕ}
    (hm : m = Module.finrank (ZMod p) (LinearMap.range f)) (hm1 : 0 < m)
    {ξ : Fin m → (V →ₗ[ZMod p] ZMod p)}
    {b : Module.Basis (Fin m) (ZMod p) (LinearMap.range f)}
    (hbne : b ⟨0, hm1⟩ ≠ 0)
    {u : Fin m → V} (hu : ∀ i, u i = (b i : V))
    (hdecomp : f = ∑ i, (ξ i).smulRight (u i))
    (c : Fin m → ZMod p) (hcoord : ∀ i, u i = c i • u ⟨0, hm1⟩) :
    m ≤ 1 := by
  have hrange_span : LinearMap.range f ≤
      Submodule.span (ZMod p) ({u ⟨0, hm1⟩} : Set V) := by
    rintro y ⟨v, rfl⟩
    rw [hdecomp]
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hcoord i, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  calc m = Module.finrank (ZMod p) (LinearMap.range f) := hm
    _ ≤ Module.finrank (ZMod p) (Submodule.span (ZMod p) ({u ⟨0, hm1⟩} : Set V)) :=
        Submodule.finrank_mono hrange_span
    _ = 1 := finrank_span_singleton
        (fun h => hbne (Subtype.ext (hu ⟨0, hm1⟩ ▸ h)))

private lemma finrank_range_pos
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V]
    {f : V →ₗ[ZMod p] V} {m : ℕ}
    (hm : m = Module.finrank (ZMod p) (LinearMap.range f)) (hfne : f ≠ 0) :
    0 < m := by
  rw [Nat.pos_iff_ne_zero, hm]
  intro h0
  exact hfne (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))

private theorem rank_eq_one_of_minimal
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hUstab : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U)
    (htriv : ∀ a ∈ A, ∀ v : V, a v - v ∈ U)
    (hirr : ∀ W : Submodule (ZMod p) V, W ≤ U →
      (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = U)
    (hend : ∀ f : V →ₗ[ZMod p] V, LinearMap.range f ≤ U →
      (∀ a ∈ A, ∀ u ∈ U, f (a u) = a (f u)) →
      ∃ c : ZMod p, ∀ u ∈ U, f u = c • u)
    (M : Submodule (ZMod p) (V →ₗ[ZMod p] V))
    (hUle : ∀ g ∈ M, LinearMap.range g ≤ U)
    (hUker : ∀ g ∈ M, ∀ u ∈ U, g u = 0)
    (hconj : ∀ a ∈ A, ∀ g ∈ M, a.toLinearMap.comp (g.comp a⁻¹.toLinearMap) ∈ M)
    (f : V →ₗ[ZMod p] V) (hfM : f ∈ M) (hfne : f ≠ 0)
    (hmin : ∀ g ∈ M, g ≠ 0 →
      Module.finrank (ZMod p) (LinearMap.range f) ≤ Module.finrank (ZMod p) (LinearMap.range g)) :
    Module.finrank (ZMod p) (LinearMap.range f) = 1 := by
  classical
  let m := Module.finrank (ZMod p) (LinearMap.range f)
  change m = 1
  have hle : LinearMap.range f ≤ U := hUle f hfM
  have hm1 : 0 < m := finrank_range_pos (m := m) rfl hfne
  let b : Module.Basis (Fin m) (ZMod p) (LinearMap.range f) :=
    Module.finBasis (ZMod p) (LinearMap.range f)
  obtain ⟨ξ, hξ_coords, hdecomp⟩ := exists_functionals b
  have hξkill : ∀ i, ∀ u ∈ U, ξ i u = 0 :=
    functionals_kill_U hξ_coords (fun u hu => hUker f hfM u hu)
  obtain ⟨Φ, xf, hΦ_apply, hΦxf, hxf0⟩ := exists_Phi b ξ hdecomp hle
  let X : Submodule (ZMod p) (Fin m → U) := M.comap Φ
  let π0 : X →ₗ[ZMod p] U := (LinearMap.proj ⟨0, hm1⟩).comp X.subtype
  have hπ0 : ∀ x : X, π0 x = (x : Fin m → U) ⟨0, hm1⟩ := fun x => rfl
  have hxfM : Φ xf ∈ M := by rw [hΦxf]; exact hfM
  have hmin' : ∀ g ∈ M, g ≠ 0 → m ≤ Module.finrank (ZMod p) (LinearMap.range g) := hmin
  have hΦ_small : ∀ x : Fin m → U, Φ x ∈ M → x ⟨0, hm1⟩ = 0 → Φ x = 0 :=
    fun x hxM hx0 => Phi_eq_zero_of_zero_coord hm1 hΦ_apply hmin' hxM hx0
  have hinj : Function.Injective π0 :=
    pi0_injective hm1 hξ_coords hΦ_apply hΦ_small π0 hπ0
  obtain ⟨ρ, hρM, hρ_conj, hπ0_eq, hπi_eq⟩ :=
    exists_rho_action hUstab htriv hm1 hΦ_apply hξkill hconj hπ0
  have hbne_sub : b ⟨0, hm1⟩ ≠ 0 := b.ne_zero ⟨0, hm1⟩
  have hbne : (b ⟨0, hm1⟩ : V) ≠ 0 := fun h => hbne_sub (Subtype.ext h)
  have hsurj : Function.Surjective π0 :=
    pi0_surjective hirr hm1 hxfM (hxf0 ⟨0, hm1⟩) hbne hρM hπ0 hπ0_eq
  let e : X ≃ₗ[ZMod p] U := LinearEquiv.ofBijective π0 ⟨hinj, hsurj⟩
  have he : ∀ x, e x = π0 x := fun x => rfl
  let Ti : Fin m → (U →ₗ[ZMod p] U) :=
    fun i => (LinearMap.proj i).comp (X.subtype.comp e.symm.toLinearMap)
  have hTi : ∀ i uu, Ti i uu = (((e.symm uu : X) : Fin m → U) i) := fun i uu => rfl
  have hTi_comm := Ti_comm hUstab he hρM hπ0_eq hπi_eq hTi
  obtain ⟨gi, hgi_range, hgi_apply, hgi_comm⟩ := exists_extensions hUstab hTi_comm
  obtain ⟨c, hcoord⟩ := exists_scalars_coord hm1 hπ0 he hTi hgi_range hgi_apply hgi_comm hend
  have hcoord' : ∀ i, (b i : V) = c i • (b ⟨0, hm1⟩ : V) := by
    intro i
    have h := hcoord ⟨xf, hxfM⟩ i
    rw [hxf0 i, hxf0 ⟨0, hm1⟩] at h
    exact h
  have hle1 : m ≤ 1 :=
    finrank_le_one_of_proportional (f := f) (b := b) (u := fun i => (b i : V))
      rfl hm1 hbne_sub (fun i => rfl) hdecomp c hcoord'
  omega

private lemma U_stable
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (htriv : ∀ a ∈ A, ∀ v : V, a v - v ∈ U) :
    ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := by
  intro a ha u hu
  have h := htriv a ha u
  have : a u = u + (a u - u) := by abel
  rw [this]
  exact U.add_mem hu h

private lemma range_le_of_mem_span_linDiff
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (htriv : ∀ g ∈ A, ∀ v : V, g v - v ∈ U) :
    ∀ φ ∈ Submodule.span (ZMod p)
      (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V))),
      LinearMap.range φ ≤ U := by
  intro φ hφ
  refine Submodule.span_induction (p := fun φ _ => LinearMap.range φ ≤ U) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨h, hhN, rfl⟩
    rintro y ⟨v, rfl⟩
    simpa [linDiff_apply] using htriv h (mem_Nsub.mp hhN).1 v
  · simp
  · intro x y _ _ hx hy
    exact le_trans (LinearMap.range_add_le x y) (sup_le hx hy)
  · intro c x _ hx
    rintro y ⟨v, rfl⟩
    exact U.smul_mem c (hx ⟨v, rfl⟩)

private lemma eq_zero_of_mem_span_linDiff
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)} :
    ∀ φ ∈ Submodule.span (ZMod p)
      (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V))),
      ∀ u ∈ U, φ u = 0 := by
  intro φ hφ
  refine Submodule.span_induction (p := fun φ _ => ∀ u ∈ U, φ u = 0) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨h, hhN, rfl⟩ u hu
    simp only [linDiff_apply]
    rw [(mem_Nsub.mp hhN).2 u hu, sub_self]
  · intro u hu; simp
  · intro x y _ _ hx hy u hu
    simp [hx u hu, hy u hu]
  · intro c x _ hx u hu
    simp [hx u hu]

private lemma conj_mem_span_linDiff
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hUstab : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U) :
    ∀ a ∈ A, ∀ φ ∈ Submodule.span (ZMod p)
      (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V))),
      a.toLinearMap.comp (φ.comp a⁻¹.toLinearMap) ∈
        Submodule.span (ZMod p)
          (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V))) := by
  intro a ha φ hφ
  refine Submodule.span_induction
    (p := fun φ _ => a.toLinearMap.comp (φ.comp a⁻¹.toLinearMap) ∈
      Submodule.span (ZMod p)
        (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V)))) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨h, hhN, rfl⟩
    have hconj_eq : a.toLinearMap.comp ((linDiff h).comp a⁻¹.toLinearMap) =
        linDiff (a * h * a⁻¹) := by
      ext v; simp [linDiff_apply, LinearEquiv.mul_apply]
    rw [hconj_eq]
    have hmem : a * h * a⁻¹ ∈ Nsub A U := by
      rw [mem_Nsub]
      refine ⟨A.mul_mem (A.mul_mem ha (mem_Nsub.mp hhN).1) (A.inv_mem ha), ?_⟩
      intro u hu
      simp only [LinearEquiv.mul_apply]
      rw [(mem_Nsub.mp hhN).2 (a⁻¹ u) (hUstab a⁻¹ (A.inv_mem ha) u hu)]
      simp
    exact Submodule.subset_span ⟨a * h * a⁻¹, hmem, rfl⟩
  · simp
  · rintro x y _ _ hx hy
    have : a.toLinearMap.comp ((x + y).comp a⁻¹.toLinearMap) =
        a.toLinearMap.comp (x.comp a⁻¹.toLinearMap) +
        a.toLinearMap.comp (y.comp a⁻¹.toLinearMap) := by
      ext v; simp [LinearMap.add_apply]
    rw [this]
    exact Submodule.add_mem _ hx hy
  · rintro c x _ hx
    have : a.toLinearMap.comp ((c • x).comp a⁻¹.toLinearMap) =
        c • (a.toLinearMap.comp (x.comp a⁻¹.toLinearMap)) := by
      ext v; simp [LinearMap.smul_apply, map_smul]
    rw [this]
    exact Submodule.smul_mem _ c hx

private lemma exists_minimal_rank
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {U : Submodule (ZMod p) V} {A : Subgroup (V ≃ₗ[ZMod p] V)}
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ A)
    (hgU : ∀ u ∈ U, g u = u) (hg1 : g ≠ 1) :
    ∃ f ∈ Submodule.span (ZMod p)
        (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V))),
      f ≠ 0 ∧ ∀ φ ∈ Submodule.span (ZMod p)
        (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V))), φ ≠ 0 →
        Module.finrank (ZMod p) (LinearMap.range f) ≤
          Module.finrank (ZMod p) (LinearMap.range φ) := by
  classical
  have hgN : g ∈ Nsub A U := mem_Nsub.mpr ⟨hg, hgU⟩
  have hgne : linDiff g ≠ 0 := by
    intro h0
    apply hg1
    ext v
    exact sub_eq_zero.mp (by
      have := congrArg (fun f : V →ₗ[ZMod p] V => f v) h0
      simpa [linDiff_apply] using this)
  have hgM : linDiff g ∈ Submodule.span (ZMod p)
      (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V))) :=
    Submodule.subset_span ⟨g, hgN, rfl⟩
  have hex : ∃ n, ∃ φ ∈ Submodule.span (ZMod p)
        (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V))),
      φ ≠ 0 ∧ Module.finrank (ZMod p) (LinearMap.range φ) = n :=
    ⟨_, linDiff g, hgM, hgne, rfl⟩
  obtain ⟨f, hfM, hfne, hfrank⟩ := Nat.find_spec hex
  refine ⟨f, hfM, hfne, ?_⟩
  intro φ hφM hφne
  rw [hfrank]
  exact Nat.find_min' hex ⟨φ, hφM, hφne, rfl⟩

theorem ggLin_faithful_on_com
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hnotr : ∀ g ∈ A, g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}))
    (hirr : ∀ W : Submodule (ZMod p) V, W ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ggLinCom (A : Set (V ≃ₗ[ZMod p] V)))
    (hend : ∀ f : V →ₗ[ZMod p] V, LinearMap.range f ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ A, ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), f (a u) = a (f u)) →
      ∃ c : ZMod p, ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), f u = c • u)
    (htriv : ∀ g ∈ A, ∀ v, g v - v ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)))
    (g : V ≃ₗ[ZMod p] V) (hg : g ∈ A)
    (hgU : ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), g u = u) : g = 1 := by
  classical
  by_contra hg1
  set U : Submodule (ZMod p) V := ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) with hU
  have hUstab : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := U_stable htriv
  let M : Submodule (ZMod p) (V →ₗ[ZMod p] V) :=
    Submodule.span (ZMod p) (linDiff '' (Nsub A U : Set (V ≃ₗ[ZMod p] V)))
  obtain ⟨f, hfM, hfne, hmin⟩ := exists_minimal_rank hg hgU hg1
  have hM_range : ∀ φ ∈ M, LinearMap.range φ ≤ U :=
    fun φ hφ => range_le_of_mem_span_linDiff htriv φ hφ
  have hM_ker : ∀ φ ∈ M, ∀ u ∈ U, φ u = 0 :=
    fun φ hφ => eq_zero_of_mem_span_linDiff φ hφ
  have hM_conj : ∀ a ∈ A, ∀ φ ∈ M,
      a.toLinearMap.comp (φ.comp a⁻¹.toLinearMap) ∈ M :=
    fun a ha φ hφ => conj_mem_span_linDiff hUstab a ha φ hφ
  have hrank : Module.finrank (ZMod p) (LinearMap.range f) = 1 :=
    rank_eq_one_of_minimal hUstab htriv hirr hend M hM_range hM_ker hM_conj f hfM hfne hmin
  obtain ⟨h, hhN, hhlin⟩ := exists_linDiff_of_mem_span htriv f hfM
  have hhA : h ∈ A := (mem_Nsub.mp hhN).1
  have hhne : h ≠ 1 := by
    intro hh1
    apply hfne
    rw [← hhlin, hh1, linDiff_one]
  have hfin : Module.finrank (ZMod p) (ggLinMove h) = 1 := by
    rw [show ggLinMove h = LinearMap.range (linDiff h) from rfl, hhlin]
    exact hrank
  have hfix : ggLinMove h ≤ ggLinFix {h} := by
    rw [show ggLinMove h = LinearMap.range (linDiff h) from rfl, hhlin]
    intro w hw
    have hwU : w ∈ U := hM_range f hfM hw
    have hwfix : h w = w := (mem_Nsub.mp hhN).2 w hwU
    simpa [ggLinFix] using hwfix
  exact hnotr h hhA hhne ⟨hfin, hfix⟩

end Module

end CFSG.StandardType

end
