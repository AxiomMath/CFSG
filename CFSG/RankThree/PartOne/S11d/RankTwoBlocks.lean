module

public import CFSG.RankThree.PartOne.S11d.RankTwoLinear
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartOne.LIT

open Module

universe u

variable {k : Type u} [Field k] {A B : Type} [AddCommGroup A] [Module k A] [AddCommGroup B]
  [Module k B]

@[expose] def blockHom : (A ≃ₗ[k] A) × (B ≃ₗ[k] B) →* ((A × B) ≃ₗ[k] (A × B)) where
  toFun x := x.1.prodCongr x.2
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

@[simp] theorem blockHom_apply (x : (A ≃ₗ[k] A) × (B ≃ₗ[k] B)) (v : A × B) :
    blockHom x v = (x.1 v.1, x.2 v.2) := rfl

theorem blockHom_injective : Function.Injective (blockHom (k := k) (A := A) (B := B)) := by
  intro x y h
  have h1 : ∀ a : A, x.1 a = y.1 a := fun a => by
    have := congrArg Prod.fst (LinearEquiv.congr_fun h (a, 0))
    simpa using this
  have h2 : ∀ b : B, x.2 b = y.2 b := fun b => by
    have := congrArg Prod.snd (LinearEquiv.congr_fun h (0, b))
    simpa using this
  exact Prod.ext (LinearEquiv.ext h1) (LinearEquiv.ext h2)

@[expose] def unip (k : Type u) [Field k] (A B : Type) [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] : Subgroup ((A × B) ≃ₗ[k] (A × B)) where
  carrier := {u | (∀ v, (u v).2 = v.2) ∧ ∀ a : A, u (a, 0) = (a, 0)}
  one_mem' := ⟨fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro u u' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun v => ?_, fun a => ?_⟩
    · change (u (u' v)).2 = v.2
      rw [h1, h1']
    · change u (u' (a, 0)) = (a, 0)
      rw [h2', h2]
  inv_mem' := by
    rintro u ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun a => ?_⟩
    · have := h1 (u.symm v)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    · show u.symm (a, 0) = (a, 0)
      rw [LinearEquiv.symm_apply_eq, h2]

theorem unip_apply {u : (A × B) ≃ₗ[k] (A × B)} (hu : u ∈ unip k A B) (a : A) (b : B) :
    u (a, b) = (a + (u (0, b)).1, b) := by
  obtain ⟨h1, h2⟩ := hu
  have hsum : (a, b) = (a, 0) + (0, b) := by simp
  rw [hsum, map_add, h2]
  refine Prod.ext ?_ ?_
  · simp
  · have := h1 (0, b)
    simp only [Prod.snd_add, zero_add]
    simpa using this

theorem unip_sq [CharP k 2] {u : (A × B) ≃ₗ[k] (A × B)} (hu : u ∈ unip k A B) : u * u = 1 := by
  apply LinearEquiv.ext
  rintro ⟨a, b⟩
  have h := unip_apply hu a b
  change u (u (a, b)) = (a, b)
  rw [h, unip_apply hu (a + (u (0, b)).1) b]
  refine Prod.ext ?_ rfl
  have h2 : (2 : k) = 0 := by simpa using CharP.cast_eq_zero k 2
  have : (u (0, b)).1 + (u (0, b)).1 = 0 := by
    rw [← two_smul k, h2, zero_smul]
  show a + (u (0, b)).1 + (u (0, b)).1 = a
  rw [add_assoc, this, add_zero]

theorem blockHom_inv_apply (x : (A ≃ₗ[k] A) × (B ≃ₗ[k] B)) (v : A × B) :
    (blockHom x)⁻¹ v = (x.1⁻¹ v.1, x.2⁻¹ v.2) := by
  rw [← map_inv]
  rfl

theorem blockHom_conj_mem_unip (x : (A ≃ₗ[k] A) × (B ≃ₗ[k] B)) {u : (A × B) ≃ₗ[k] (A × B)}
    (hu : u ∈ unip k A B) : blockHom x * u * (blockHom x)⁻¹ ∈ unip k A B := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨fun v => ?_, fun a => ?_⟩
  · change (blockHom x (u ((blockHom x)⁻¹ v))).2 = v.2
    rw [blockHom_apply, h1, blockHom_inv_apply]
    show x.2 (x.2⁻¹ v.2) = v.2
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  · change blockHom x (u ((blockHom x)⁻¹ (a, 0))) = (a, 0)
    have : (blockHom x)⁻¹ (a, 0) = (x.1⁻¹ a, 0) := by
      rw [blockHom_inv_apply]
      simp
    rw [this, h2, blockHom_apply]
    refine Prod.ext ?_ (by simp)
    show x.1 (x.1⁻¹ a) = a
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl

theorem blockHom_mem_normalizer_unip (x : (A ≃ₗ[k] A) × (B ≃ₗ[k] B)) :
    blockHom x ∈ Subgroup.normalizer (unip k A B : Set ((A × B) ≃ₗ[k] (A × B))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => blockHom_conj_mem_unip x hu, fun hu => ?_⟩
  have h := blockHom_conj_mem_unip x⁻¹ hu
  rw [map_inv, inv_inv] at h
  have : (blockHom x)⁻¹ * (blockHom x * u * (blockHom x)⁻¹) * blockHom x = u := by group
  rwa [this] at h

theorem det_unip [CharP k 2] [FiniteDimensional k A] [FiniteDimensional k B]
    {u : (A × B) ≃ₗ[k] (A × B)} (hu : u ∈ unip k A B) : LinearEquiv.det u = 1 := by
  have h1 : LinearEquiv.det u * LinearEquiv.det u = 1 := by
    rw [← map_mul, unip_sq hu, map_one]
  have h2 : ((LinearEquiv.det u : kˣ) : k) * ((LinearEquiv.det u : kˣ) : k) = 1 := by
    have := congrArg (fun x : kˣ => (x : k)) h1
    simpa using this
  apply Units.ext
  have h3 : (2 : k) = 0 := by simpa using CharP.cast_eq_zero k 2
  have h4 : (((LinearEquiv.det u : kˣ) : k) - 1) * (((LinearEquiv.det u : kˣ) : k) - 1) = 0 := by
    linear_combination h2 - (((LinearEquiv.det u : kˣ) : k) - 1) * h3
  have h5 := mul_self_eq_zero.mp h4
  rw [Units.val_one]
  exact sub_eq_zero.mp h5

@[expose] def shear (φ : B →ₗ[k] A) : (A × B) ≃ₗ[k] (A × B) :=
  LinearEquiv.ofLinearMap
    ((LinearMap.fst k A B + φ.comp (LinearMap.snd k A B)).prod (LinearMap.snd k A B))
    ((LinearMap.fst k A B - φ.comp (LinearMap.snd k A B)).prod (LinearMap.snd k A B))
    (LinearMap.ext fun v => Prod.ext (by simp) rfl)
    (LinearMap.ext fun v => Prod.ext (by simp) rfl)

@[simp] theorem shear_apply (φ : B →ₗ[k] A) (v : A × B) : shear φ v = (v.1 + φ v.2, v.2) := rfl

theorem shear_mem_unip (φ : B →ₗ[k] A) : shear φ ∈ unip k A B :=
  ⟨fun _ => rfl, fun a => by simp⟩

theorem unip_ne_bot [Nontrivial A] [Nontrivial B] : unip k A B ≠ ⊥ := by
  classical
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  obtain ⟨b₀, hb₀⟩ := exists_ne (0 : B)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k B, f b₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hb₀ ((Module.forall_dual_apply_eq_zero_iff k b₀).mp h)
  intro hbot
  have hmem : shear (f.smulRight a₀) ∈ unip k A B := shear_mem_unip _
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg Prod.fst (LinearEquiv.congr_fun hmem (0, b₀))
  have h2 : f b₀ • a₀ = 0 := by simpa using this
  rcases smul_eq_zero.mp h2 with h | h
  · exact hf h
  · exact ha₀ h

theorem isPGroup_unip [CharP k 2] : IsPGroup 2 (unip k A B) := fun x =>
  ⟨1, by
    have := unip_sq x.2
    exact Subtype.ext (by simpa [pow_two] using this)⟩

theorem det_eq_one_of_pow_eq_one [Fintype k] {r : ℕ} (hr : r.Prime) (hrk : ¬ r ∣ Fintype.card k - 1)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {g : W ≃ₗ[k] W}
    (hg : g ^ r = 1) : LinearEquiv.det g = 1 := by
  have h1 : (LinearEquiv.det g) ^ r = 1 := by rw [← map_pow, hg, map_one]
  have h2 : orderOf (LinearEquiv.det g) ∣ r := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (LinearEquiv.det g) ∣ Fintype.card k - 1 := by
    have := orderOf_dvd_natCard (LinearEquiv.det g)
    rwa [Nat.card_units, Nat.card_eq_fintype_card] at this
  rcases (Nat.dvd_prime hr).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h3) hrk

theorem det_blockHom [FiniteDimensional k A] [FiniteDimensional k B]
    (x : (A ≃ₗ[k] A) × (B ≃ₗ[k] B)) :
    LinearEquiv.det (blockHom x) = LinearEquiv.det x.1 * LinearEquiv.det x.2 := by
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_mul, LinearEquiv.coe_det, LinearEquiv.coe_det]
  have : ((blockHom x : (A × B) ≃ₗ[k] (A × B)) : (A × B) →ₗ[k] (A × B)) =
      (x.1 : A →ₗ[k] A).prodMap (x.2 : B →ₗ[k] B) := LinearMap.ext fun _ => rfl
  rw [this, LinearMap.det_prodMap]

theorem exists_rank_two_block [Fintype k] {r : ℕ} (hr : r.Prime) (hrk : ¬ r ∣ Fintype.card k - 1)
    [FiniteDimensional k A] [FiniteDimensional k B] {e : ℕ} (he1 : 1 ≤ e)
    (hdvd : r ∣ Fintype.card k ^ e - 1) (heA : e ≤ finrank k A) (heB : e ≤ finrank k B) :
    ∃ R : Subgroup ((A × B) ≃ₗ[k] (A × B)), CFSG.IsElementaryAbelian r R ∧ Nat.card R = r ^ 2 ∧
      (∀ g ∈ R, LinearEquiv.det g = 1) ∧
      R ≤ Subgroup.normalizer (unip k A B : Set ((A × B) ≃ₗ[k] (A × B))) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨C, hC⟩ := LIT.exists_orderOf_prime_linearEquiv hr he1 heA hdvd
  obtain ⟨D, hD⟩ := LIT.exists_orderOf_prime_linearEquiv hr he1 heB hdvd
  have hCr : C ^ r = 1 := by rw [← hC]; exact pow_orderOf_eq_one C
  have hDr : D ^ r = 1 := by rw [← hD]; exact pow_orderOf_eq_one D
  have hdetC : LinearEquiv.det C = 1 := det_eq_one_of_pow_eq_one hr hrk hCr
  have hdetD : LinearEquiv.det D = 1 := det_eq_one_of_pow_eq_one hr hrk hDr
  let R₀ : Subgroup ((A ≃ₗ[k] A) × (B ≃ₗ[k] B)) := (Subgroup.zpowers C).prod (Subgroup.zpowers D)
  refine ⟨R₀.map blockHom, ?_, ?_, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · intro a b
      obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      show (a : (A × B) ≃ₗ[k] (A × B)) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx1
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy1
      obtain ⟨i', hi'⟩ := Subgroup.mem_zpowers_iff.mp hx2
      obtain ⟨j', hj'⟩ := Subgroup.mem_zpowers_iff.mp hy2
      refine Prod.ext ?_ ?_
      · show x.1 * y.1 = y.1 * x.1
        rw [← hi, ← hj]
        exact (Commute.zpow_zpow_self C i j).eq
      · show x.2 * y.2 = y.2 * x.2
        rw [← hi', ← hj']
        exact (Commute.zpow_zpow_self D i' j').eq
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
      obtain ⟨x, hx, hg⟩ := Subgroup.mem_map.mp g.2
      apply Subtype.ext
      show (g : (A × B) ≃ₗ[k] (A × B)) ^ r = 1
      rw [← hg, ← map_pow]
      obtain ⟨hx1, hx2⟩ := hx
      have h1 : x.1 ^ r = 1 := by
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx1
        rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hCr, one_zpow]
      have h2 : x.2 ^ r = 1 := by
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx2
        rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hDr, one_zpow]
      have : x ^ r = 1 := Prod.ext h1 h2
      rw [this, map_one]
  · rw [Subgroup.card_map_of_injective blockHom_injective]
    have hC' : Nat.card (Subgroup.zpowers C) = r := by rw [Nat.card_zpowers, hC]
    have hD' : Nat.card (Subgroup.zpowers D) = r := by rw [Nat.card_zpowers, hD]
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hC', hD']
    ring
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hx1, hx2⟩ := hx
    rw [det_blockHom]
    have h1 : LinearEquiv.det x.1 = 1 := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx1
      rw [← hi, map_zpow, hdetC, one_zpow]
    have h2 : LinearEquiv.det x.2 = 1 := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx2
      rw [← hi, map_zpow, hdetD, one_zpow]
    rw [h1, h2, mul_one]
  · rintro _ ⟨x, -, rfl⟩
    exact blockHom_mem_normalizer_unip x

end CFSG.RankThree.PartOne.LIT
