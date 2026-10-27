module

public import CFSG.Monster.GMS.Griess13.Blocks

public section

namespace CFSG.Monster.GMS.Griess13

open Finset

section Perfect

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem comm_on_block {W : Submodule (ZMod 2) V} {x : V} {T A B : Module.End (ZMod 2) V}
    (hspan : ∀ y ∈ W, ∃ a b : ZMod 2, y = a • x + b • T x) (hx : x ∈ W)
    (hT2 : T (T x) = x + T x) (hA : ∀ y ∈ W, A y ∈ W) (hB : ∀ y ∈ W, B y ∈ W)
    (hAT : ∀ y ∈ W, A (T y) = T (A y)) (hBT : ∀ y ∈ W, B (T y) = T (B y)) :
    ∀ y ∈ W, A (B y) = B (A y) := by
  have key : ∀ C : Module.End (ZMod 2) V, (∀ y ∈ W, C y ∈ W) → (∀ y ∈ W, C (T y) = T (C y)) →
      ∃ a₁ b₁ : ZMod 2, ∀ p q : ZMod 2,
        C (p • x + q • T x) =
          (p * a₁ + q * b₁) • x + (p * b₁ + q * (a₁ + b₁)) • T x := by
    intro C hC hCT
    obtain ⟨a₁, b₁, hCx⟩ := hspan (C x) (hC x hx)
    refine ⟨a₁, b₁, fun p q => ?_⟩
    have hCTx : C (T x) = b₁ • x + (a₁ + b₁) • T x := by
      rw [hCT x hx, hCx, map_add, map_smul, map_smul, hT2]
      module
    rw [map_add, map_smul, map_smul, hCx, hCTx]
    module
  obtain ⟨a₁, b₁, hA'⟩ := key A hA hAT
  obtain ⟨a₂, b₂, hB'⟩ := key B hB hBT
  intro y hy
  obtain ⟨a, b, rfl⟩ := hspan y hy
  rw [hB', hA', hA', hB']
  have hid : ∀ a b a₁ b₁ a₂ b₂ : ZMod 2,
      (a * a₂ + b * b₂) * a₁ + (a * b₂ + b * (a₂ + b₂)) * b₁ =
        (a * a₁ + b * b₁) * a₂ + (a * b₁ + b * (a₁ + b₁)) * b₂ ∧
      (a * a₂ + b * b₂) * b₁ + (a * b₂ + b * (a₂ + b₂)) * (a₁ + b₁) =
        (a * a₁ + b * b₁) * b₂ + (a * b₁ + b * (a₁ + b₁)) * (a₂ + b₂) := by decide
  obtain ⟨h1, h2⟩ := hid a b a₁ b₁ a₂ b₂
  rw [h1, h2]

theorem rho_inv_apply_apply (ρ : Representation (ZMod 2) Γ V) (g : Γ) (y : V) :
    ρ g⁻¹ (ρ g y) = y := by
  simp

theorem perfect_acts_trivially (ρ : Representation (ZMod 2) Γ V) {W : Submodule (ZMod 2) V}
    {x : V} {T : Module.End (ZMod 2) V}
    (hspan : ∀ y ∈ W, ∃ a b : ZMod 2, y = a • x + b • T x) (hx : x ∈ W)
    (hT2 : T (T x) = x + T x) (P : Subgroup Γ) (hperf : P ≤ ⁅P, P⁆)
    (hPW : ∀ p ∈ P, ∀ y ∈ W, ρ p y ∈ W) (hPT : ∀ p ∈ P, ∀ y ∈ W, ρ p (T y) = T (ρ p y)) :
    ∀ p ∈ P, ∀ y ∈ W, ρ p y = y := by
  let K : Subgroup Γ :=
    { carrier := {g | ∀ y ∈ W, ρ g y = y}
      mul_mem' := fun {g h} hg hh y hy => by
        rw [map_mul, Module.End.mul_apply, hh y hy, hg y hy]
      one_mem' := fun y _ => by simp
      inv_mem' := fun {g} hg y hy => by
        calc ρ g⁻¹ y = ρ g⁻¹ (ρ g y) := by rw [hg y hy]
          _ = y := rho_inv_apply_apply ρ g y }
  have hcomm : ⁅P, P⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂ y hy
    have hy₁ : ρ g₂⁻¹ y ∈ W := hPW g₂⁻¹ (P.inv_mem hg₂) y hy
    have hc := comm_on_block (A := ρ g₂) (B := ρ g₁⁻¹) hspan hx hT2 (hPW g₂ hg₂)
      (hPW g₁⁻¹ (P.inv_mem hg₁)) (hPT g₂ hg₂) (hPT g₁⁻¹ (P.inv_mem hg₁)) _ hy₁
    show ρ (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) y = y
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    rw [hc, rho_apply_inv_apply ρ g₂ y, rho_apply_inv_apply ρ g₁ y]
  intro p hp
  exact hcomm (hperf hp)

theorem list_prod_commutator_mem (P : Subgroup Γ) (l : List (Γ × Γ))
    (hl : ∀ q ∈ l, q.1 ∈ P ∧ q.2 ∈ P) :
    (l.map fun q => q.1 * q.2 * q.1⁻¹ * q.2⁻¹).prod ∈ ⁅P, P⁆ := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.commutator_mem_commutator (hl q hq).1 (hl q hq).2

theorem closure_le_commutator {S : Set Γ}
    (hS : ∀ s ∈ S, s ∈ ⁅Subgroup.closure S, Subgroup.closure S⁆) :
    Subgroup.closure S ≤ ⁅Subgroup.closure S, Subgroup.closure S⁆ :=
  (Subgroup.closure_le _).mpr hS

variable (ι : AddChar F3Vec Γ)

@[expose] def stabSubgroup (w : F3Vec) : Subgroup Γ where
  carrier := {g | ∃ A : Matrix (Fin 6) (Fin 6) (ZMod 3), ConjAct ι g A ∧ Matrix.vecMul w A = w}
  mul_mem' := by
    rintro g₁ g₂ ⟨A₁, h₁, hw₁⟩ ⟨A₂, h₂, hw₂⟩
    exact ⟨A₁ * A₂, h₁.mul h₂, by rw [← Matrix.vecMul_vecMul, hw₁, hw₂]⟩
  one_mem' := ⟨1, ConjAct.one, Matrix.vecMul_one w⟩
  inv_mem' := by
    rintro g ⟨A, h, hw⟩
    refine ⟨A⁻¹, h.inv, ?_⟩
    have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp h.isUnit
    calc Matrix.vecMul w A⁻¹ = Matrix.vecMul (Matrix.vecMul w A) A⁻¹ := by rw [hw]
      _ = w := by rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hdet, Matrix.vecMul_one]

theorem mem_stabSubgroup {w : F3Vec} {g : Γ} :
    g ∈ stabSubgroup ι w ↔
      ∃ A : Matrix (Fin 6) (Fin 6) (ZMod 3), ConjAct ι g A ∧ Matrix.vecMul w A = w := Iff.rfl

variable {ι}

theorem stab_apply_mem (ρ : Representation (ZMod 2) Γ V) {w₁ : F3Vec} {g : Γ}
    (hg : g ∈ stabSubgroup ι w₁) {y : V} (hy : y ∈ LinearMap.range (eK ρ ι w₁)) :
    ρ g y ∈ LinearMap.range (eK ρ ι w₁) := by
  obtain ⟨A, hA, hw⟩ := hg
  have h := range_eK_eq_map ρ hA (w := w₁) (w' := w₁) (c := 1) one_ne_zero
    (by rw [one_smul]; exact hw)
  rw [h]
  exact Submodule.mem_map_of_mem hy

theorem stab_apply_comm (ρ : Representation (ZMod 2) Γ V) {w₁ v₀ : F3Vec} {g : Γ}
    (hg : g ∈ stabSubgroup ι w₁) (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {y : V}
    (hy : y ∈ LinearMap.range (eK ρ ι w₁)) :
    ρ g (ρ (ι v₀) y) = ρ (ι v₀) (ρ g y) := by
  have hgy := stab_apply_mem ρ hg hy
  obtain ⟨A, hA, hw⟩ := hg
  have h1 : ρ g (ρ (ι v₀) y) = ρ (ι (A.mulVec v₀)) (ρ g y) := by
    have := LinearMap.congr_fun (congrArg ρ (hA.mul_apply v₀)) y
    simpa using this
  have hc : (w₁ ⬝ᵥ A.mulVec v₀) * (w₁ ⬝ᵥ v₀)⁻¹ = 1 := by
    rw [Matrix.dotProduct_mulVec, hw]
    exact mul_inv_cancel₀ hv₀
  have hval : (1 : ZMod 3).val = 1 := rfl
  rw [h1, apply_ι_of_mem_range_eK ρ ι hv₀ _ hgy, hc, hval, pow_one]

end Perfect


section PerfectBlock

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Γ V) (ι : AddChar F3Vec Γ)

theorem perfect_acts_trivially_on_block {w₁ v₀ : F3Vec}
    (hdim : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w₁)) = 2) (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0)
    {x : V} (hx : x ∈ LinearMap.range (eK ρ ι w₁)) (hx0 : x ≠ 0) (P : Subgroup Γ)
    (hPstab : P ≤ stabSubgroup ι w₁) (hperf : P ≤ ⁅P, P⁆) :
    ∀ p ∈ P, ∀ y ∈ LinearMap.range (eK ρ ι w₁), ρ p y = y :=
  perfect_acts_trivially ρ (W := LinearMap.range (eK ρ ι w₁)) (x := x) (T := ρ (ι v₀))
    (fun _ hy => exists_coeffs_of_mem_range_eK ρ ι hdim hv₀ hx hx0 hy) hx
    (apply_sq_of_mem_range_eK ρ ι hv₀ hx) P hperf
    (fun _ hp _ hy => stab_apply_mem ρ (hPstab hp) hy)
    (fun _ hp _ hy => stab_apply_comm ρ (hPstab hp) hv₀ hy)

end PerfectBlock

section Transfer

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) Γ V) (ι : AddChar F3Vec Γ)

@[expose] def coef (c : ZMod 3) : Fin 2 → ZMod 2 :=
  if c = 0 then ![1, 0] else if c = 1 then ![0, 1] else ![1, 1]

theorem pow_apply_eq_coef {T : Module.End (ZMod 2) V} {x : V} (hT2 : T (T x) = x + T x)
    (c : ZMod 3) : (T ^ c.val) x = coef c 0 • x + coef c 1 • T x := by
  rcases zmod_three_cases c with rfl | rfl | rfl
  · simp [coef]
  · have h1 : (1 : ZMod 3).val = 1 := rfl
    simp [coef, h1]
  · have h1 : (-1 : ZMod 3).val = 2 := rfl
    have h2 : ¬ ((-1 : ZMod 3) = 0) := by decide
    have h3 : ¬ ((-1 : ZMod 3) = 1) := by decide
    simp [coef, h1, h2, h3, pow_two, hT2]

@[expose] def fixSubgroup (x : V) : Subgroup Γ where
  carrier := {g | ρ g x = x}
  mul_mem' := fun {g h} hg hh => by
    show ρ (g * h) x = x
    rw [map_mul, Module.End.mul_apply, show ρ h x = x from hh, show ρ g x = x from hg]
  one_mem' := by simp
  inv_mem' := fun {g} hg => by
    show ρ g⁻¹ x = x
    calc ρ g⁻¹ x = ρ g⁻¹ (ρ g x) := by rw [show ρ g x = x from hg]
      _ = x := rho_inv_apply_apply ρ g x

theorem mem_fixSubgroup {x : V} {g : Γ} : g ∈ fixSubgroup ρ x ↔ ρ g x = x := Iff.rfl

theorem rho_apply_basis (b : Module.Basis (Fin 12 × Fin 2) (ZMod 2) V) {r : Fin 12 → Γ}
    {w₁ v₀ : F3Vec} (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {x : V}
    (hb : ∀ i j, b (i, j) = ρ (r i) ((ρ (ι v₀) ^ (j : ℕ)) x))
    (hx : x ∈ LinearMap.range (eK ρ ι w₁)) {n : Γ} {σ : Fin 12 → Fin 12}
    {u : Fin 12 → Fin 2 → F3Vec} {s : Fin 12 → Fin 2 → Γ}
    (hdec : ∀ (i : Fin 12) (j : Fin 2), n * r i * ι v₀ ^ (j : ℕ) = r (σ i) * ι (u i j) * s i j)
    (hs : ∀ i j, ρ (s i j) x = x) (i : Fin 12) (j : Fin 2) :
    ρ n (b (i, j)) =
      coef ((w₁ ⬝ᵥ u i j) * (w₁ ⬝ᵥ v₀)⁻¹) 0 • b (σ i, 0) +
        coef ((w₁ ⬝ᵥ u i j) * (w₁ ⬝ᵥ v₀)⁻¹) 1 • b (σ i, 1) := by
  have hT2 := apply_sq_of_mem_range_eK ρ ι hv₀ hx
  have h1 : ρ n (b (i, j)) = ρ (r (σ i)) ((ρ (ι v₀) ^ ((w₁ ⬝ᵥ u i j) * (w₁ ⬝ᵥ v₀)⁻¹).val) x) := by
    rw [hb i j]
    have e : ρ n (ρ (r i) ((ρ (ι v₀) ^ (j : ℕ)) x)) = ρ (n * r i * ι v₀ ^ (j : ℕ)) x := by
      rw [map_mul, map_mul, map_pow, Module.End.mul_apply, Module.End.mul_apply]
    rw [e, hdec i j, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hs i j,
      apply_ι_of_mem_range_eK ρ ι hv₀ (u i j) hx]
  rw [h1, pow_apply_eq_coef hT2, map_add, map_smul, map_smul, hb (σ i) 0, hb (σ i) 1]
  simp

variable {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V'] (ρ' : Representation (ZMod 2) Γ V')

theorem transfer (b : Module.Basis (Fin 12 × Fin 2) (ZMod 2) V)
    (b' : Module.Basis (Fin 12 × Fin 2) (ZMod 2) V') {r : Fin 12 → Γ} {w₁ v₀ : F3Vec}
    (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {x : V} {x' : V'}
    (hb : ∀ i j, b (i, j) = ρ (r i) ((ρ (ι v₀) ^ (j : ℕ)) x))
    (hb' : ∀ i j, b' (i, j) = ρ' (r i) ((ρ' (ι v₀) ^ (j : ℕ)) x'))
    (hx : x ∈ LinearMap.range (eK ρ ι w₁)) (hx' : x' ∈ LinearMap.range (eK ρ' ι w₁))
    {n : Γ} {σ : Fin 12 → Fin 12} {u : Fin 12 → Fin 2 → F3Vec} {s : Fin 12 → Fin 2 → Γ}
    (hdec : ∀ (i : Fin 12) (j : Fin 2), n * r i * ι v₀ ^ (j : ℕ) = r (σ i) * ι (u i j) * s i j)
    (hs : ∀ i j, ρ (s i j) x = x) (hs' : ∀ i j, ρ' (s i j) x' = x') (v : V) :
    b.equiv b' (Equiv.refl _) (ρ n v) = ρ' n (b.equiv b' (Equiv.refl _) v) := by
  have key : (b.equiv b' (Equiv.refl _) : V →ₗ[ZMod 2] V').comp (ρ n) =
      (ρ' n).comp (b.equiv b' (Equiv.refl _) : V →ₗ[ZMod 2] V') := by
    apply b.ext
    rintro ⟨i, j⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.refl_apply]
    rw [rho_apply_basis ρ ι b hv₀ hb hx hdec hs i j, map_add, map_smul, map_smul,
      Module.Basis.equiv_apply, Module.Basis.equiv_apply,
      rho_apply_basis ρ' ι b' hv₀ hb' hx' hdec hs' i j]
    simp
  exact LinearMap.congr_fun key v

theorem transfer_of_decomposition (b : Module.Basis (Fin 12 × Fin 2) (ZMod 2) V)
    (b' : Module.Basis (Fin 12 × Fin 2) (ZMod 2) V') {r : Fin 12 → Γ} {w₁ v₀ : F3Vec}
    (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {x : V} {x' : V'}
    (hb : ∀ i j, b (i, j) = ρ (r i) ((ρ (ι v₀) ^ (j : ℕ)) x))
    (hb' : ∀ i j, b' (i, j) = ρ' (r i) ((ρ' (ι v₀) ^ (j : ℕ)) x'))
    (hx : x ∈ LinearMap.range (eK ρ ι w₁)) (hx' : x' ∈ LinearMap.range (eK ρ' ι w₁))
    {n : Γ} {σ : Fin 12 → Fin 12} {u : Fin 12 → Fin 2 → F3Vec} {t : Γ}
    {ε : Fin 12 → Fin 2 → ℕ} {p : Fin 12 → Fin 2 → Γ} (P : Subgroup Γ)
    (hdec : ∀ (i : Fin 12) (j : Fin 2),
      n * r i * ι v₀ ^ (j : ℕ) = r (σ i) * ι (u i j) * t ^ ε i j * p i j)
    (hp : ∀ i j, p i j ∈ P) (hP : ∀ q ∈ P, ρ q x = x) (hP' : ∀ q ∈ P, ρ' q x' = x')
    (ht : ρ t x = x) (ht' : ρ' t x' = x') (v : V) :
    b.equiv b' (Equiv.refl _) (ρ n v) = ρ' n (b.equiv b' (Equiv.refl _) v) := by
  refine transfer ρ ι ρ' b b' hv₀ hb hb' hx hx' (s := fun i j => t ^ ε i j * p i j)
    (fun i j => by rw [hdec i j, mul_assoc]) (fun i j => ?_) (fun i j => ?_) v
  · have h1 : t ^ ε i j ∈ fixSubgroup ρ x := (fixSubgroup ρ x).pow_mem ht _
    have h2 : p i j ∈ fixSubgroup ρ x := hP _ (hp i j)
    exact (fixSubgroup ρ x).mul_mem h1 h2
  · have h1 : t ^ ε i j ∈ fixSubgroup ρ' x' := (fixSubgroup ρ' x').pow_mem ht' _
    have h2 : p i j ∈ fixSubgroup ρ' x' := hP' _ (hp i j)
    exact (fixSubgroup ρ' x').mul_mem h1 h2

end Transfer

section Glue

variable {Γ : Type*} [Group Γ] {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V'] [Module (ZMod 2) V'] (ρ : Representation (ZMod 2) Γ V)
  (ρ' : Representation (ZMod 2) Γ V')

@[expose] def intertwiners (f : V →ₗ[ZMod 2] V') : Subgroup Γ where
  carrier := {g | ∀ v, f (ρ g v) = ρ' g (f v)}
  mul_mem' := fun {g h} hg hh v => by
    have hg' : ∀ v, f (ρ g v) = ρ' g (f v) := hg
    have hh' : ∀ v, f (ρ h v) = ρ' h (f v) := hh
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg', hh']
  one_mem' := fun v => by simp
  inv_mem' := fun {g} hg v => by
    have hg' : ∀ v, f (ρ g v) = ρ' g (f v) := hg
    calc f (ρ g⁻¹ v) = ρ' g⁻¹ (ρ' g (f (ρ g⁻¹ v))) := (rho_inv_apply_apply ρ' g _).symm
      _ = ρ' g⁻¹ (f (ρ g (ρ g⁻¹ v))) := by rw [hg']
      _ = ρ' g⁻¹ (f v) := by rw [rho_apply_inv_apply ρ g v]

theorem mem_intertwiners {f : V →ₗ[ZMod 2] V'} {g : Γ} :
    g ∈ intertwiners ρ ρ' f ↔ ∀ v, f (ρ g v) = ρ' g (f v) := Iff.rfl

theorem intertwine_of_mem_closure (f : V →ₗ[ZMod 2] V') {S : Set Γ}
    (hS : ∀ g ∈ S, ∀ v, f (ρ g v) = ρ' g (f v)) {g : Γ} (hg : g ∈ Subgroup.closure S) (v : V) :
    f (ρ g v) = ρ' g (f v) :=
  (Subgroup.closure_le (intertwiners ρ ρ' f)).mpr hS hg v

theorem intertwine_of_glue (f : V ≃ₗ[ZMod 2] V') {N : Subgroup Γ}
    (hN : ∀ n ∈ N, ∀ v, f (ρ n v) = ρ' n (f v)) {g : Γ} (hg7 : g ^ 7 = 1) {κ : Type*}
    (x : κ → Γ) (hxN : ∀ k, x k ∈ N) (hyN : ∀ k, g * x k * g⁻¹ ∈ N)
    (huniq : ∀ M : Module.End (ZMod 2) V',
      (∀ k, M * ρ' (x k) = ρ' (g * x k * g⁻¹) * M) → IsUnit M → M ^ 7 = 1 → M = ρ' g)
    (v : V) : f (ρ g v) = ρ' g (f v) := by
  set M : Module.End (ZMod 2) V' := f.conjRingEquiv (ρ g) with hM
  have hMapp : ∀ v', M v' = f (ρ g (f.symm v')) := fun v' => rfl
  have hcomm : ∀ k, M * ρ' (x k) = ρ' (g * x k * g⁻¹) * M := by
    intro k
    ext v'
    simp only [Module.End.mul_apply, hMapp]
    have h1 : f.symm (ρ' (x k) v') = ρ (x k) (f.symm v') := by
      have := hN (x k) (hxN k) (f.symm v')
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this, LinearEquiv.symm_apply_apply]
    have h2 : ρ g (ρ (x k) (f.symm v')) = ρ (g * x k * g⁻¹) (ρ g (f.symm v')) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [h1, h2, hN _ (hyN k)]
  have hunit : IsUnit M := ((Group.isUnit g).map ρ).map f.conjRingEquiv
  have hpow : M ^ 7 = 1 := by
    rw [hM, ← map_pow, ← map_pow, hg7, map_one, map_one]
  have := LinearMap.congr_fun (huniq M hcomm hunit hpow) (f v)
  rw [hMapp, LinearEquiv.symm_apply_apply] at this
  exact this

theorem exists_equiv_of_closure_eq_top (f : V ≃ₗ[ZMod 2] V') {S : Set Γ}
    (hS : Subgroup.closure S = ⊤) (h : ∀ s ∈ S, ∀ v, f (ρ s v) = ρ' s (f v)) :
    ∃ ψ : V ≃ₗ[ZMod 2] V', ∀ g v, ψ (ρ g v) = ρ' g (ψ v) :=
  ⟨f, fun g v =>
    intertwine_of_mem_closure ρ ρ' (f : V →ₗ[ZMod 2] V') h (hS ▸ Subgroup.mem_top g) v⟩

theorem exists_equiv_of_glue (f : V ≃ₗ[ZMod 2] V') {N : Subgroup Γ}
    (hN : ∀ n ∈ N, ∀ v, f (ρ n v) = ρ' n (f v)) {g : Γ} (hg7 : g ^ 7 = 1) {κ : Type*}
    (x : κ → Γ) (hxN : ∀ k, x k ∈ N) (hyN : ∀ k, g * x k * g⁻¹ ∈ N)
    (huniq : ∀ M : Module.End (ZMod 2) V',
      (∀ k, M * ρ' (x k) = ρ' (g * x k * g⁻¹) * M) → IsUnit M → M ^ 7 = 1 → M = ρ' g)
    (hgen : Subgroup.closure ((N : Set Γ) ∪ {g}) = ⊤) :
    ∃ ψ : V ≃ₗ[ZMod 2] V', ∀ γ v, ψ (ρ γ v) = ρ' γ (ψ v) := by
  refine exists_equiv_of_closure_eq_top ρ ρ' f hgen ?_
  rintro s (hs | hs)
  · exact hN s hs
  · rw [Set.mem_singleton_iff.mp hs]
    exact intertwine_of_glue ρ ρ' f hN hg7 x hxN hyN huniq

theorem huniq_of_matrix {d : ℕ} (ρ' : Representation (ZMod 2) Γ (Fin d → ZMod 2))
    (G : Γ → Matrix (Fin d) (Fin d) (ZMod 2)) (hG : ∀ γ, ρ' γ = Matrix.mulVecLin (G γ))
    {κ : Type*} (y : κ → Γ) (g : Γ)
    (h : ∀ M : Matrix (Fin d) (Fin d) (ZMod 2),
      (∀ k, M * G (y k) = G (g * y k * g⁻¹) * M) → IsUnit M → M ^ 7 = 1 → M = G g)
    (M : Module.End (ZMod 2) (Fin d → ZMod 2))
    (hM : ∀ k, M * ρ' (y k) = ρ' (g * y k * g⁻¹) * M) (hu : IsUnit M) (h7 : M ^ 7 = 1) :
    M = ρ' g := by
  let e := LinearMap.toMatrixAlgEquiv' (R := ZMod 2) (n := Fin d)
  have he : ∀ γ, e (ρ' γ) = G γ := fun γ => by
    rw [hG γ]
    exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' (G γ)
  have h1 : e M = G g := by
    refine h (e M) (fun k => ?_) (hu.map e) ?_
    · rw [← he (y k), ← he (g * y k * g⁻¹), ← map_mul, ← map_mul, hM k]
    · rw [← map_pow, h7, map_one]
  rw [← he g] at h1
  exact e.injective h1

end Glue


section Capstone

variable {Γ : Type*} [Group Γ] {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V'] [Module (ZMod 2) V']

theorem exists_equiv_of_block_data (ρ : Representation (ZMod 2) Γ V)
    (ρ' : Representation (ZMod 2) Γ V') (ι : AddChar F3Vec Γ)
    (hV : Module.finrank (ZMod 2) V = 24) (hV' : Module.finrank (ZMod 2) V' = 24)
    (hnt : ∃ v, ρ (ι v) ≠ 1) (hnt' : ∃ v, ρ' (ι v) ≠ 1)
    {ν : Type*} (n : ν → Γ) (Amat : ν → Matrix (Fin 6) (Fin 6) (ZMod 3))
    (hn : ∀ m, ConjAct ι (n m) (Amat m)) {R : Finset F3Vec} (hR : IsLineReps R)
    (cls : F3Vec → Fin 3) (h0 : (R.filter fun w => cls w = 0).card = 12)
    (h1 : (R.filter fun w => cls w = 1).card = 132)
    (h2 : (R.filter fun w => cls w = 2).card = 220)
    (horbit : ∀ w ∈ R, ∀ w' ∈ R, cls w = cls w' → Relation.EqvGen
      (fun a b : F3Vec => ∃ m, ∃ c : ZMod 3, c ≠ 0 ∧ Matrix.vecMul b (Amat m) = c • a) w w')
    (w : Fin 12 → F3Vec) (hinj : Function.Injective w) (hwR : ∀ i, w i ∈ R)
    (hwcls : ∀ i, cls (w i) = 0) {w₁ v₀ : F3Vec} (hw₁R : w₁ ∈ R) (hw₁cls : cls w₁ = 0)
    (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) (r : Fin 12 → Γ) (Ar : Fin 12 → Matrix (Fin 6) (Fin 6) (ZMod 3))
    (cr : Fin 12 → ZMod 3) (hr : ∀ i, ConjAct ι (r i) (Ar i)) (hcr : ∀ i, cr i ≠ 0)
    (hwA : ∀ i, Matrix.vecMul (w i) (Ar i) = cr i • w₁) (t : Γ)
    (At : Matrix (Fin 6) (Fin 6) (ZMod 3)) (ct : ZMod 3) (ht : ConjAct ι t At) (ht2 : t * t = 1)
    (hct : ct ≠ 0) (hwt : Matrix.vecMul w₁ At = ct • w₁) (P : Subgroup Γ)
    (hPstab : P ≤ stabSubgroup ι w₁) (hperf : P ≤ ⁅P, P⁆) (σ : ν → Fin 12 → Fin 12)
    (u : ν → Fin 12 → Fin 2 → F3Vec) (ε : ν → Fin 12 → Fin 2 → ℕ) (p : ν → Fin 12 → Fin 2 → Γ)
    (hdec : ∀ (m : ν) (i : Fin 12) (j : Fin 2),
      n m * r i * ι v₀ ^ (j : ℕ) = r (σ m i) * ι (u m i j) * t ^ ε m i j * p m i j)
    (hp : ∀ m i j, p m i j ∈ P) {g : Γ} (hg7 : g ^ 7 = 1) {κ : Type*} (y : κ → Γ)
    (hyN : ∀ k, y k ∈ Subgroup.closure (Set.range n))
    (hyN' : ∀ k, g * y k * g⁻¹ ∈ Subgroup.closure (Set.range n))
    (huniq : ∀ M : Module.End (ZMod 2) V',
      (∀ k, M * ρ' (y k) = ρ' (g * y k * g⁻¹) * M) → IsUnit M → M ^ 7 = 1 → M = ρ' g)
    (hgen : Subgroup.closure (Set.range n ∪ {g}) = ⊤) :
    ∃ ψ : V ≃ₗ[ZMod 2] V', ∀ γ v, ψ (ρ γ v) = ρ' γ (ψ v) := by
  classical
  have : FiniteDimensional (ZMod 2) V := finiteDimensional_of_finrank_eq_24 hV
  have : FiniteDimensional (ZMod 2) V' := finiteDimensional_of_finrank_eq_24 hV'
  have hconst : ∀ w ∈ R, ∀ w' ∈ R, cls w = cls w' →
      Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
        Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w')) := fun w hw w' hw' hc =>
    finrank_range_eK_eq_of_eqvGen ρ n Amat hn (horbit w hw w' hw' hc)
  have hconst' : ∀ w ∈ R, ∀ w' ∈ R, cls w = cls w' →
      Module.finrank (ZMod 2) (LinearMap.range (eK ρ' ι w)) =
        Module.finrank (ZMod 2) (LinearMap.range (eK ρ' ι w')) := fun w hw w' hw' hc =>
    finrank_range_eK_eq_of_eqvGen ρ' n Amat hn (horbit w hw w' hw' hc)
  obtain ⟨-, hdim⟩ := piE_eq_zero_and_finrank_eK ρ ι hV hR cls h0 h1 h2 hconst hnt
  obtain ⟨-, hdim'⟩ := piE_eq_zero_and_finrank_eK ρ' ι hV' hR cls h0 h1 h2 hconst' hnt'
  have hd₁ : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w₁)) = 2 := by
    rw [hdim w₁ hw₁R]; simp [hw₁cls]
  have hd₁' : Module.finrank (ZMod 2) (LinearMap.range (eK ρ' ι w₁)) = 2 := by
    rw [hdim' w₁ hw₁R]; simp [hw₁cls]
  obtain ⟨x, hx, hx0, htx⟩ := exists_fixed_mem_range_eK ρ ι ht ht2 hct hwt (fun h => by
    rw [h] at hd₁; simp at hd₁)
  obtain ⟨x', hx', hx0', htx'⟩ := exists_fixed_mem_range_eK ρ' ι ht ht2 hct hwt (fun h => by
    rw [h] at hd₁'; simp at hd₁')
  obtain ⟨b, hb⟩ := exists_basis_of_orbits ρ ι hV hR cls h0 h1 h2 hconst hnt w hinj hwR hwcls
    hw₁R hw₁cls hv₀ hx hx0 r Ar cr hr hcr hwA
  obtain ⟨b', hb'⟩ := exists_basis_of_orbits ρ' ι hV' hR cls h0 h1 h2 hconst' hnt' w hinj hwR
    hwcls hw₁R hw₁cls hv₀ hx' hx0' r Ar cr hr hcr hwA
  have hP := perfect_acts_trivially_on_block ρ ι hd₁ hv₀ hx hx0 P hPstab hperf
  have hP' := perfect_acts_trivially_on_block ρ' ι hd₁' hv₀ hx' hx0' P hPstab hperf
  let f : V ≃ₗ[ZMod 2] V' := b.equiv b' (Equiv.refl _)
  have hgen_n : ∀ m v, f (ρ (n m) v) = ρ' (n m) (f v) := fun m v =>
    transfer_of_decomposition ρ ι ρ' b b' hv₀ hb hb' hx hx' (σ := σ m) (u := u m) (ε := ε m)
      (p := p m) P (hdec m) (hp m) (fun q hq => hP q hq x hx) (fun q hq => hP' q hq x' hx')
      htx htx' v
  have hN : ∀ q ∈ Subgroup.closure (Set.range n), ∀ v, f (ρ q v) = ρ' q (f v) :=
    fun q hq v => intertwine_of_mem_closure ρ ρ' (f : V →ₗ[ZMod 2] V') (S := Set.range n)
      (by rintro _ ⟨m, rfl⟩ v; exact hgen_n m v) hq v
  have hg : ∀ v, f (ρ g v) = ρ' g (f v) :=
    intertwine_of_glue ρ ρ' f hN hg7 y hyN hyN' huniq
  refine exists_equiv_of_closure_eq_top ρ ρ' f hgen ?_
  rintro s (⟨m, rfl⟩ | hs)
  · exact hgen_n m
  · rw [Set.mem_singleton_iff.mp hs]
    exact hg

end Capstone

end CFSG.Monster.GMS.Griess13
