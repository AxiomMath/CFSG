module

public import CFSG.Sporadic.Co1.Cover.Elementary

public section

namespace CFSG.Sporadic.Co1.Cover

open Matrix

structure EquivSection {n : ℕ} {P T : Type*} [Group P] [Group T] (E : CentralExt n T)
    (ρ : P →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))) where
  γ : P →* MulAut T
  fix_z : ∀ p, γ p E.z = E.z
  act : ∀ p t, E.ψ (γ p t) = Multiplicative.ofAdd (ρ p (Multiplicative.toAdd (E.ψ t)))
  s₀ : Multiplicative (Fin n → ZMod 2) →* T
  sec : ∀ v, E.ψ (s₀ v) = v

namespace EquivSection

variable {n : ℕ} {P T : Type*} [Group P] [Group T] {E : CentralExt n T}
  {ρ : P →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))} (Q : EquivSection E ρ)

theorem fix_zz (p : P) (k : ZMod 2) : Q.γ p (E.zz k) = E.zz k := by
  show Q.γ p (E.z ^ k.val) = E.z ^ k.val
  rw [map_pow, Q.fix_z]

theorem exists_delta (p : P) (x : Fin n → ZMod 2) :
    ∃! k : ZMod 2, Q.γ p (Q.s₀ (Multiplicative.ofAdd x)) =
      Q.s₀ (Multiplicative.ofAdd (ρ p x)) * E.zz k := by
  apply E.exists_unique_zz
  rw [Q.act, Q.sec, Q.sec]
  simp

noncomputable def delta (p : P) (x : Fin n → ZMod 2) : ZMod 2 := (Q.exists_delta p x).exists.choose

theorem gamma_s (p : P) (x : Fin n → ZMod 2) :
    Q.γ p (Q.s₀ (Multiplicative.ofAdd x)) =
      Q.s₀ (Multiplicative.ofAdd (ρ p x)) * E.zz (Q.delta p x) :=
  (Q.exists_delta p x).exists.choose_spec

theorem delta_unique {p : P} {x : Fin n → ZMod 2} {k : ZMod 2}
    (h : Q.γ p (Q.s₀ (Multiplicative.ofAdd x)) =
      Q.s₀ (Multiplicative.ofAdd (ρ p x)) * E.zz k) : Q.delta p x = k :=
  (Q.exists_delta p x).unique (Q.gamma_s p x) h

theorem delta_add (p : P) (x y : Fin n → ZMod 2) :
    Q.delta p (x + y) = Q.delta p x + Q.delta p y := by
  apply Q.delta_unique
  have h1 := Q.gamma_s p x
  have h2 := Q.gamma_s p y
  have hxy : Multiplicative.ofAdd (x + y) =
      Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl
  have hxy' : Multiplicative.ofAdd (ρ p (x + y)) =
      Multiplicative.ofAdd (ρ p x) * Multiplicative.ofAdd (ρ p y) := by
    rw [map_add]; rfl
  rw [hxy, hxy', map_mul, map_mul, map_mul, h1, h2, E.zz_add]
  calc Q.s₀ (Multiplicative.ofAdd (ρ p x)) * E.zz (Q.delta p x) *
        (Q.s₀ (Multiplicative.ofAdd (ρ p y)) * E.zz (Q.delta p y))
      = Q.s₀ (Multiplicative.ofAdd (ρ p x)) *
        (E.zz (Q.delta p x) * Q.s₀ (Multiplicative.ofAdd (ρ p y))) *
          E.zz (Q.delta p y) := by simp only [mul_assoc]
    _ = _ := by rw [E.zz_central]; simp only [mul_assoc]

theorem delta_mul (p q : P) (x : Fin n → ZMod 2) :
    Q.delta (p * q) x = Q.delta p (ρ q x) + Q.delta q x := by
  apply Q.delta_unique
  have h1 := Q.gamma_s q x
  have h2 := Q.gamma_s p (ρ q x)
  have hρ : ρ (p * q) x = ρ p (ρ q x) := by rw [map_mul]; rfl
  have hγ : Q.γ (p * q) (Q.s₀ (Multiplicative.ofAdd x)) =
      Q.γ p (Q.γ q (Q.s₀ (Multiplicative.ofAdd x))) := by rw [map_mul]; rfl
  rw [hγ, h1, map_mul, Q.fix_zz, h2, hρ, E.zz_add]
  simp only [mul_assoc]

theorem delta_zero (p : P) : Q.delta p 0 = 0 := by
  have h := Q.delta_add p 0 0
  rw [add_zero] at h
  revert h
  generalize Q.delta p 0 = x
  revert x
  decide

theorem dot_of_additive (f : (Fin n → ZMod 2) → ZMod 2) (h0 : f 0 = 0)
    (hadd : ∀ x y, f (x + y) = f x + f y) (x : Fin n → ZMod 2) :
    f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
  let fl : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := AddMonoidHom.toZModLinearMap 2 ⟨⟨f, h0⟩, hadd⟩
  have hfl : ∀ v, fl v = f v := fun v => rfl
  rw [← hfl, LinearMap.pi_apply_eq_sum_univ fl x]
  simp only [dotProduct, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun j => if i = j then (1 : ZMod 2) else 0) = Pi.single i 1 := by
    funext j
    rw [Pi.single_apply]
    by_cases h : j = i
    · subst h; simp
    · have h' : ¬ i = j := fun e => h e.symm
      simp [h, h']
  rw [this, hfl, mul_comm]

noncomputable def lvec (p : P) : Fin n → ZMod 2 := fun i => Q.delta p (Pi.single i 1)

theorem delta_eq_dot (p : P) (x : Fin n → ZMod 2) : Q.delta p x = Q.lvec p ⬝ᵥ x :=
  dot_of_additive (Q.delta p) (Q.delta_zero p) (Q.delta_add p) x

theorem lvec_cocycle (p q : P) (x : Fin n → ZMod 2) :
    Q.lvec (p * q) ⬝ᵥ x = Q.lvec p ⬝ᵥ ρ q x + Q.lvec q ⬝ᵥ x := by
  rw [← Q.delta_eq_dot, ← Q.delta_eq_dot, ← Q.delta_eq_dot, Q.delta_mul]

end EquivSection

section Adjust

variable {n : ℕ} {P T : Type*} [Group P] [Group T] {E : CentralExt n T}
  {ρ : P →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))} (Q : EquivSection E ρ)

theorem zmod_two_add_self (y : ZMod 2) : y + y = 0 := CharTwo.add_self_eq_zero y

theorem exists_equivariant_section (a b : P) (hgen : Subgroup.closure ({a, b} : Set P) = ⊤)
    (x₀ : Fin n → ZMod 2) (hx₀ : ρ a x₀ = x₀)
    (hfix : Q.γ a (Q.s₀ (Multiplicative.ofAdd x₀)) = Q.s₀ (Multiplicative.ofAdd x₀))
    (hfox : ∀ l : P → (Fin n → ZMod 2),
      (∀ p q x, l (p * q) ⬝ᵥ x = l p ⬝ᵥ ρ q x + l q ⬝ᵥ x) → l a ⬝ᵥ x₀ = 0 →
        ∃ φ : Fin n → ZMod 2, (∀ x, l a ⬝ᵥ x = φ ⬝ᵥ ρ a x + φ ⬝ᵥ x) ∧
          (∀ x, l b ⬝ᵥ x = φ ⬝ᵥ ρ b x + φ ⬝ᵥ x)) :
    ∃ s' : Multiplicative (Fin n → ZMod 2) →* T, (∀ v, E.ψ (s' v) = v) ∧
      ∀ p v, Q.γ p (s' v) = s' (Multiplicative.ofAdd (ρ p (Multiplicative.toAdd v))) := by
  have hδ : Q.delta a x₀ = 0 := by
    have h := Q.gamma_s a x₀
    rw [hx₀, hfix] at h
    have h2 : E.zz (Q.delta a x₀) = E.zz 0 := by
      rw [E.zz_zero]
      exact (mul_eq_left.1 h.symm)
    exact E.zz_injective h2
  obtain ⟨φ₀, hφa, hφb⟩ := hfox Q.lvec Q.lvec_cocycle (by rw [← Q.delta_eq_dot, hδ])
  let s' : Multiplicative (Fin n → ZMod 2) →* T :=
    { toFun := fun v => Q.s₀ v * E.zz (φ₀ ⬝ᵥ Multiplicative.toAdd v)
      map_one' := by simp [E.zz_zero]
      map_mul' := fun v w => by
        have : φ₀ ⬝ᵥ Multiplicative.toAdd (v * w) =
            φ₀ ⬝ᵥ Multiplicative.toAdd v + φ₀ ⬝ᵥ Multiplicative.toAdd w := by
          rw [toAdd_mul, dotProduct_add]
        rw [this, E.zz_add, map_mul]
        symm
        calc Q.s₀ v * E.zz (φ₀ ⬝ᵥ Multiplicative.toAdd v) *
              (Q.s₀ w * E.zz (φ₀ ⬝ᵥ Multiplicative.toAdd w))
            = Q.s₀ v * (E.zz (φ₀ ⬝ᵥ Multiplicative.toAdd v) * Q.s₀ w) *
              E.zz (φ₀ ⬝ᵥ Multiplicative.toAdd w) := by simp only [mul_assoc]
          _ = Q.s₀ v * (Q.s₀ w * E.zz (φ₀ ⬝ᵥ Multiplicative.toAdd v)) *
              E.zz (φ₀ ⬝ᵥ Multiplicative.toAdd w) := by rw [E.zz_central]
          _ = _ := by simp only [mul_assoc] }
  have hs'v : ∀ v, s' v = Q.s₀ v * E.zz (φ₀ ⬝ᵥ Multiplicative.toAdd v) := fun v => rfl
  have hψ : ∀ v, E.ψ (s' v) = v := by
    intro v
    rw [hs'v, map_mul, Q.sec, (E.mem_ker_iff.2 ⟨_, rfl⟩ : E.zz _ ∈ E.ψ.ker)]
    simp
  have hgenr : ∀ c : P, (∀ x, Q.lvec c ⬝ᵥ x = φ₀ ⬝ᵥ ρ c x + φ₀ ⬝ᵥ x) →
      ∀ v, Q.γ c (s' v) = s' (Multiplicative.ofAdd (ρ c (Multiplicative.toAdd v))) := by
    intro c hc v
    obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective v
    rw [hs'v, hs'v, map_mul, Q.fix_zz, Q.gamma_s]
    simp only [toAdd_ofAdd]
    rw [mul_assoc, ← E.zz_add]
    congr 2
    rw [Q.delta_eq_dot, hc x, add_assoc, zmod_two_add_self, add_zero]
  let H : Subgroup P :=
    { carrier := {p | ∀ v, Q.γ p (s' v) =
        s' (Multiplicative.ofAdd (ρ p (Multiplicative.toAdd v)))}
      mul_mem' := fun {p q} hp hq v => by
        have h1 : Q.γ (p * q) (s' v) = Q.γ p (Q.γ q (s' v)) := by rw [map_mul]; rfl
        rw [h1, hq v, hp]
        congr 1
        rw [map_mul]; rfl
      one_mem' := fun v => by simp
      inv_mem' := fun {p} hp v => by
        have h1 := hp (Multiplicative.ofAdd (ρ p⁻¹ (Multiplicative.toAdd v)))
        have h2 : ρ p (ρ p⁻¹ (Multiplicative.toAdd v)) = Multiplicative.toAdd v := by
          rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
        simp only [toAdd_ofAdd, h2, ofAdd_toAdd] at h1
        have h3 : Q.γ p⁻¹ (Q.γ p (s' (Multiplicative.ofAdd (ρ p⁻¹ (Multiplicative.toAdd v))))) =
            s' (Multiplicative.ofAdd (ρ p⁻¹ (Multiplicative.toAdd v))) := by
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        rw [h1] at h3
        exact h3 }
  have hH : H = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro c hc
    rcases hc with rfl | rfl
    · exact hgenr _ hφa
    · exact hgenr _ hφb
  exact ⟨s', hψ, fun p v => (hH ▸ Subgroup.mem_top p : p ∈ H) v⟩

end Adjust

end CFSG.Sporadic.Co1.Cover
