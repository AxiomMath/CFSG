module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

section Nk

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem s16c1G_add_self (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have h : (2 : ZMod 2) = 0 := by decide
  rw [h, zero_smul]

private theorem s16c1G_zmod_two (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

@[expose] def s16c1G_nk (φ : V →ₗ[ZMod 2] ZMod 2) (z x : V) : V :=
  if φ x = 0 then x else x + z

variable {φ : V →ₗ[ZMod 2] ZMod 2} {z : V}

theorem s16c1G_nk_eq_or (x : V) : s16c1G_nk φ z x = x ∨ s16c1G_nk φ z x = x + z := by
  unfold s16c1G_nk
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem s16c1G_nk_mem (hφ : φ z = 1) (x : V) : φ (s16c1G_nk φ z x) = 0 := by
  unfold s16c1G_nk
  split_ifs with h
  · exact h
  · rw [map_add, hφ]
    rcases s16c1G_zmod_two (φ x) with h0 | h1
    · exact absurd h0 h
    · rw [h1]
      decide

theorem s16c1G_nk_of_ker {x : V} (h : φ x = 0) : s16c1G_nk φ z x = x := by
  unfold s16c1G_nk
  rw [if_pos h]

theorem s16c1G_nk_add (hφ : φ z = 1) (x : V) : s16c1G_nk φ z (x + z) = s16c1G_nk φ z x := by
  rcases s16c1G_zmod_two (φ x) with h0 | h1
  · have h1 : φ (x + z) ≠ 0 := by
      rw [map_add, h0, hφ]
      decide
    unfold s16c1G_nk
    rw [if_neg h1, if_pos h0, add_assoc, s16c1G_add_self, add_zero]
  · have h0 : φ (x + z) = 0 := by
      rw [map_add, h1, hφ]
      decide
    have h1' : φ x ≠ 0 := by
      rw [h1]
      decide
    unfold s16c1G_nk
    rw [if_pos h0, if_neg h1']

theorem s16c1G_nk_eq_nk_iff (hφ : φ z = 1) (x y : V) :
    s16c1G_nk φ z x = s16c1G_nk φ z y ↔ x = y ∨ x = y + z := by
  constructor
  · intro h
    rcases s16c1G_nk_eq_or (φ := φ) (z := z) x with hx | hx <;>
      rcases s16c1G_nk_eq_or (φ := φ) (z := z) y with hy | hy
    · exact Or.inl (hx.symm.trans (h.trans hy))
    · refine Or.inr ?_
      rw [← hy, ← h, hx]
    · refine Or.inr ?_
      have h2 : x + z = y := by rw [← hx, h, hy]
      rw [← h2, add_assoc, s16c1G_add_self, add_zero]
    · refine Or.inl ?_
      have h2 : x + z = y + z := by rw [← hx, h, hy]
      exact add_right_cancel h2
  · rintro (rfl | rfl)
    · rfl
    · exact s16c1G_nk_add hφ y

theorem s16c1G_nk_map (hφ : φ z = 1) (g : V ≃ₗ[ZMod 2] V) (hg : g z = z) (y : V) :
    s16c1G_nk φ z (g (s16c1G_nk φ z y)) = s16c1G_nk φ z (g y) := by
  rcases s16c1G_nk_eq_or (φ := φ) (z := z) y with h | h
  · rw [h]
  · rw [h, map_add, hg]
    exact s16c1G_nk_add hφ (g y)

end Nk

section Act

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem s16c1G_stab_apply {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {z : V}
    (g : ↥(MulAction.stabilizer Γ z)) : (g.1.1 : V ≃ₗ[ZMod 2] V) z = z :=
  MulAction.mem_stabilizer_iff.1 g.2

variable (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (z : V) (φ : V →ₗ[ZMod 2] ZMod 2) (hφ : φ z = 1)
  (P : V → Prop) (hP1 : ∀ x, P x → P (x + z))
  (hPg : ∀ g ∈ Γ, (g : V ≃ₗ[ZMod 2] V) z = z → ∀ x, P x → P (g x))

@[expose] def s16c1G_pairFun (g : ↥(MulAction.stabilizer Γ z)) (x : {x : V // P x ∧ φ x = 0}) :
    {x : V // P x ∧ φ x = 0} :=
  ⟨s16c1G_nk φ z ((g.1.1 : V ≃ₗ[ZMod 2] V) x.1), by
    have hPx : P ((g.1.1 : V ≃ₗ[ZMod 2] V) x.1) := hPg g.1.1 g.1.2 (s16c1G_stab_apply g) x.1 x.2.1
    refine ⟨?_, s16c1G_nk_mem hφ _⟩
    rcases s16c1G_nk_eq_or (φ := φ) (z := z) ((g.1.1 : V ≃ₗ[ZMod 2] V) x.1) with h | h
    · rw [h]; exact hPx
    · rw [h]; exact hP1 _ hPx⟩

theorem s16c1G_pairFun_one (x : {x : V // P x ∧ φ x = 0}) :
    s16c1G_pairFun Γ z φ hφ P hP1 hPg 1 x = x :=
  Subtype.ext (s16c1G_nk_of_ker x.2.2)

theorem s16c1G_pairFun_mul (g h : ↥(MulAction.stabilizer Γ z)) (x : {x : V // P x ∧ φ x = 0}) :
    s16c1G_pairFun Γ z φ hφ P hP1 hPg (g * h) x =
      s16c1G_pairFun Γ z φ hφ P hP1 hPg g (s16c1G_pairFun Γ z φ hφ P hP1 hPg h x) := by
  refine Subtype.ext ?_
  exact (s16c1G_nk_map hφ g.1.1 (s16c1G_stab_apply g) _).symm

@[expose] def s16c1G_pairAct :
    ↥(MulAction.stabilizer Γ z) →* Equiv.Perm {x : V // P x ∧ φ x = 0} where
  toFun g :=
    { toFun := s16c1G_pairFun Γ z φ hφ P hP1 hPg g
      invFun := s16c1G_pairFun Γ z φ hφ P hP1 hPg g⁻¹
      left_inv := fun x => by
        rw [← s16c1G_pairFun_mul, inv_mul_cancel, s16c1G_pairFun_one]
      right_inv := fun x => by
        rw [← s16c1G_pairFun_mul, mul_inv_cancel, s16c1G_pairFun_one] }
  map_one' := Equiv.ext fun x => s16c1G_pairFun_one Γ z φ hφ P hP1 hPg x
  map_mul' := fun g h => Equiv.ext fun x => s16c1G_pairFun_mul Γ z φ hφ P hP1 hPg g h x

theorem s16c1G_mem_ker_pairAct_iff (g : ↥(MulAction.stabilizer Γ z)) :
    g ∈ (s16c1G_pairAct Γ z φ hφ P hP1 hPg).ker ↔
      ∀ x, P x → (g.1.1 : V ≃ₗ[ZMod 2] V) x = x ∨ (g.1.1 : V ≃ₗ[ZMod 2] V) x = x + z := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x hx
    have hx₀P : P (s16c1G_nk φ z x) := by
      rcases s16c1G_nk_eq_or (φ := φ) (z := z) x with h' | h'
      · rw [h']; exact hx
      · rw [h']; exact hP1 _ hx
    let x₀ : {x : V // P x ∧ φ x = 0} := ⟨s16c1G_nk φ z x, hx₀P, s16c1G_nk_mem hφ x⟩
    have h1 : s16c1G_nk φ z ((g.1.1 : V ≃ₗ[ZMod 2] V) x₀.1) = x₀.1 := by
      have := congrArg Subtype.val (Equiv.congr_fun h x₀)
      exact this
    have h2 : s16c1G_nk φ z ((g.1.1 : V ≃ₗ[ZMod 2] V) x) = s16c1G_nk φ z x := by
      rw [← s16c1G_nk_map hφ g.1.1 (s16c1G_stab_apply g) x]
      exact h1
    exact (s16c1G_nk_eq_nk_iff hφ _ _).1 h2
  · intro h
    refine Equiv.ext fun x => Subtype.ext ?_
    have h1 := (s16c1G_nk_eq_nk_iff hφ ((g.1.1 : V ≃ₗ[ZMod 2] V) x.1) x.1).2 (h x.1 x.2.1)
    exact h1.trans (s16c1G_nk_of_ker x.2.2)

end Act

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
