module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP1

public section

namespace CFSG.Quasithin.H13

open Subgroup
open scoped commutatorElement

theorem a5_normal_two_elements_bot_cv (N : Subgroup (alternatingGroup (Fin 5))) [N.Normal]
    (hN : ∀ a ∈ N, ∃ n : ℕ, a ^ (2 ^ n) = 1) : N = ⊥ := by
  let a3 : alternatingGroup (Fin 5) :=
    ⟨List.formPerm [0, 1, 2], Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
  have ha3 : a3 ^ 3 = 1 := Subtype.ext (by decide)
  have ha3ne : a3 ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    revert this
    decide
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have ha : a3 ∈ N := by
      rw [h]
      exact mem_top _
    obtain ⟨n, hn⟩ := hN a3 ha
    have hcop : Nat.gcd 3 (2 ^ n) = 1 :=
      Nat.Coprime.pow_right n (by norm_num)
    have h1 : a3 ^ (Nat.gcd 3 (2 ^ n)) = 1 := pow_gcd_eq_one.2 ⟨ha3, hn⟩
    rw [hcop, pow_one] at h1
    exact ha3ne h1

theorem exists_lift_a5_cv {X Y : Type} [Group X] [Group Y] (f : X →* Y) (hf : Function.Surjective f)
    (hker : ∀ x ∈ f.ker, ∃ n : ℕ, x ^ (2 ^ n) = 1)
    (φ : X →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ) :
    ∃ ψ : Y →* alternatingGroup (Fin 5), Function.Surjective ψ ∧ ∀ x, ψ (f x) = φ x := by
  haveI hN₀n : (f.ker.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  have hN₀2 : ∀ a ∈ f.ker.map φ, ∃ n : ℕ, a ^ (2 ^ n) = 1 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨n, hn⟩ := hker x hx
    refine ⟨n, ?_⟩
    rw [← map_pow, hn, map_one]
  have hN₀bot : f.ker.map φ = ⊥ := a5_normal_two_elements_bot_cv (f.ker.map φ) hN₀2
  have hle : f.ker ≤ φ.ker := by
    intro x hx
    have hmem : φ x ∈ f.ker.map φ := Subgroup.mem_map_of_mem φ hx
    rw [hN₀bot, Subgroup.mem_bot] at hmem
    exact MonoidHom.mem_ker.2 hmem
  let g₀ : {g : X →* alternatingGroup (Fin 5) // f.ker ≤ g.ker} := ⟨φ, hle⟩
  have hψf : ∀ x, (MonoidHom.liftOfSurjective f hf g₀) (f x) = φ x :=
    fun x => MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) g₀ x
  refine ⟨MonoidHom.liftOfSurjective f hf g₀, ?_, hψf⟩
  intro a
  obtain ⟨x, rfl⟩ := hφ a
  exact ⟨f x, hψf x⟩

theorem perfect_le_of_index_two_cv {R : Type} [Group R] (N : Subgroup R) [N.Normal]
    (hN : N.index = 2) (B : Subgroup R) (hB : ⁅B, B⁆ = B) : B ≤ N := by
  have hcard : Nat.card (R ⧸ N) = 2 := hN
  have hsq : ∀ x : R ⧸ N, x * x = 1 := by
    intro x
    have h := pow_card_eq_one' (G := R ⧸ N) (x := x)
    rw [hcard, pow_two] at h
    exact h
  have hcomm : ∀ x y : R ⧸ N, x * y = y * x := by
    intro x y
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq (x * y))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right (hsq y), inv_eq_of_mul_eq_one_right (hsq x)]
  have hcomm' : ∀ a b : R, ⁅a, b⁆ ∈ N := by
    intro a b
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have hle : ⁅B, B⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    exact hcomm' a b
  calc B = ⁅B, B⁆ := hB.symm
    _ ≤ N := hle

end CFSG.Quasithin.H13
