module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {X : Type*} [Group X]

theorem ne_of_three {N₁ N₂ N₃ : Subgroup X} {ρ z : X} (h3 : N₃.index = 2) (hρ : ρ ∉ N₁)
    (hz : z ∉ N₂) (hρz : ρ * z ∉ N₃) : N₁ ≠ N₂ ∨ N₂ ≠ N₃ := by
  by_contra h
  push Not at h
  obtain ⟨rfl, rfl⟩ := h
  exact hρz ((Subgroup.mul_mem_iff_of_index_two h3).2 (iff_of_false hρ hz))

theorem index_inf_eq_four [Finite X] {A B : Subgroup X} [A.Normal] (hA : A.index = 2)
    (hB : B.index = 2) (hne : A ≠ B) : (A ⊓ B).index = 4 := by
  have h1 : (A ⊓ B).index = A.relIndex B * B.index := Subgroup.index_inf
  have hdvd : A.relIndex B ∣ 2 := hA ▸ Subgroup.relIndex_dvd_index_of_normal A B
  have hne1 : A.relIndex B ≠ 1 := by
    intro h
    have hBA : B ≤ A := Subgroup.relIndex_eq_one.1 h
    apply hne
    have h2 := Subgroup.relIndex_mul_relIndex B A ⊤ hBA le_top
    rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, hA, hB] at h2
    have h3 : B.relIndex A = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h3) hBA
  have : A.relIndex B = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne1
    · exact h
  rw [h1, this, hB]

theorem mem_of_odd_orderOf {H N : Subgroup X} (hsq : ∀ x ∈ H, x ^ 2 ∈ N) {x : X} (hxH : x ∈ H)
    (hx : Odd (orderOf x)) : x ∈ N := by
  obtain ⟨k, hk⟩ := hx
  have h1 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have h2 : x = (x ^ 2) ^ (k + 1) := by
    calc x = x ^ (2 * k + 1) * x := by rw [h1, one_mul]
      _ = (x ^ 2) ^ (k + 1) := by rw [← pow_succ, ← pow_mul]; congr 1
  rw [h2]
  exact N.pow_mem (hsq x hxH) _

theorem normal_closure_odd :
    (Subgroup.closure {x : X | Odd (orderOf x)}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ?_
    show Odd (orderOf (g * x * g⁻¹))
    have : orderOf (g * x * g⁻¹) = orderOf x :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    rw [this]; exact hx
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]; exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem hx

theorem le_closure_odd_of_card [Finite X] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {S : Subgroup X} (hS : IsPGroup p S) : S ≤ Subgroup.closure {x : X | Odd (orderOf x)} := by
  intro s hs
  refine Subgroup.subset_closure ?_
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hs' : s ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hd : orderOf s ∣ p ^ k := orderOf_dvd_of_pow_eq_one hs'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hd
  show Odd (orderOf s)
  rw [hj]
  exact (hp.eq_two_or_odd'.resolve_left hodd).pow

theorem prime_dvd_index_closure_odd [Finite X] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hdvd : p ∣ (Subgroup.closure {x : X | Odd (orderOf x)}).index) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S⟩ : Nonempty (Sylow p X) := inferInstance
  have hS : (S : Subgroup X) ≤ Subgroup.closure {x : X | Odd (orderOf x)} :=
    le_closure_odd_of_card hp hodd S.isPGroup'
  exact S.not_dvd_index ((hdvd.trans (Subgroup.index_dvd_of_le hS)))

end CFSG.Quasithin.H13.F431.U42Aut
