module

public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix

variable {G V : Type*} [Group G]

def layer (g y : G) (h : List G) : List G :=
  h.flatMap fun k => [g * k, g * y * k, g * (y * y) * k]

def prodList (y : G) (g₀ g₁ g₂ g₃ : G) (h₀ h₁ h₂ h₃ : List G) : List G :=
  layer g₀ y h₀ ++ layer g₁ y h₁ ++ layer g₂ y h₂ ++ layer g₃ y h₃

def ParityCert (enc : G → ℕ) (T : List G) : Prop :=
  (T.map enc).count (enc 1) % 2 = 1 ∧
    ∀ c ∈ T.map enc, c ≠ enc 1 → (T.map enc).count c % 2 = 0

section Trace

variable [Group V]

def tr (ρ : G →* MulAut V) (y : G) (h : List G) (v : V) : V :=
  (h.map fun k => ρ k v * ρ (y * k) v * ρ (y * y * k) v).prod

theorem ρ_apply_ρ (ρ : G →* MulAut V) (g k : G) (v : V) : ρ g (ρ k v) = ρ (g * k) v := by
  rw [map_mul, MulAut.mul_apply]

theorem apply_tr (ρ : G →* MulAut V) (y g : G) (v : V) (h : List G) :
    ρ g (tr ρ y h v) = ((layer g y h).map fun τ => ρ τ v).prod := by
  induction h with
  | nil => simp [tr, layer]
  | cons k h ih =>
    have ih' : ρ g (tr ρ y h v) = ((layer g y h).map fun τ => ρ τ v).prod := ih
    have e1 : tr ρ y (k :: h) v =
        (ρ k v * ρ (y * k) v * ρ (y * y * k) v) * tr ρ y h v := by
      simp [tr]
    have e2 : layer g y (k :: h) = [g * k, g * y * k, g * (y * y) * k] ++ layer g y h := by
      simp [layer]
    rw [e1, e2, map_mul, ih', map_mul, map_mul, ρ_apply_ρ, ρ_apply_ρ, ρ_apply_ρ]
    simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc]

end Trace

section Comm

variable [Group V]

theorem tr_fixed (hcomm : ∀ a b : V, a * b = b * a) (ρ : G →* MulAut V) {y : G}
    (hy : y * y * y = 1) (h : List G) (v : V) : ρ y (tr ρ y h v) = tr ρ y h v := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  unfold tr
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  have h1 : ρ y (ρ k v) = ρ (y * k) v := ρ_apply_ρ ρ y k v
  have h2 : ρ y (ρ (y * k) v) = ρ (y * y * k) v := by rw [ρ_apply_ρ, mul_assoc]
  have h3 : ρ y (ρ (y * y * k) v) = ρ k v := by
    rw [ρ_apply_ρ, ← mul_assoc, ← mul_assoc, hy, one_mul]
  show ρ y (ρ k v * ρ (y * k) v * ρ (y * y * k) v) = ρ k v * ρ (y * k) v * ρ (y * y * k) v
  rw [map_mul (ρ y), map_mul (ρ y), h1, h2, h3]
  exact (mul_rotate _ _ _).symm

theorem prod_map_eq_of_parity [DecidableEq G] (hcomm : ∀ a b : V, a * b = b * a)
    (hV : ∀ v : V, v * v = 1) (f : G → V) (T : List G) (hodd : T.count 1 % 2 = 1)
    (heven : ∀ x ∈ T, x ≠ 1 → T.count x % 2 = 0) : (T.map f).prod = f 1 := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  have hsq : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  have hpow : ∀ (v : V) (n : ℕ), n % 2 = 0 → v ^ n = 1 := by
    intro v n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    rw [pow_mul, hsq, one_pow]
  rw [Finset.prod_list_map_count, Finset.prod_eq_single (1 : G)]
  · obtain ⟨m, hm⟩ : ∃ m, T.count 1 = 2 * m + 1 := ⟨T.count 1 / 2, by omega⟩
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
  · intro x hx hx1
    exact hpow _ _ (heven x (List.mem_toFinset.1 hx) hx1)
  · intro h1
    exfalso
    apply h1
    rw [List.mem_toFinset]
    refine List.count_pos_iff.1 ?_
    omega

end Comm

theorem card_le_pow_four [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hV : ∀ v : V, v * v = 1) (ρ : G →* MulAut V) {y : G} (hy : y * y * y = 1)
    (g₀ g₁ g₂ g₃ : G) (h₀ h₁ h₂ h₃ : List G) (enc : G → ℕ) (henc : Function.Injective enc)
    (hT : ParityCert enc (prodList y g₀ g₁ g₂ g₃ h₀ h₁ h₂ h₃)) :
    Nat.card V ≤ Nat.card {v : V // ρ y v = v} ^ 4 := by
  classical
  set T := prodList y g₀ g₁ g₂ g₃ h₀ h₁ h₂ h₃ with hTdef
  have hodd : T.count 1 % 2 = 1 := by
    have := hT.1
    rwa [List.count_map_of_injective T enc henc] at this
  have heven : ∀ x ∈ T, x ≠ 1 → T.count x % 2 = 0 := by
    intro x hx hx1
    have := hT.2 (enc x) (List.mem_map_of_mem hx) (fun h => hx1 (henc h))
    rwa [List.count_map_of_injective T enc henc] at this
  let F : {v : V // ρ y v = v} × {v : V // ρ y v = v} × {v : V // ρ y v = v} ×
      {v : V // ρ y v = v} → V :=
    fun p => ρ g₀ p.1 * ρ g₁ p.2.1 * ρ g₂ p.2.2.1 * ρ g₃ p.2.2.2
  have hsurj : Function.Surjective F := by
    intro v
    refine ⟨(⟨tr ρ y h₀ v, tr_fixed hcomm ρ hy h₀ v⟩, ⟨tr ρ y h₁ v, tr_fixed hcomm ρ hy h₁ v⟩,
      ⟨tr ρ y h₂ v, tr_fixed hcomm ρ hy h₂ v⟩, ⟨tr ρ y h₃ v, tr_fixed hcomm ρ hy h₃ v⟩), ?_⟩
    show ρ g₀ (tr ρ y h₀ v) * ρ g₁ (tr ρ y h₁ v) * ρ g₂ (tr ρ y h₂ v) *
      ρ g₃ (tr ρ y h₃ v) = v
    rw [apply_tr, apply_tr, apply_tr, apply_tr, ← List.prod_append, ← List.prod_append,
      ← List.prod_append, ← List.map_append, ← List.map_append, ← List.map_append]
    have := prod_map_eq_of_parity hcomm hV (fun τ => ρ τ v) T hodd heven
    rw [hTdef, prodList] at this
    rw [this]
    simp
  calc Nat.card V ≤ Nat.card ({v : V // ρ y v = v} × {v : V // ρ y v = v} ×
        {v : V // ρ y v = v} × {v : V // ρ y v = v}) := Nat.card_le_card_of_surjective F hsurj
    _ = Nat.card {v : V // ρ y v = v} ^ 4 := by
        simp only [Nat.card_prod]
        ring

end CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix
