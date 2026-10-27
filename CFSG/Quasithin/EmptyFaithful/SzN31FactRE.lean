module

public import CFSG.Quasithin.EmptyFaithful.SzN31FactRD

public section

namespace CFSG.Quasithin.SzN31

section FactRE

variable {p : ℕ} {Q : Type*} [Group Q]

@[expose] def omegaOne (p : ℕ) (N : Subgroup Q) (hN : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) : Subgroup Q where
  carrier := {x | x ∈ N ∧ x ^ p = 1}
  mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ =>
    ⟨N.mul_mem ha hb, by rw [Commute.mul_pow (hN a ha b hb), ha', hb', one_mul]⟩
  one_mem' := ⟨N.one_mem, one_pow p⟩
  inv_mem' := fun ⟨ha, ha'⟩ => ⟨N.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩

theorem invol_eq_one_of_fixed_omegaOne (hp : p.Prime) (hp2 : p ≠ 2) (hQ : IsPGroup p Q) (σ : MulAut Q)
    (hσ : σ * σ = 1) {N : Subgroup Q} (hNn : N.Normal) (hNi : ∀ x ∈ N, σ x ∈ N)
    (hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hNC : ∀ y : Q, (∀ n ∈ N, y * n = n * y) → y ∈ N)
    (hfix : ∀ x ∈ omegaOne p N hNc, σ x = x) : σ = 1 := by
  have hN' : IsPGroup p N := hQ.to_subgroup N
  have h1 : ∀ x ∈ N, σ x = x :=
    invol_fixed_of_fixed_order_p hp hp2 σ hσ N hN' hNi (fun z hz hzp => hfix z ⟨hz, hzp⟩)
  exact invol_eq_one_of_fixed_selfCentralizing hp hp2 σ hσ N hN' hNC h1

end FactRE

theorem card_le_four_of_selfCentralizing {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q)
    (hrank : ∀ E : Subgroup Q, (∀ x ∈ E, x ^ p = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      Nat.card E ≤ p ^ 2)
    {Bh : Type} [Group Bh] [Finite Bh] (act : Bh →* MulAut Q) (hB : ∀ b : Bh, b * b = 1)
    {N : Subgroup Q} (hNn : N.Normal) (hNi : ∀ b : Bh, ∀ x ∈ N, act b x ∈ N)
    (hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hNC : ∀ y : Q, (∀ n ∈ N, y * n = n * y) → y ∈ N) :
    Nat.card Bh ≤ 4 * Nat.card act.ker := by
  have hEc : ∀ x ∈ omegaOne p N hNc, ∀ y ∈ omegaOne p N hNc, x * y = y * x :=
    fun x hx y hy => hNc x hx.1 y hy.1
  have hEe : ∀ x ∈ omegaOne p N hNc, x ^ p = 1 := fun x hx => hx.2
  have hEi : ∀ b : Bh, ∀ x ∈ omegaOne p N hNc, act b x ∈ omegaOne p N hNc :=
    fun b x hx => ⟨hNi b x hx.1, by rw [← map_pow, hx.2, map_one]⟩
  obtain ⟨g, hg⟩ := sign_bound hp hp2 act hB hEc hEe (hrank _ hEe hEc) hEi
  have hbb : ∀ b : Bh, act b * act b = 1 := fun b => by rw [← map_mul, hB b, map_one]
  have hL5 : ∀ b : Bh, (∀ x ∈ omegaOne p N hNc, act b x = x) → act b = 1 := fun b hb =>
    invol_eq_one_of_fixed_omegaOne hp hp2 hQ (act b) (hbb b) hNn (hNi b) hNc hNC hb
  have hinj : Function.Injective (fun σ : act.range => g (σ : MulAut Q)) := by
    rintro ⟨_, b, rfl⟩ ⟨_, c, rfl⟩ h
    have hag := hg b c h
    have h1 : act (b * c) = 1 := hL5 (b * c) (fun x hx => by
      rw [map_mul, MulAut.mul_apply, ← hag x hx, act_invol act hB b x])
    have h2 : act b * act c = 1 := by rwa [map_mul] at h1
    have h3 : act c = act b := by
      have := inv_eq_of_mul_eq_one_right h2
      rw [← this, inv_eq_of_mul_eq_one_right (hbb b)]
    exact Subtype.ext h3.symm
  have hrange : Nat.card act.range ≤ 4 :=
    calc Nat.card act.range ≤ Nat.card (Bool × Bool) := Nat.card_le_card_of_injective _ hinj
      _ = 4 := by simp
  calc Nat.card Bh = Nat.card act.ker * Nat.card act.range :=
        (Subgroup.card_ker_mul_card_range act).symm
    _ ≤ Nat.card act.ker * 4 := Nat.mul_le_mul_left _ hrange
    _ = 4 * Nat.card act.ker := mul_comm _ _

end CFSG.Quasithin.SzN31
