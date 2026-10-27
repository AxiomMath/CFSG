module

public import CFSG.Quasithin.Background.F7TwoInvSeed

public section

namespace CFSG.Quasithin.F7Two

variable {L M : Type*} [Group L] [Group M]

theorem invAutGen_of_hom_class (f : L →* M) {a b : L}
    (hab : Subgroup.closure {a, b} = ⊤) {A B D r u : M} (hA : f a = A) (hB : f b = B)
    {d c : L} (hD : f d = D) {sa ma sb mb : ℕ} (hma : Odd ma) (hmb : Odd mb)
    (h1a : ((D * r * D⁻¹) * A * (D * r * D⁻¹)⁻¹ * A⁻¹) ^ (2 ^ sa * ma) = 1)
    (h2a : ((D * r * D⁻¹) * A * (D * r * D⁻¹)⁻¹ * A⁻¹) ^ 2 ^ sa ≠ 1)
    (h1b : ((D * r * D⁻¹) * B * (D * r * D⁻¹)⁻¹ * B⁻¹) ^ (2 ^ sb * mb) = 1)
    (h2b : ((D * r * D⁻¹) * B * (D * r * D⁻¹)⁻¹ * B⁻¹) ^ 2 ^ sb ≠ 1)
    {α : MulAut L} (hα : ∀ x : L, f (α x) = u * f x * u⁻¹) (hu : u = f c * r * (f c)⁻¹) :
    InvAutGen L α := by
  obtain ⟨g, hg⟩ : ∃ g : L, g = d * c⁻¹ := ⟨_, rfl⟩
  obtain ⟨α', hα'def⟩ : ∃ α' : MulAut L, α' = MulAut.conj g * α * (MulAut.conj g)⁻¹ := ⟨_, rfl⟩
  have hfg : f g = D * (f c)⁻¹ := by rw [hg, map_mul, map_inv, hD]
  have he : f g * u * (f g)⁻¹ = D * r * D⁻¹ := by
    rw [hfg, hu]
    group
  have hα' : ∀ x : L, f (α' x) = (D * r * D⁻¹) * f x * (D * r * D⁻¹)⁻¹ := by
    intro x
    have h1 : f (α' x) = (f g * u * (f g)⁻¹) * f x * (f g * u * (f g)⁻¹)⁻¹ := by
      simp only [hα'def, conj_conj_inv_apply, map_mul, map_inv, hα]
      group
    rw [h1, he]
  have key : ∀ (x : L) (X : M) (s m : ℕ), f x = X → Odd m →
      ((D * r * D⁻¹) * X * (D * r * D⁻¹)⁻¹ * X⁻¹) ^ (2 ^ s * m) = 1 →
      ((D * r * D⁻¹) * X * (D * r * D⁻¹)⁻¹ * X⁻¹) ^ 2 ^ s ≠ 1 → x ∈ invXiAut α' := by
    intro x X s m hx hm h1 h2
    rw [mem_invXiAut_iff]
    intro n hn
    have hn' := congrArg f hn
    rw [map_pow, map_one, map_mul, map_inv, hα', hx] at hn'
    exact pow_two_pow_ne_one_of_pow hm h1 h2 n hn'
  have ha : a ∈ invXiAut α' := key a A sa ma hA hma h1a h2a
  have hb : b ∈ invXiAut α' := key b B sb mb hB hmb h1b h2b
  have h := invAutGen_of_seeds hab (fun x hx => Or.inl (by
    rcases hx with rfl | rfl
    · exact ha
    · exact hb)) ⟨a, by simp, ha⟩
  rw [hα'def] at h
  exact (InvAutGen.conj_iff (MulAut.conj g) α).2 h

theorem invAutGen_of_inner_classes {M : Type*} [Group M] (N : Subgroup M) (reps : Set M)
    (hZ : Subgroup.center N = ⊥) (hin : ∀ φ : MulAut N, ∃ x : N, MulAut.conj x = φ)
    (hcov : ∀ u ∈ N, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ N, u = c * r * c⁻¹)
    (hcls : ∀ r ∈ reps, ∀ x c : N, (x : M) = c * r * (c : M)⁻¹ →
      InvAutGen N (MulAut.conj x)) :
    ∀ φ : MulAut N, φ * φ = 1 → φ ≠ 1 → InvAutGen N φ := by
  refine invAutGen_of_inner_conj hZ hin fun x hxx hx1 => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (x : M) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← Subgroup.coe_mul, hxx, Subgroup.coe_one]
    · intro h
      exact hx1 (Subtype.ext h)
  obtain ⟨r, hr, c, hc, hxc⟩ := hcov x x.2 hord
  exact hcls r hr x ⟨c, hc⟩ hxc

end CFSG.Quasithin.F7Two
