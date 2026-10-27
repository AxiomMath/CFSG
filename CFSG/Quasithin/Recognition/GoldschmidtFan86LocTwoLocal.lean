module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocTwoLocalFin
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Open

section Generic

variable {S C : Type} [Group S] [Group C]

theorem inl_mem_normalizer (P : S → Prop) (hPc : ∀ v σ, P v → P (σ * v * σ⁻¹))
    (hF1 : ∀ ξ : S, ξ ^ 3 = 1 → ξ ≠ 1 → ∀ K : Subgroup S, IsPGroup 2 K →
      (∀ k ∈ K, ξ * k * ξ⁻¹ ∈ K) → ∀ k ∈ K, P k)
    (hF2 : ∀ ξ : S, ξ ^ 3 = 1 → ξ ≠ 1 → ∀ v w : S, P v → v ≠ 1 → P w → w ≠ 1 →
      ∃ j : ℕ, ξ ^ j * v * (ξ ^ j)⁻¹ = w)
    {Q : Subgroup (S × C)} (hQ : IsPGroup 2 Q) {ξ : S} (h3 : ξ ^ 3 = 1) (h1 : ξ ≠ 1)
    (hξ : ((ξ, 1) : S × C) ∈ Subgroup.normalizer (Q : Set (S × C))) (σ : S) :
    ((σ, 1) : S × C) ∈ Subgroup.normalizer (Q : Set (S × C)) := by
  have hK2 : IsPGroup 2 (Q.map (MonoidHom.fst S C)) := by
    rintro ⟨k, q, hq, rfl⟩
    obtain ⟨m, hm⟩ := hQ ⟨q, hq⟩
    refine ⟨m, Subtype.ext ?_⟩
    have := congrArg (fun z : Q => (z : S × C).1) hm
    simpa using this
  have hKN : ∀ k ∈ Q.map (MonoidHom.fst S C), ξ * k * ξ⁻¹ ∈ Q.map (MonoidHom.fst S C) := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨(ξ, 1) * q * (ξ, 1)⁻¹, (Subgroup.mem_normalizer_iff.1 hξ q).1 hq, by simp⟩
  have hPQ : ∀ q ∈ Q, P q.1 := fun q hq => hF1 ξ h3 h1 _ hK2 hKN q.1 ⟨q, hq, rfl⟩
  have hconj : ∀ τ : S, ∀ q ∈ Q, ((τ, 1) : S × C) * q * ((τ, 1) : S × C)⁻¹ ∈ Q := by
    intro τ q hq
    obtain ⟨v, d⟩ := q
    have hv : P v := hPQ (v, d) hq
    have e : ((τ, 1) : S × C) * (v, d) * ((τ, 1) : S × C)⁻¹ = (τ * v * τ⁻¹, d) := by simp
    rw [e]
    by_cases hv1 : v = 1
    · subst hv1
      simpa using hq
    · obtain ⟨j, hj⟩ := hF2 ξ h3 h1 v (τ * v * τ⁻¹) hv hv1 (hPc v τ hv) (conj_ne_one hv1 τ)
      have hxj : ((ξ, 1) : S × C) ^ j ∈ Subgroup.normalizer (Q : Set (S × C)) :=
        Subgroup.pow_mem _ hξ j
      have h := (Subgroup.mem_normalizer_iff.1 hxj (v, d)).1 hq
      have e2 : ((ξ, 1) : S × C) ^ j * (v, d) * (((ξ, 1) : S × C) ^ j)⁻¹ =
          (ξ ^ j * v * (ξ ^ j)⁻¹, d) := by simp
      rw [e2, hj] at h
      exact h
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj σ h, fun h' => ?_⟩
  have h2 := hconj σ⁻¹ _ h'
  obtain ⟨a, b⟩ := h
  simpa [mul_assoc] using h2

theorem nonempty_mulEquiv_prod {M : Subgroup (S × C)} (hS : ∀ σ : S, ((σ, 1) : S × C) ∈ M) :
    ∃ C₀ : Subgroup C, Nonempty (M ≃* S × C₀) := by
  have key : ∀ m : M, ((1 : S), (m : S × C).2) ∈ M := by
    rintro ⟨⟨σ, c⟩, hm⟩
    have h := M.mul_mem (M.inv_mem (hS σ)) hm
    simpa using h
  refine ⟨M.comap (MonoidHom.inr S C), ⟨{
    toFun := fun m => ((m : S × C).1, ⟨(m : S × C).2, key m⟩)
    invFun := fun p => ⟨(p.1, (p.2 : C)), by
      have h := M.mul_mem (hS p.1) (show ((1 : S), (p.2 : C)) ∈ M from p.2.2)
      simpa using h⟩
    left_inv := fun m => by ext <;> rfl
    right_inv := fun p => by ext <;> rfl
    map_mul' := fun a b => by ext <;> rfl }⟩⟩

theorem exists_mulEquiv_prod_of_facts [Finite S] [Finite C] (hC : IsPGroup 2 C) (P : S → Prop)
    (hPc : ∀ v σ, P v → P (σ * v * σ⁻¹))
    (hF1 : ∀ ξ : S, ξ ^ 3 = 1 → ξ ≠ 1 → ∀ K : Subgroup S, IsPGroup 2 K →
      (∀ k ∈ K, ξ * k * ξ⁻¹ ∈ K) → ∀ k ∈ K, P k)
    (hF2 : ∀ ξ : S, ξ ^ 3 = 1 → ξ ≠ 1 → ∀ v w : S, P v → v ≠ 1 → P w → w ≠ 1 →
      ∃ j : ℕ, ξ ^ j * v * (ξ ^ j)⁻¹ = w)
    {M : Subgroup (S × C)} (hM : IsTwoLocal M) (h3 : 3 ∣ Nat.card M) :
    ∃ C₀ : Subgroup C, Nonempty (M ≃* S × C₀) := by
  obtain ⟨Q, -, hQ, rfl⟩ := hM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx : orderOf (y : S × C) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hx3 : (y : S × C) ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
  obtain ⟨ξ, c, hxy⟩ : ∃ (ξ : S) (c : C), (y : S × C) = (ξ, c) := ⟨_, _, rfl⟩
  rw [hxy] at hx hx3
  have hcube : ξ ^ 3 = 1 ∧ c ^ 3 = 1 := by simpa [Prod.ext_iff] using hx3
  have hc : c = 1 := eq_one_of_pow_three_eq_one hC hcube.2
  have hξ1 : ξ ≠ 1 := by
    intro h
    have h1 : orderOf ((ξ, c) : S × C) = 1 := by
      rw [h, hc]
      exact orderOf_one
    omega
  have hξ : ((ξ, 1) : S × C) ∈ Subgroup.normalizer (Q : Set (S × C)) := by
    have := y.2
    rw [hxy, hc] at this
    exact this
  exact nonempty_mulEquiv_prod fun σ =>
    inl_mem_normalizer P hPc hF1 hF2 hQ hcube.1 hξ1 hξ σ

end Generic

theorem isTwoLocal_perm_prod {n : ℕ} (hn : n = 3 ∨ n = 4) {C : Type} [Group C] [Finite C]
    (hC : IsPGroup 2 C) {M : Subgroup (Equiv.Perm (Fin n) × C)} (hM : IsTwoLocal M)
    (h3 : 3 ∣ Nat.card M) :
    ∃ C₀ : Subgroup C, Nonempty (M ≃* (Equiv.Perm (Fin 3) × C₀)) ∨
      Nonempty (M ≃* (Equiv.Perm (Fin 4) × C₀)) := by
  rcases hn with rfl | rfl
  · obtain ⟨C₀, e⟩ := exists_mulEquiv_prod_of_facts hC (fun v : Equiv.Perm (Fin 3) => v = 1)
      (fun v σ hv => by subst hv; simp)
      (fun ξ h3 h1 K hK hN => eq_one_of_normalized_three h3 h1 hK hN)
      (fun ξ _ _ v w hv hv1 _ _ => absurd hv hv1) hM h3
    exact ⟨C₀, Or.inl e⟩
  · obtain ⟨C₀, e⟩ := exists_mulEquiv_prod_of_facts hC IsKlein4
      (fun v σ hv => isKlein4_conj hv σ)
      (fun ξ h3 h1 K hK hN => isKlein4_of_normalized_four h3 h1 hK hN)
      (fun ξ h3 h1 v w hv hv1 hw hw1 => exists_conj_eq_four h3 h1 hv hv1 hw hw1) hM h3
    exact ⟨C₀, Or.inr e⟩

end CFSG.Quasithin.Fan86
