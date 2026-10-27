module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open

section Exp3

variable {W : Type*} [Group W]

theorem zpow_eq_of_emod {x : W} (hx : x ^ 3 = 1) {m n : ℤ} (h : m % 3 = n % 3) :
    x ^ m = x ^ n := by
  have h3 : x ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hx]
  rw [← Int.emod_add_mul_ediv m 3, ← Int.emod_add_mul_ediv n 3, zpow_add, zpow_add, zpow_mul,
    zpow_mul, h3, one_zpow, one_zpow, h]

theorem eq_of_mem_zpowers_of_cube {a b : W} (ha : a ^ 3 = 1) (hb : b ∈ Subgroup.zpowers a) :
    b = 1 ∨ b = a ∨ b = a * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [zpow_eq_of_emod ha (Int.emod_emod k 3).symm]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h1 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · rw [h, zpow_zero]
    exact Or.inl rfl
  · rw [h, zpow_one]
    exact Or.inr (Or.inl rfl)
  · rw [h, zpow_two]
    exact Or.inr (Or.inr rfl)

theorem fix_of_mem_zpowers {γ : W →* W} (hγ : ∀ w, γ (γ (γ w)) = w) {a : W} (ha : a ^ 3 = 1)
    (h : γ a ∈ Subgroup.zpowers a) : γ a = a := by
  rcases eq_of_mem_zpowers_of_cube ha h with h | h | h
  · have h1 : a = 1 := by rw [← hγ a, h, map_one, map_one]
    rw [h, h1]
  · exact h
  · have h2 : γ (γ a) = a := by
      rw [h, map_mul, h]
      calc a * a * (a * a) = a ^ 3 * a := by rw [pow_three]; simp only [mul_assoc]
        _ = a := by rw [ha, one_mul]
    have h3 : a * a = a := by
      calc a * a = γ a := h.symm
        _ = γ (γ (γ a)) := by rw [h2]
        _ = a := hγ a
    have h1 : a = 1 := by simpa using h3
    rw [h, h1, mul_one]

end Exp3

section Comm3

variable {W : Type*} [CommGroup W]

theorem emod_eq_zero_of_zpow_mul_zpow (hexp : ∀ w : W, w ^ 3 = 1) {a b : W} (ha : a ≠ 1)
    (hb : b ∉ Subgroup.zpowers a) {i j : ℤ} (h : a ^ i * b ^ j = 1) : i % 3 = 0 ∧ j % 3 = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbj : b ^ j ∈ Subgroup.zpowers a := by
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers a i)
  have hj : j % 3 = 0 := by
    by_contra hj
    apply hb
    have hjj : j * j % 3 = 1 % 3 := by
      rw [Int.mul_emod]
      have h0 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
      have h1 : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num)
      obtain h' | h' : j % 3 = 1 ∨ j % 3 = 2 := by omega
      · rw [h']
        norm_num
      · rw [h']
        norm_num
    have h2 : (b ^ j) ^ j = b := by
      rw [← zpow_mul, zpow_eq_of_emod (hexp b) hjj, zpow_one]
    rw [← h2]
    exact Subgroup.zpow_mem _ hbj j
  have hbj1 : b ^ j = 1 := by
    rw [zpow_eq_of_emod (hexp b) (n := 0) (by rw [hj]; rfl), zpow_zero]
  rw [hbj1, mul_one] at h
  have hord : orderOf a = 3 := orderOf_eq_prime (hexp a) ha
  have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h
  rw [hord] at h3
  have h4 : (3 : ℤ) ∣ i := by exact_mod_cast h3
  exact ⟨by omega, hj⟩

theorem pair_injective (hexp : ∀ w : W, w ^ 3 = 1) {a b : W} (ha : a ≠ 1)
    (hb : b ∉ Subgroup.zpowers a) :
    Function.Injective fun ij : Fin 3 × Fin 3 => a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only at h
  have h1 : a ^ ((i : ℤ) - i') * b ^ ((j : ℤ) - j') = 1 := by
    rw [zpow_sub, zpow_sub, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
      mul_mul_mul_comm, h, mul_mul_mul_comm, mul_inv_cancel, mul_inv_cancel, one_mul]
  obtain ⟨hi, hj⟩ := emod_eq_zero_of_zpow_mul_zpow hexp ha hb h1
  have := i.isLt
  have := i'.isLt
  have := j.isLt
  have := j'.isLt
  have hii : (i : ℕ) = i' := by omega
  have hjj : (j : ℕ) = j' := by omega
  rw [Fin.ext hii, Fin.ext hjj]

theorem span_of_card [Finite W] (hexp : ∀ w : W, w ^ 3 = 1) (hcard : Nat.card W ≤ 9) {a b : W}
    (ha : a ≠ 1) (hb : b ∉ Subgroup.zpowers a) : ∀ x : W, ∃ i j : ℕ, x = a ^ i * b ^ j := by
  have hinj := pair_injective hexp ha hb
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    exact hcard)
  intro x
  obtain ⟨⟨i, j⟩, h⟩ := hbij.2 x
  exact ⟨i, j, h.symm⟩

theorem pow_eq_one_of_sq {w : W} (hw : w ^ 3 = 1) {j : ℕ} (h : w ^ j * w ^ j = 1) :
    w ^ j = 1 := by
  calc w ^ j = w ^ j * (w ^ j * w ^ j) := by rw [h, mul_one]
    _ = (w ^ j) ^ 3 := by rw [pow_three]
    _ = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]

theorem inv_of_commute [Finite W] (hexp : ∀ w : W, w ^ 3 = 1) (hcard : Nat.card W ≤ 9)
    (β γ : W →* W) (hβ : ∀ w, β (β w) = w) (hγ : ∀ w, γ (γ (γ w)) = w)
    (hβγ : ∀ w, β (γ w) = γ (β w)) (hβ1 : ∃ w, β w ≠ w) (hγ1 : ∃ w, γ w ≠ w) :
    ∀ w, β w = w⁻¹ := by
  by_contra hne
  simp only [not_forall] at hne
  obtain ⟨w, hw⟩ := hne
  obtain ⟨u, hu⟩ := hβ1
  have hw1β : β (w * β w) = w * β w := by rw [map_mul, hβ, mul_comm]
  have hw2β : β (u⁻¹ * β u) = (u⁻¹ * β u)⁻¹ := by
    rw [map_mul, map_inv, hβ, mul_inv_rev, inv_inv]
  have hw1ne : w * β w ≠ 1 := fun h => hw (eq_inv_of_mul_eq_one_right h)
  have hw2ne : u⁻¹ * β u ≠ 1 := fun h => hu (inv_mul_eq_one.mp h).symm
  have hfixinv : ∀ t : W, β t = t → β t = t⁻¹ → t = 1 := by
    intro t h1 h2
    have h3 : t * t = 1 := by
      calc t * t = t * β t := by rw [h1]
        _ = 1 := by rw [h2, mul_inv_cancel]
    have := pow_eq_one_of_sq (hexp t) (j := 1) (by simpa using h3)
    simpa using this
  have hw2nmem : u⁻¹ * β u ∉ Subgroup.zpowers (w * β w) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hw2ne
    refine hfixinv _ ?_ hw2β
    rw [← hk, map_zpow, hw1β]
  have hspan := span_of_card hexp hcard hw1ne hw2nmem
  have hγw1 : γ (w * β w) = w * β w := by
    refine fix_of_mem_zpowers hγ (hexp _) ?_
    obtain ⟨i, j, hij⟩ := hspan (γ (w * β w))
    have h1 : β (γ (w * β w)) = γ (w * β w) := by rw [hβγ, hw1β]
    rw [hij, map_mul, map_pow, map_pow, hw1β, hw2β, inv_pow] at h1
    have h2 : (u⁻¹ * β u) ^ j * (u⁻¹ * β u) ^ j = 1 := by
      have h3 := mul_left_cancel h1
      calc (u⁻¹ * β u) ^ j * (u⁻¹ * β u) ^ j =
          (u⁻¹ * β u) ^ j * ((u⁻¹ * β u) ^ j)⁻¹ := by rw [h3]
        _ = 1 := mul_inv_cancel _
    rw [hij, pow_eq_one_of_sq (hexp _) h2, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i
  have hγw2 : γ (u⁻¹ * β u) = u⁻¹ * β u := by
    refine fix_of_mem_zpowers hγ (hexp _) ?_
    obtain ⟨i, j, hij⟩ := hspan (γ (u⁻¹ * β u))
    have h1 : β (γ (u⁻¹ * β u)) = (γ (u⁻¹ * β u))⁻¹ := by rw [hβγ, hw2β, map_inv]
    rw [hij, map_mul, map_pow, map_pow, hw1β, hw2β, inv_pow, mul_inv] at h1
    have h2 : (w * β w) ^ i * (w * β w) ^ i = 1 := by
      have h3 := mul_right_cancel h1
      calc (w * β w) ^ i * (w * β w) ^ i = ((w * β w) ^ i)⁻¹ * (w * β w) ^ i := by rw [← h3]
        _ = 1 := inv_mul_cancel _
    rw [hij, pow_eq_one_of_sq (hexp _) h2, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j
  obtain ⟨x, hx⟩ := hγ1
  apply hx
  obtain ⟨i, j, rfl⟩ := hspan x
  rw [map_mul, map_pow, map_pow, hγw1, hγw2]

theorem exists_fixed_ne_one (hexp : ∀ w : W, w ^ 3 = 1) (γ : W →* W) (hγ : ∀ w, γ (γ (γ w)) = w)
    (hγ1 : ∃ w, γ w ≠ w) : ∃ w, w ≠ 1 ∧ γ w = w := by
  obtain ⟨u, hu⟩ := hγ1
  by_cases hf : u * γ u * γ (γ u) = 1
  · refine ⟨γ u * u⁻¹, fun h => hu (mul_inv_eq_one.mp h), ?_⟩
    have e : γ (γ u) = (u * γ u)⁻¹ := eq_inv_of_mul_eq_one_right hf
    have h3 := hexp (γ u)
    rw [map_mul, map_inv, e]
    apply Additive.ofMul.injective
    have h3' : (3 : ℕ) • Additive.ofMul (γ u) = 0 := by
      rw [← ofMul_pow, h3]
      rfl
    simp only [ofMul_mul, ofMul_inv]
    rw [← sub_eq_zero]
    calc _ = -((3 : ℕ) • Additive.ofMul (γ u)) := by abel
      _ = 0 := by rw [h3', neg_zero]
  · refine ⟨_, hf, ?_⟩
    rw [map_mul, map_mul, hγ]
    exact (mul_rotate _ _ _).symm

end Comm3

section E9

variable {U : Type*} [AddCommGroup U]

theorem norm_eq_zero_of_inv (h2 : ∀ u : U, u + u = 0) (β σ : U →+ U) (hσ : ∀ u, σ (σ (σ u)) = u)
    (hβσ : ∀ u, β (σ u) = σ (σ (β u))) (hH : ∀ u u' : U, β u - u = σ (β u' - u') → β u = u)
    (u : U) : (β u - u) + σ (β u - u) + σ (σ (β u - u)) = 0 := by
  have hσβ : ∀ x, σ (β x) = β (σ (σ x)) := by
    intro x
    have := hβσ (σ (σ x))
    rw [hσ] at this
    rw [this, hσ]
  have hb : ∀ x, σ x = x → β x = x := by
    intro x hx
    refine hH x x ?_
    rw [map_sub, hσβ, hx, hx]
  have he : β (u + σ u + σ (σ u)) = u + σ u + σ (σ u) := by
    refine hb _ ?_
    rw [map_add, map_add, hσ]
    abel
  have hu : u = (u + σ u + σ (σ u)) + (σ (σ u) - σ u) := by
    have := h2 (σ (σ u))
    calc u = u + (σ (σ u) + σ (σ u)) := by rw [this, add_zero]
      _ = _ := by abel
  have key : ∃ t, β u - u = σ t - t := by
    refine ⟨σ (β (σ u)) + β (σ u) - σ u, ?_⟩
    have e1 : β u = β (u + σ u + σ (σ u)) + (β (σ (σ u)) - β (σ u)) := by
      conv_lhs => rw [hu]
      rw [map_add, map_sub]
    rw [e1, he, hβσ (σ u), map_sub, map_add]
    have h3 := h2 (σ (σ u))
    calc _ = (σ (σ (β (σ u))) + σ (β (σ u)) - σ (σ u) -
          (σ (β (σ u)) + β (σ u) - σ u)) + (σ (σ u) + σ (σ u)) := by abel
      _ = _ := by rw [h3, add_zero]
  obtain ⟨t, ht⟩ := key
  rw [ht]
  simp only [map_sub, hσ]
  abel

theorem e9_fix (h2 : ∀ u : U, u + u = 0) (β ξ η : U →+ U) (hξ : ∀ u, ξ (ξ (ξ u)) = u)
    (hη : ∀ u, η (η (η u)) = u) (hξη : ∀ u, ξ (η u) = η (ξ u))
    (hβξ : ∀ u, β (ξ u) = ξ (ξ (β u))) (hβη : ∀ u, β (η u) = η (η (β u)))
    (hHξ : ∀ u u' : U, β u - u = ξ (β u' - u') → β u = u)
    (hHη : ∀ u u' : U, β u - u = η (β u' - u') → β u = u)
    (hHξη : ∀ u u' : U, β u - u = ξ (η (β u' - u')) → β u = u)
    (hHξη2 : ∀ u u' : U, β u - u = ξ (η (η (β u' - u'))) → β u = u) (u : U) : β u = u := by
  have hηξ : ∀ x, η (ξ x) = ξ (η x) := fun x => (hξη x).symm
  have hN1 := norm_eq_zero_of_inv h2 β ξ hξ hβξ hHξ u
  have hN2 := norm_eq_zero_of_inv h2 β η hη hβη hHη u
  have hN3 := norm_eq_zero_of_inv h2 β (ξ.comp η)
    (fun x => by simp only [AddMonoidHom.comp_apply, hηξ, hξ, hη])
    (fun x => by simp only [AddMonoidHom.comp_apply, hβξ, hβη, hηξ])
    (fun x x' h => hHξη x x' h) u
  have hN4 := norm_eq_zero_of_inv h2 β (ξ.comp (η.comp η))
    (fun x => by simp only [AddMonoidHom.comp_apply, hηξ, hξ, hη])
    (fun x => by simp only [AddMonoidHom.comp_apply, hβξ, hβη, hηξ, hη])
    (fun x x' h => hHξη2 x x' h) u
  simp only [AddMonoidHom.comp_apply, hηξ, hη] at hN3 hN4
  rw [← sub_eq_zero]
  generalize β u - u = a at hN1 hN2 hN3 hN4 ⊢
  have hsum : (a + η a + η (η a)) + ξ (a + η a + η (η a)) + ξ (ξ (a + η a + η (η a))) = 0 := by
    rw [hN2, map_zero, map_zero, add_zero, add_zero]
  simp only [map_add] at hsum
  have h2a := h2 a
  have e : a = (a + ξ a + ξ (ξ a)) + (a + η a + η (η a)) + (a + ξ (η a) + ξ (ξ (η (η a)))) +
      (a + ξ (η (η a)) + ξ (ξ (η a))) - (a + η a + η (η a) + (ξ a + ξ (η a) + ξ (η (η a))) +
      (ξ (ξ a) + ξ (ξ (η a)) + ξ (ξ (η (η a))))) - (a + a) := by abel
  rw [e, hsum, hN1, hN2, hN3, hN4, h2a]
  abel

end E9

theorem e9_fix_mul {U : Type*} [CommGroup U] (h2 : ∀ u : U, u * u = 1) (β ξ η : U →* U)
    (hξ : ∀ u, ξ (ξ (ξ u)) = u) (hη : ∀ u, η (η (η u)) = u) (hξη : ∀ u, ξ (η u) = η (ξ u))
    (hβξ : ∀ u, β (ξ u) = ξ (ξ (β u))) (hβη : ∀ u, β (η u) = η (η (β u)))
    (hHξ : ∀ u u' : U, β u / u = ξ (β u' / u') → β u = u)
    (hHη : ∀ u u' : U, β u / u = η (β u' / u') → β u = u)
    (hHξη : ∀ u u' : U, β u / u = ξ (η (β u' / u')) → β u = u)
    (hHξη2 : ∀ u u' : U, β u / u = ξ (η (η (β u' / u'))) → β u = u) (u : U) : β u = u :=
  e9_fix (U := Additive U) h2 (MonoidHom.toAdditive β) (MonoidHom.toAdditive ξ)
    (MonoidHom.toAdditive η) hξ hη hξη hβξ hβη hHξ hHη hHξη hHξη2 u

section Rank

variable {K : Type*} [Group K]

theorem exists_mul_of_mem_sup {A B : Subgroup K} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : K} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have comm : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) :=
    fun m n => hcomm m m.2 n n.2
  have hrange := MonoidHom.noncommCoprod_range A.subtype B.subtype comm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange] at hx
  obtain ⟨⟨a, b⟩, rfl⟩ := hx
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem card_sup_of_commute {A B : Subgroup K} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisj : Disjoint A B) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have comm : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) :=
    fun m n => hcomm m m.2 n n.2
  have hinj := (MonoidHom.noncommCoprod_injective A.subtype B.subtype comm).2
    ⟨A.subtype_injective, B.subtype_injective, by simpa [Subgroup.range_subtype] using hdisj⟩
  have hrange := MonoidHom.noncommCoprod_range A.subtype B.subtype comm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem mem_zpowers_of_mem_zpowers {x y : K} (hx : x ^ 3 = 1) (hy : y ∈ Subgroup.zpowers x)
    (hy1 : y ≠ 1) : x ∈ Subgroup.zpowers y := by
  rcases eq_of_mem_zpowers_of_cube hx hy with h | h | h
  · exact absurd h hy1
  · rw [h]
    exact Subgroup.mem_zpowers x
  · have e : y * y = x := by
      rw [h]
      calc x * x * (x * x) = x ^ 3 * x := by rw [pow_three]; simp only [mul_assoc]
        _ = x := by rw [hx, one_mul]
    rw [← e]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers y) (Subgroup.mem_zpowers y)

theorem disjoint_zpowers {A : Subgroup K} {x : K} (hx : x ^ 3 = 1) (hxA : x ∉ A) :
    Disjoint A (Subgroup.zpowers x) := by
  rw [Subgroup.disjoint_def]
  intro y hyA hyx
  by_contra hy1
  exact hxA (Subgroup.zpowers_le.mpr hyA (mem_zpowers_of_mem_zpowers hx hyx hy1))

theorem three_le_pRank [Finite K] {x z c : K} (hxz : x * z = z * x) (hxc : x * c = c * x)
    (hzc : z * c = c * z) (hx : x ^ 3 = 1) (hz : z ^ 3 = 1) (hc : c ^ 3 = 1) (hz1 : z ≠ 1)
    (hxz' : x ∉ Subgroup.zpowers z) (hc' : c ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers x) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcz : ∀ {a b : K}, a * b = b * a → ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Subgroup.zpowers b,
      u * v = v * u := by
    intro a b hab u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ((show Commute a b from hab).zpow_zpow i j).eq
  have hx1 : x ≠ 1 := fun h => hxz' (by rw [h]; exact Subgroup.one_mem _)
  have hc1 : c ≠ 1 := fun h => hc' (by rw [h]; exact Subgroup.one_mem _)
  have hA : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers x, a * b = b * a :=
    hcz hxz.symm
  have hcardA : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers x) = 3 ^ 2 := by
    rw [card_sup_of_commute hA (disjoint_zpowers hx hxz'), Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime hz hz1, orderOf_eq_prime hx hx1]
    norm_num
  have hAc : ∀ a ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers c,
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup hA ha
    have h1 := hcz hzc a₁ ha₁ b hb
    have h2 := hcz hxc a₂ ha₂ b hb
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  set E := (Subgroup.zpowers z ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers c with hE
  have hcardE : Nat.card E = 3 ^ 3 := by
    rw [hE, card_sup_of_commute hAc (disjoint_zpowers hc hc'), hcardA, Nat.card_zpowers,
      orderOf_eq_prime hc hc1]
    norm_num
  have hmemE : ∀ e ∈ E, ∃ a₁ ∈ Subgroup.zpowers z, ∃ a₂ ∈ Subgroup.zpowers x,
      ∃ b ∈ Subgroup.zpowers c, e = a₁ * a₂ * b := by
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hAc he
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup hA ha
    exact ⟨a₁, ha₁, a₂, ha₂, b, hb, rfl⟩
  have hcube : ∀ {y : K}, y ^ 3 = 1 → ∀ u ∈ Subgroup.zpowers y, u ^ 3 = 1 := by
    intro y hy u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := by
    intro e he f hf
    obtain ⟨a₁, ha₁, a₂, ha₂, b, hb, rfl⟩ := hmemE e he
    obtain ⟨a₁', ha₁', a₂', ha₂', b', hb', rfl⟩ := hmemE f hf
    have c1 : Commute a₁ a₁' := hcz rfl a₁ ha₁ a₁' ha₁'
    have c2 : Commute a₁ a₂' := hcz hxz.symm a₁ ha₁ a₂' ha₂'
    have c3 : Commute a₁ b' := hcz hzc a₁ ha₁ b' hb'
    have c4 : Commute a₂ a₁' := hcz hxz a₂ ha₂ a₁' ha₁'
    have c5 : Commute a₂ a₂' := hcz rfl a₂ ha₂ a₂' ha₂'
    have c6 : Commute a₂ b' := hcz hxc a₂ ha₂ b' hb'
    have c7 : Commute b a₁' := (hcz hzc a₁' ha₁' b hb).symm
    have c8 : Commute b a₂' := (hcz hxc a₂' ha₂' b hb).symm
    have c9 : Commute b b' := hcz rfl b hb b' hb'
    exact (((c1.mul_right c2).mul_right c3).mul_left ((c4.mul_right c5).mul_right c6)).mul_left
      ((c7.mul_right c8).mul_right c9) |>.eq
  have hexpE : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    obtain ⟨a₁, ha₁, a₂, ha₂, b, hb, rfl⟩ := hmemE e he
    have c12 : Commute a₁ a₂ := hcz hxz.symm a₁ ha₁ a₂ ha₂
    have c3 : Commute (a₁ * a₂) b := hAc _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂)) b hb
    rw [c3.mul_pow, c12.mul_pow, hcube hz a₁ ha₁, hcube hx a₂ ha₂, hcube hc b hb, one_mul,
      one_mul]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexpE⟩ hcardE

end Rank

end CFSG.Quasithin.H13.A5
