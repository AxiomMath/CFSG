module

public import CFSG.Quasithin.Background.C124AsmZ3Grp

public section

namespace CFSG.Quasithin.C124

theorem exists_order_three_lift {Γ M : Type*} [Group Γ] [Group M] (ρ : Γ →* M) {K : Subgroup Γ}
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) {x : M} (h3 : x ^ 3 = 1)
    (hKx : ∀ a ∈ K, ρ a ∈ Subgroup.zpowers x) {y t : Γ} (hy : y ∈ K) (hρy : ρ y = x)
    (ht : ∀ a ∈ K, t * a * t⁻¹ ∈ K) (htx : ρ t * x * (ρ t)⁻¹ = x⁻¹)
    (hD : ∀ d ∈ K, ρ d = 1 → t * d * t⁻¹ = d) :
    ∃ x₀ ∈ K, x₀ ^ 3 = 1 ∧ ρ x₀ = x ^ 2 := by
  have hτρ : ∀ a ∈ K, ρ (t * a * t⁻¹) = (ρ a)⁻¹ := by
    intro a ha
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hKx a ha)
    calc ρ (t * a * t⁻¹) = ρ t * ρ a * (ρ t)⁻¹ := by simp only [map_mul, map_inv]
      _ = ρ t * x ^ i * (ρ t)⁻¹ := by rw [← hi]
      _ = (ρ t * x * (ρ t)⁻¹) ^ i := conj_zpow.symm
      _ = (x ^ i)⁻¹ := by rw [htx, inv_zpow]
      _ = (ρ a)⁻¹ := by rw [hi]
  have hτ2 : ∀ a ∈ K, t * (t * a * t⁻¹) * t⁻¹ = a := by
    intro a ha
    have hτa := ht a ha
    have hw : a * (t * a * t⁻¹) ∈ K := K.mul_mem ha hτa
    have hw1 : ρ (a * (t * a * t⁻¹)) = 1 := by rw [map_mul, hτρ a ha, mul_inv_cancel]
    have h1 := hD _ hw hw1
    have e : t * (a * (t * a * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) := by
      group
    rw [e] at h1
    have h2 : (t * a * t⁻¹) * a = a * (t * a * t⁻¹) := (hK a ha _ hτa).symm
    exact mul_left_cancel (h1.trans h2.symm)
  set u : Γ := y * (t * y * t⁻¹)⁻¹ with hu
  have huK : u ∈ K := K.mul_mem hy (K.inv_mem (ht y hy))
  have hρu : ρ u = x ^ 2 := by
    rw [hu, map_mul, map_inv, hτρ y hy, hρy, inv_inv, sq]
  have htu : t * u * t⁻¹ = u⁻¹ := by
    have := hτ2 y hy
    calc t * u * t⁻¹ = (t * y * t⁻¹) * (t * (t * y * t⁻¹) * t⁻¹)⁻¹ := by rw [hu]; group
      _ = (t * y * t⁻¹) * y⁻¹ := by rw [this]
      _ = u⁻¹ := by rw [hu]; group
  have hu3 : u ^ 3 ∈ K := K.pow_mem huK 3
  have hρu3 : ρ (u ^ 3) = 1 := by
    rw [map_pow, hρu, ← pow_mul]
    calc x ^ (2 * 3) = (x ^ 3) ^ 2 := by rw [mul_comm, pow_mul]
      _ = 1 := by rw [h3, one_pow]
  have hfix := hD _ hu3 hρu3
  have hu6 : u ^ 6 = 1 := by
    have h1 : t * u ^ 3 * t⁻¹ = (u ^ 3)⁻¹ := by rw [← conj_pow, htu, inv_pow]
    have h2 : u ^ 3 = (u ^ 3)⁻¹ := hfix.symm.trans h1
    calc u ^ 6 = u ^ 3 * u ^ 3 := by rw [← pow_add]
      _ = u ^ 3 * (u ^ 3)⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel _
  refine ⟨u ^ 4, K.pow_mem huK 4, ?_, ?_⟩
  · calc (u ^ 4) ^ 3 = (u ^ 6) ^ 2 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [hu6, one_pow]
  · rw [map_pow, hρu, ← pow_mul]
    calc x ^ (2 * 4) = (x ^ 3) ^ 2 * x ^ 2 := by rw [← pow_mul, ← pow_add]
      _ = x ^ 2 := by rw [h3, one_pow, one_mul]

theorem exists_sign_character {P M : Type*} [Group P] [Group M] (σ : P →* M) {x : M}
    (h3 : x ^ 3 = 1) (h1 : x ≠ 1)
    (hn : ∀ p, σ p * x * (σ p)⁻¹ = x ∨ σ p * x * (σ p)⁻¹ = x⁻¹) :
    ∃ ω : P →* ℤˣ, ∀ p, σ p * x * (σ p)⁻¹ = x ^ (ω p : ℤ) := by
  classical
  have hxx : x ≠ x⁻¹ := ne_inv_of_order_three h3 h1
  have hconj : ∀ p q : P, σ (p * q) * x * (σ (p * q))⁻¹ =
      σ p * (σ q * x * (σ q)⁻¹) * (σ p)⁻¹ := by
    intro p q
    simp [map_mul, mul_assoc]
  have hinv : ∀ p : P, σ p * x⁻¹ * (σ p)⁻¹ = (σ p * x * (σ p)⁻¹)⁻¹ := by
    intro p
    group
  let f : P → ℤˣ := fun p => if σ p * x * (σ p)⁻¹ = x then 1 else -1
  have hf1 : f 1 = 1 := by simp [f]
  have hfm : ∀ p q, f (p * q) = f p * f q := by
    intro p q
    simp only [f]
    rw [hconj]
    rcases hn q with hq | hq <;> rcases hn p with hp | hp
    · rw [hq, hp]
      simp
    · rw [hq, hp]
      simp [hxx.symm]
    · rw [hq, hinv, hp]
      simp [hxx.symm]
    · rw [hq, hinv, hp, inv_inv]
      simp [hxx.symm]
  refine ⟨{ toFun := f, map_one' := hf1, map_mul' := hfm }, fun p => ?_⟩
  show σ p * x * (σ p)⁻¹ = x ^ ((if σ p * x * (σ p)⁻¹ = x then 1 else -1 : ℤˣ) : ℤ)
  by_cases hc : σ p * x * (σ p)⁻¹ = x
  · simp [hc]
  · have hfp : (if σ p * x * (σ p)⁻¹ = x then (1 : ℤˣ) else -1) = -1 := by simp [hc]
    rw [hfp]
    simp only [Units.val_neg, Units.val_one, zpow_neg, zpow_one]
    exact (hn p).resolve_left hc

theorem exists_semi_invariant {Γ M : Type*} [Group Γ] [Group M] (ρ : Γ →* M) {K : Subgroup Γ}
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) {P : Type*} [Group P] [Finite P] (ψ : P →* Γ)
    (hψ : ∀ (p : P), ∀ a ∈ K, ψ p * a * (ψ p)⁻¹ ∈ K) (ω : P →* ℤˣ) {x₀ : Γ} (hx₀ : x₀ ∈ K)
    (h3 : x₀ ^ 3 = 1) (hρ : ∀ p : P, ρ (ψ p * x₀ * (ψ p)⁻¹) = ρ x₀ ^ (ω p : ℤ)) :
    ∃ x ∈ K, x ^ 3 = 1 ∧ (∀ p : P, ψ p * x * (ψ p)⁻¹ = x ^ (ω p : ℤ)) ∧
      ρ x = ρ x₀ ^ Nat.card P := by
  classical
  have : Fintype P := Fintype.ofFinite P
  let _ : CommGroup K := { (inferInstance : Group K) with
    mul_comm := fun a b => Subtype.ext (hK a a.2 b b.2) }
  let κ : P → K →* K := fun p =>
    { toFun := fun a => ⟨ψ p * a * (ψ p)⁻¹, hψ p a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hκmul : ∀ (p q : P) (a : K), κ p (κ q a) = κ (p * q) a := by
    intro p q a
    apply Subtype.ext
    simp [κ, mul_assoc]
  let x₀' : K := ⟨x₀, hx₀⟩
  let c : P → K := fun p => κ p x₀'
  have hc3 : ∀ p, c p ^ 3 = 1 := by
    intro p
    show κ p x₀' ^ 3 = 1
    rw [← map_pow]
    have : x₀' ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [this, map_one]
  let g : P → K := fun p => c p ^ (ω p : ℤ)
  let x : K := ∏ p : P, g p
  have hx3 : x ^ 3 = 1 := by
    show (∏ p : P, g p) ^ 3 = 1
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro p _
    show (c p ^ (ω p : ℤ)) ^ 3 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hκx : ∀ p : P, κ p x = x ^ (ω p : ℤ) := by
    intro p
    calc κ p x = ∏ q : P, κ p (g q) := map_prod _ _ _
      _ = ∏ q : P, c (p * q) ^ (ω q : ℤ) := by
          refine Finset.prod_congr rfl fun q _ => ?_
          show κ p (c q ^ (ω q : ℤ)) = _
          rw [map_zpow]
          exact congrArg (· ^ (ω q : ℤ)) (hκmul p q x₀')
      _ = ∏ r : P, c r ^ (ω (p⁻¹ * r) : ℤ) := by
          rw [← Equiv.prod_comp (Equiv.mulLeft p) (fun r => c r ^ (ω (p⁻¹ * r) : ℤ))]
          refine Finset.prod_congr rfl fun q _ => ?_
          simp
      _ = ∏ r : P, g r ^ (ω p : ℤ) := by
          refine Finset.prod_congr rfl fun r _ => ?_
          have hω : ((ω (p⁻¹ * r) : ℤˣ) : ℤ) = (ω r : ℤ) * (ω p : ℤ) := by
            rw [map_mul, map_inv, Int.units_inv_eq_self, Units.val_mul, mul_comm]
          show _ = (c r ^ (ω r : ℤ)) ^ (ω p : ℤ)
          rw [hω, zpow_mul]
      _ = x ^ (ω p : ℤ) := Finset.prod_zpow _ _ _
  have hg : ∀ p : P, ρ (g p : Γ) = ρ x₀ := by
    intro p
    have h1 : ρ (c p : Γ) = ρ x₀ ^ (ω p : ℤ) := hρ p
    show ρ ((c p ^ (ω p : ℤ) : K) : Γ) = _
    rw [Subgroup.coe_zpow, map_zpow, h1, ← zpow_mul]
    have : ((ω p : ℤˣ) : ℤ) * (ω p : ℤ) = 1 := by
      rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
    rw [this, zpow_one]
  have hprod : ∀ s : Finset P, ρ ((∏ p ∈ s, g p : K) : Γ) = ρ x₀ ^ s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Subgroup.coe_mul, map_mul, ih,
        hg a, pow_succ']
  refine ⟨x, x.2, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val hx3
  · intro p
    have := congrArg Subtype.val (hκx p)
    simpa [κ] using this
  · have := hprod Finset.univ
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
    exact this

theorem exists_invariant_order_three {Γ M : Type*} [Group Γ] [Group M] (ρ : Γ →* M)
    {K : Subgroup Γ} (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) {x : M} (h3 : x ^ 3 = 1)
    (h1 : x ≠ 1) (hKx : ∀ a ∈ K, ρ a ∈ Subgroup.zpowers x) {y t : Γ} (hy : y ∈ K)
    (hρy : ρ y = x) (ht : ∀ a ∈ K, t * a * t⁻¹ ∈ K) (htx : ρ t * x * (ρ t)⁻¹ = x⁻¹)
    (hD : ∀ d ∈ K, ρ d = 1 → t * d * t⁻¹ = d) {P : Type*} [Group P] [Finite P] (ψ : P →* Γ)
    (hψ : ∀ (p : P), ∀ a ∈ K, ψ p * a * (ψ p)⁻¹ ∈ K)
    (hn : ∀ p, ρ (ψ p) * x * (ρ (ψ p))⁻¹ = x ∨ ρ (ψ p) * x * (ρ (ψ p))⁻¹ = x⁻¹) :
    ∃ z ∈ K, z ^ 3 = 1 ∧ (∀ p : P, ψ p * z * (ψ p)⁻¹ ∈ Subgroup.zpowers z) ∧
      ρ z = x ^ (2 * Nat.card P) := by
  obtain ⟨x₀, hx₀, hx₀3, hρx₀⟩ := exists_order_three_lift ρ hK h3 hKx hy hρy ht htx hD
  obtain ⟨ω, hω⟩ := exists_sign_character (ρ.comp ψ) h3 h1 hn
  have hρ : ∀ p : P, ρ (ψ p * x₀ * (ψ p)⁻¹) = ρ x₀ ^ (ω p : ℤ) := by
    intro p
    have h2 := hω p
    simp only [MonoidHom.comp_apply] at h2
    rw [map_mul, map_mul, map_inv, hρx₀]
    calc ρ (ψ p) * x ^ 2 * (ρ (ψ p))⁻¹ = (ρ (ψ p) * x * (ρ (ψ p))⁻¹) ^ 2 := conj_pow.symm
      _ = (x ^ (ω p : ℤ)) ^ 2 := by rw [h2]
      _ = (x ^ 2) ^ (ω p : ℤ) := by
        rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  obtain ⟨z, hz, hz3, hzs, hρz⟩ := exists_semi_invariant ρ hK ψ hψ ω hx₀ hx₀3 hρ
  refine ⟨z, hz, hz3, fun p => ?_, ?_⟩
  · rw [hzs p]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) _
  · rw [hρz, hρx₀, ← pow_mul]

end CFSG.Quasithin.C124
