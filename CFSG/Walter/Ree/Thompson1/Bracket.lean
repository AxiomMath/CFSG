module

public import CFSG.Walter.Ree.Thompson1.LinPoly

public section

namespace CFSG.Walter.Ree.Thompson1

open Finset

section Sums

variable {K : Type*} [Field K] {m : ℕ} [NeZero m]

theorem sum_sum_two {F : ZMod m → ZMod m → K} {p₁ p₂ : ZMod m × ZMod m} (hp : p₁ ≠ p₂)
    (hF : ∀ i j, F i j ≠ 0 → (i, j) = p₁ ∨ (i, j) = p₂) :
    ∑ i, ∑ j, F i j = F p₁.1 p₁.2 + F p₂.1 p₂.2 := by
  classical
  rw [← Finset.sum_product' (f := F), Finset.sum_eq_add p₁ p₂ hp]
  · intro c _ hc
    by_contra h
    rcases hF c.1 c.2 h with h' | h'
    · exact hc.1 h'
    · exact hc.2 h'
  · simp
  · simp

theorem sum_sum_one {F : ZMod m → ZMod m → K} {p : ZMod m × ZMod m}
    (hF : ∀ i j, F i j ≠ 0 → (i, j) = p) : ∑ i, ∑ j, F i j = F p.1 p.2 := by
  classical
  rw [← Finset.sum_product' (f := F), Finset.sum_eq_single p]
  · intro c _ hc
    by_contra h
    exact hc (hF c.1 c.2 h)
  · simp

omit [NeZero m] in
theorem sum_sum_three {F : ZMod m → ZMod m → K} {p₁ p₂ p₃ : ZMod m × ZMod m} [NeZero m]
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hF : ∀ i j, F i j ≠ 0 → (i, j) = p₁ ∨ (i, j) = p₂ ∨ (i, j) = p₃) :
    ∑ i, ∑ j, F i j = F p₁.1 p₁.2 + F p₂.1 p₂.2 + F p₃.1 p₃.2 := by
  classical
  rw [← Finset.sum_product' (f := F), Finset.univ_product_univ]
  rw [← Finset.sum_subset (Finset.subset_univ {p₁, p₂, p₃}) fun c _ hc => by
    by_contra h
    rcases hF c.1 c.2 h with h' | h' | h' <;> simp_all]
  rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
    Finset.sum_singleton, add_assoc]

omit [NeZero m] in
theorem sum3_cycle [Fintype (ZMod m)] (T : ZMod m → ZMod m → ZMod m → K) (f g h : ZMod m → K) :
    ∑ x, ∑ y, ∑ z, T x y z * g x * h y * f z = ∑ x, ∑ y, ∑ z, T y z x * f x * g y * h z := by
  calc ∑ a, ∑ b, ∑ c, T a b c * g a * h b * f c
      = ∑ a, ∑ c, ∑ b, T a b c * g a * h b * f c :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, T a b c * g a * h b * f c := Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ z, T y z x * f x * g y * h z :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by ring

end Sums

section Index

variable {m : ℕ}

theorem two_mul_ne_zero_of_odd (hm : Odd m) {s : ZMod m} (hs : s ≠ 0) : 2 * s ≠ 0 := by
  have hc : Nat.Coprime 2 m := (Nat.coprime_two_left).2 hm
  intro h
  apply hs
  have hu : IsUnit (2 : ZMod m) := by
    have := (ZMod.unitOfCoprime 2 hc).isUnit
    simpa using this
  exact (hu.mul_right_eq_zero).1 h

theorem perm_shape_A {s i j i₀ : ZMod m} (hs : s ≠ 0) (hs2 : 2 * s ≠ 0)
    (h : IsPerm3 (i + s) i j (i₀ + s) i₀ i₀) : i = i₀ ∧ j = i₀ := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩
  · exact ⟨h2, h3⟩
  · exact ⟨h2, h3⟩
  · exact absurd (by linear_combination h1 - h2) hs2
  · exact absurd (by linear_combination h1 - h2) hs
  · exact absurd (by linear_combination h1 - h2) hs2
  · exact absurd (by linear_combination h1 - h2) hs

theorem perm_shape_B {s i j i₀ : ZMod m} (hs : s ≠ 0) (hs2 : 2 * s ≠ 0)
    (h : IsPerm3 (i + s) i j (i₀ + s) i₀ (i₀ + s)) : i = i₀ ∧ j = i₀ + s := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩
  · exact ⟨h2, h3⟩
  · exact absurd (by linear_combination h1 - h2) hs
  · exact absurd (by linear_combination h1 - h2) hs2
  · exact absurd (by linear_combination h1 - h2) hs2
  · exact absurd (by linear_combination h1 - h2) hs
  · exact ⟨h2, h3⟩

theorem perm_shape_C {s i j a : ZMod m} (hs : s ≠ 0) (hs2 : 2 * s ≠ 0)
    (h : IsPerm3 (i + s) i j (a + s) a (a + 2 * s)) :
    (i = a ∧ j = a + 2 * s) ∨ (i = a + s ∧ j = a) ∨ (i = a + 2 * s ∧ j = a + s ∧ 3 * s = 0) := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h2, h3⟩
  · exact absurd (by linear_combination h1 - h2) hs2
  · exact absurd (by linear_combination h1 - h2) hs2
  · exact Or.inr (Or.inr ⟨h2, h3, by linear_combination h1 - h2⟩)
  · exact Or.inr (Or.inl ⟨h2, h3⟩)
  · exact absurd (by linear_combination h2 - h1) hs

theorem perm_shape_C' {s i j a : ZMod m} (hs : s ≠ 0) (hs2 : 2 * s ≠ 0)
    (h : IsPerm3 (i + s) i j (a + 2 * s) (a + s) a) :
    (i = a ∧ j = a + 2 * s) ∨ (i = a + s ∧ j = a) ∨ (i = a + 2 * s ∧ j = a + s ∧ 3 * s = 0) := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨h2, h3⟩)
  · exact absurd (by linear_combination h2 - h1) hs
  · exact absurd (by linear_combination h1 - h2) hs2
  · exact Or.inl ⟨h2, h3⟩
  · exact Or.inr (Or.inr ⟨h2, h3, by linear_combination h1 - h2⟩)
  · exact absurd (by linear_combination h1 - h2) hs2

end Index

variable {K : Type*} [Field K] [Fintype K] [CharP K 3] {m : ℕ} [NeZero m]
  (hK : Fintype.card K = 3 ^ m)
include hK

omit [CharP K 3] in
theorem coeff_support {B : ZMod m → ZMod m → K} {χ : ZMod m → ZMod m → K → K} {ψ : K → K}
    (h : ∀ κ : K, κ ≠ 0 → ∀ α β : K, ∑ i, ∑ j, B i j * χ i j κ * fr m i α * fr m j β =
      ψ κ * ∑ i, ∑ j, B i j * fr m i α * fr m j β)
    {i j : ZMod m} (hij : B i j ≠ 0) {κ : K} (hκ : κ ≠ 0) : χ i j κ = ψ κ := by
  have := bilin_unique hK (c := fun i j => B i j * χ i j κ - ψ κ * B i j) fun α β => by
    calc ∑ i, ∑ j, (B i j * χ i j κ - ψ κ * B i j) * fr m i α * fr m j β
        = ∑ i, ∑ j, (B i j * χ i j κ * fr m i α * fr m j β
            - ψ κ * (B i j * fr m i α * fr m j β)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := by
          simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
          linear_combination h κ hκ α β
  have h2 := congrFun (congrFun this i) j
  simp only [Pi.zero_apply] at h2
  have : B i j * (χ i j κ - ψ κ) = 0 := by linear_combination h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hij)

variable (m) in
@[expose] def jacT (s : ZMod m) (C : ZMod m → ZMod m → K) (x y z : ZMod m) : K :=
  (if x = y + s then C y z else 0) - (if y = x + s then C x z else 0)

theorem jac_expand {s : ZMod m} {c : K → K → K} {C : ZMod m → ZMod m → K}
    (hC : ∀ x y, c x y = ∑ i, ∑ j, C i j * fr m i x * fr m j y) (α β γ : K) :
    c (fr m s α * β - α * fr m s β) γ =
      ∑ x, ∑ y, ∑ z, jacT m s C x y z * fr m x α * fr m y β * fr m z γ := by
  classical
  rw [hC]
  have e1 : ∀ x y z, jacT m s C x y z * fr m x α * fr m y β * fr m z γ =
      (if x = y + s then C y z * fr m x α * fr m y β * fr m z γ else 0) -
        (if y = x + s then C x z * fr m x α * fr m y β * fr m z γ else 0) := by
    intro x y z
    simp only [jacT]
    split_ifs <;> ring
  simp only [e1, Finset.sum_sub_distrib]
  have e2 : ∑ x, ∑ y, ∑ z, (if x = y + s then C y z * fr m x α * fr m y β * fr m z γ else 0) =
      ∑ y, ∑ z, C y z * fr m (y + s) α * fr m y β * fr m z γ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_ite_eq']
    simp
  have e3 : ∑ x, ∑ y, ∑ z, (if y = x + s then C x z * fr m x α * fr m y β * fr m z γ else 0) =
      ∑ x, ∑ z, C x z * fr m x α * fr m (x + s) β * fr m z γ := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_ite_eq']
    simp
  rw [e2, e3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fr_sub_arg, fr_mul_arg, fr_mul_arg, fr_fr hK, fr_fr hK]
  ring

theorem jac_coeff {s : ZMod m} {c : K → K → K} {C : ZMod m → ZMod m → K}
    (hC : ∀ x y, c x y = ∑ i, ∑ j, C i j * fr m i x * fr m j y)
    (hjac : ∀ α β γ, c (fr m s α * β - α * fr m s β) γ + c (fr m s β * γ - β * fr m s γ) α
      + c (fr m s γ * α - γ * fr m s α) β = 0) (x y z : ZMod m) :
    jacT m s C x y z + jacT m s C y z x + jacT m s C z x y = 0 := by
  have := trilin_unique hK
    (c := fun x y z => jacT m s C x y z + jacT m s C y z x + jacT m s C z x y) fun α β γ => by
      have h := hjac α β γ
      rw [jac_expand hK hC, jac_expand hK hC, jac_expand hK hC,
        sum3_cycle (jacT m s C) (fun z => fr m z α) (fun x => fr m x β) (fun y => fr m y γ),
        sum3_cycle (jacT m s C) (fun z => fr m z β) (fun x => fr m x γ) (fun y => fr m y α),
        sum3_cycle (fun x y z => jacT m s C y z x) (fun z => fr m z α) (fun x => fr m x β)
          (fun y => fr m y γ)] at h
      rw [← h, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
  exact congrFun (congrFun (congrFun this x) y) z

theorem bilin_normal_form (hq : 3 < Fintype.card K) {b : K → K → K}
    (hb1 : ∀ x x' y, b (x + x') y = b x y + b x' y) (hb2 : ∀ x y y', b x (y + y') = b x y + b x y')
    {ψ : K → K} (hψ : ∀ κ : K, κ ≠ 0 → ∀ α β, b (κ * α) (κ * β) = ψ κ * b α β)
    (halt : ∀ α, b α α = 0) (hnd : ∀ α β, α ≠ 0 → b α β = 0 → β = 0 ∨ β = α ∨ β = -α) :
    ∃ s j₀ : ZMod m, ∃ u : K, u ≠ 0 ∧ s ≠ 0 ∧
      (∀ x : K, fr m s x = x → x = 0 ∨ x = 1 ∨ x = -1) ∧
      ∀ α β, u * b α β = fr m s (fr m j₀ α) * fr m j₀ β - fr m j₀ α * fr m s (fr m j₀ β) := by
  classical
  obtain ⟨B, hB⟩ := bilin_exists hK hb1 hb2
  have hsupp : ∀ {i j}, B i j ≠ 0 → ∀ {κ : K}, κ ≠ 0 → fr m i κ * fr m j κ = ψ κ :=
    fun {_ _} hij {_} hκ => coeff_support hK (B := B) (ψ := ψ)
      (χ := fun i j κ => fr m i κ * fr m j κ) (fun κ hκ α β => by
        rw [← hB, ← hψ κ hκ, hB]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [fr_mul_arg, fr_mul_arg]
        ring) hij hκ
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : K, β₀ ≠ 0 ∧ β₀ ≠ 1 ∧ β₀ ≠ -1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := fun x _ => by
      by_cases h0 : x = 0
      · simp [h0]
      by_cases h1 : x = 1
      · simp [h1]
      simp [hcon x h0 h1]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h3 : ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
    omega
  have hb0 : b 1 β₀ ≠ 0 := fun h => by
    rcases hnd 1 β₀ one_ne_zero h with h | h | h
    · exact hβ₀.1 h
    · exact hβ₀.2.1 h
    · exact hβ₀.2.2 h
  obtain ⟨i₀, j₀, hB0⟩ : ∃ i j, B i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hb0
    rw [hB]
    simp [hcon]
  have hpair : ∀ i j, B i j ≠ 0 → (i = i₀ ∧ j = j₀) ∨ (i = j₀ ∧ j = i₀) := by
    intro i j hij
    refine pair_perm hK fun κ => ?_
    rcases eq_or_ne κ 0 with rfl | hκ
    · simp [fr_zero_arg]
    rw [hsupp hij hκ, hsupp hB0 hκ]
  have hij0 : i₀ ≠ j₀ := by
    rintro rfl
    have h1 := halt 1
    rw [hB, sum_sum_one (p := (i₀, i₀)) fun i j h => ?_] at h1
    · simp only [fr_one_arg, mul_one] at h1
      exact hB0 h1
    · have := hpair i j (by intro h'; apply h; simp [h'])
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have htwo : ∀ F : ZMod m → ZMod m → K, (∀ i j, B i j = 0 → F i j = 0) →
      ∑ i, ∑ j, F i j = F i₀ j₀ + F j₀ i₀ := fun F hF =>
    sum_sum_two (p₁ := (i₀, j₀)) (p₂ := (j₀, i₀)) (by simp [hij0]) fun i j h => by
      have := hpair i j fun h' => h (hF i j h')
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hbform : ∀ α β, b α β =
      B i₀ j₀ * fr m i₀ α * fr m j₀ β + B j₀ i₀ * fr m j₀ α * fr m i₀ β := fun α β => by
    rw [hB, htwo _ fun i j h => by simp [h]]
  have hanti : B j₀ i₀ = -B i₀ j₀ := by
    have h1 := halt 1
    rw [hbform] at h1
    simp only [fr_one_arg, mul_one] at h1
    linear_combination h1
  refine ⟨i₀ - j₀, j₀, (B i₀ j₀)⁻¹, inv_ne_zero hB0, sub_ne_zero.2 hij0, ?_, ?_⟩
  · intro x hx
    have hx' : (B i₀ j₀)⁻¹ * b 1 (fr m (-j₀) x) = 0 := by
      rw [hbform, hanti]
      have e1 : fr m j₀ (fr m (-j₀) x) = x := by rw [fr_fr hK, add_neg_cancel, fr_zero_idx]
      have e2 : fr m i₀ (fr m (-j₀) x) = fr m (i₀ - j₀) x := by rw [fr_fr hK, sub_eq_add_neg]
      rw [e1, e2, hx]
      simp only [fr_one_arg, mul_one]
      field_simp
      ring
    have := hnd 1 (fr m (-j₀) x) one_ne_zero
      ((mul_eq_zero.1 hx').resolve_left (inv_ne_zero hB0))
    have e3 : ∀ y, fr m (-j₀) x = y → x = fr m j₀ y := fun y hy => by
      rw [← hy, fr_fr hK, add_neg_cancel, fr_zero_idx]
    rcases this with h | h | h
    · left; rw [e3 _ h, fr_zero_arg]
    · right; left; rw [e3 _ h, fr_one_arg]
    · right; right; rw [e3 _ h, fr_neg_arg, fr_one_arg]
  · intro α β
    have e : ∀ y, fr m (i₀ - j₀) (fr m j₀ y) = fr m i₀ y := fun y => by
      rw [fr_fr hK, sub_add_cancel]
    rw [hbform, hanti, e, e]
    field_simp
    ring


theorem trilin_normal_form (hm : Odd m) {s : ZMod m} (hs : s ≠ 0) {c : K → K → K}
    (hc1 : ∀ x x' y, c (x + x') y = c x y + c x' y) (hc2 : ∀ x y y', c x (y + y') = c x y + c x y')
    {ψ : K → K} (hψ : ∀ κ : K, κ ≠ 0 → ∀ x y, c (κ * fr m s κ * x) (κ * y) = ψ κ * c x y)
    (hjac : ∀ α β γ, c (fr m s α * β - α * fr m s β) γ + c (fr m s β * γ - β * fr m s γ) α
      + c (fr m s γ * α - γ * fr m s α) β = 0)
    (hnd : ∀ x y, y ≠ 0 → c x y = 0 → x = 0) :
    ∃ i₀ : ZMod m, ∃ C : K, C ≠ 0 ∧
      ((∀ x y, c x y = C * fr m i₀ (x * y)) ∨ (∀ x y, c x y = C * fr m i₀ (x * fr m s y))) := by
  classical
  have hs2 := two_mul_ne_zero_of_odd hm hs
  obtain ⟨C, hC⟩ := bilin_exists hK hc1 hc2
  have hsupp : ∀ {i j}, C i j ≠ 0 → ∀ {κ : K}, κ ≠ 0 →
      fr m (i + s) κ * fr m i κ * fr m j κ = ψ κ := fun {_ _} hij {_} hκ =>
    coeff_support hK (B := C) (ψ := ψ) (χ := fun i j κ => fr m (i + s) κ * fr m i κ * fr m j κ)
      (fun κ hκ α β => by
        rw [← hC, ← hψ κ hκ, hC]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [fr_mul_arg, fr_mul_arg, fr_mul_arg, fr_fr hK]
        ring) hij hκ
  have hperm : ∀ {i j i' j'}, C i j ≠ 0 → C i' j' ≠ 0 →
      IsPerm3 (i + s) i j (i' + s) i' j' := by
    intro i j i' j' h1 h2
    refine triple_perm hK (fun h => hs (by linear_combination h.1)) fun κ => ?_
    rcases eq_or_ne κ 0 with rfl | hκ
    · simp [fr_zero_arg]
    rw [hsupp h1 hκ, hsupp h2 hκ]
  have hT := jac_coeff hK hC hjac
  have h11 : c 1 1 ≠ 0 := fun h => one_ne_zero (hnd 1 1 one_ne_zero h)
  have hc11 : c 1 1 = ∑ i, ∑ j, C i j := by
    rw [hC]; simp [fr_one_arg]
  obtain ⟨i₀, j₀, hC0⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h11 (by rw [hc11]; simp [hcon])
  by_cases hA : j₀ = i₀
  · subst hA
    refine ⟨j₀, C j₀ j₀, hC0, Or.inl fun x y => ?_⟩
    rw [hC, sum_sum_one (p := (j₀, j₀)) fun i j h => ?_]
    · rw [fr_mul_arg]; ring
    · have := perm_shape_A hs hs2 (hperm (fun h' => h (by rw [h', zero_mul, zero_mul])) hC0)
      rw [this.1, this.2]
  by_cases hB : j₀ = i₀ + s
  · subst hB
    refine ⟨i₀, C i₀ (i₀ + s), hC0, Or.inr fun x y => ?_⟩
    rw [hC, sum_sum_one (p := (i₀, i₀ + s)) fun i j h => ?_]
    · rw [fr_mul_arg, fr_fr hK]; ring
    · have := perm_shape_B hs hs2 (hperm (fun h' => h (by rw [h', zero_mul, zero_mul])) hC0)
      rw [this.1, this.2]
  exfalso
  have hJ := hT (i₀ + s) i₀ j₀
  simp only [jacT] at hJ
  have hAP : j₀ = i₀ + 2 * s ∨ i₀ = j₀ + s := by
    by_contra hcon
    push Not at hcon
    apply hC0
    have e1 : ¬ i₀ = i₀ + s + s := fun h => hs2 (by linear_combination -h)
    have e2 : ¬ j₀ = i₀ + s + s := fun h => hcon.1 (by rw [h]; ring)
    have e3 : ¬ i₀ + s = j₀ + s := fun h => hA (by linear_combination -h)
    simpa [e1, e2, e3, hcon.2, hB] using hJ
  obtain ⟨a, ha⟩ : ∃ a : ZMod m, ∀ i j, C i j ≠ 0 →
      (i = a ∧ j = a + 2 * s) ∨ (i = a + s ∧ j = a) ∨ (i = a + 2 * s ∧ j = a + s ∧ 3 * s = 0) := by
    rcases hAP with h | h
    · refine ⟨i₀, fun i j hij => perm_shape_C hs hs2 ?_⟩
      have := hperm hij hC0
      rwa [h] at this
    · refine ⟨j₀, fun i j hij => perm_shape_C' hs hs2 ?_⟩
      have := hperm hij hC0
      rwa [h, show j₀ + s + s = j₀ + 2 * s by ring] at this
  have f1 : ¬ a = a + 2 * s := fun h => hs2 (by linear_combination -h)
  have f1' : ¬ a = a + s + s := fun h => hs2 (by linear_combination -h)
  have f2 : ¬ a + 2 * s = a + s := fun h => hs (by linear_combination h)
  have f3 : ¬ a + s = a + 2 * s + s := fun h => hs2 (by linear_combination -h)
  have t2 : (a + 2 * s = a + s + s) = True := eq_true (by ring)
  have hJ2 : C a (a + 2 * s) + (if a = a + 2 * s + s then C (a + 2 * s) (a + s) else 0)
      + C (a + s) a = 0 := by
    have h := hT (a + s) a (a + 2 * s)
    simp only [jacT, t2, f1', f2, f3, ite_true, ite_false, sub_zero] at h
    linear_combination h
  have hp12 : (a, a + 2 * s) ≠ (a + s, a) := fun h => hs (by
    have := congrArg Prod.fst h; linear_combination -this)
  have hp13 : (a, a + 2 * s) ≠ (a + 2 * s, a + s) := fun h => f1 (congrArg Prod.fst h)
  have hp23 : (a + s, a) ≠ (a + 2 * s, a + s) := fun h => f2 (by
    have := congrArg Prod.fst h; linear_combination -this)
  apply h11
  rw [hc11, sum_sum_three hp12 hp13 hp23 fun i j h => by
    rcases ha i j h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)]
  by_cases h3 : 3 * s = 0
  · have f4 : (a = a + 2 * s + s) = True := eq_true (by linear_combination -h3)
    simp only [f4, ite_true] at hJ2
    linear_combination hJ2
  · have f4 : ¬ a = a + 2 * s + s := fun h => h3 (by linear_combination -h)
    have hz : C (a + 2 * s) (a + s) = 0 := by
      by_contra hz
      rcases ha _ _ hz with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h4⟩
      · exact f1 h1.symm
      · exact f2 (by rw [h1])
      · exact h3 h4
    simp only [f4, ite_false, add_zero] at hJ2
    rw [hz, add_zero]
    linear_combination hJ2

theorem bracket_normal_form (hm : Odd m) (hq : 3 < Fintype.card K) {b c : K → K → K}
    (hb1 : ∀ x x' y, b (x + x') y = b x y + b x' y) (hb2 : ∀ x y y', b x (y + y') = b x y + b x y')
    (hc1 : ∀ x x' y, c (x + x') y = c x y + c x' y) (hc2 : ∀ x y y', c x (y + y') = c x y + c x y')
    {ψ₂ ψ₃ : K → K} (hψ₂ : ∀ κ : K, κ ≠ 0 → ∀ α β, b (κ * α) (κ * β) = ψ₂ κ * b α β)
    (hψ₃ : ∀ κ : K, κ ≠ 0 → ∀ x y, c (ψ₂ κ * x) (κ * y) = ψ₃ κ * c x y)
    (halt : ∀ α, b α α = 0) (hjac : ∀ α β γ, c (b α β) γ + c (b β γ) α + c (b γ α) β = 0)
    (hnd1 : ∀ α β, α ≠ 0 → b α β = 0 → β = 0 ∨ β = α ∨ β = -α)
    (hnd2 : ∀ x y, y ≠ 0 → c x y = 0 → x = 0) :
    ∃ s t₁ t₃ : ZMod m, ∃ u₂ u₃ : K, u₂ ≠ 0 ∧ u₃ ≠ 0 ∧ s ≠ 0 ∧
      (∀ x : K, fr m s x = x → x = 0 ∨ x = 1 ∨ x = -1) ∧
      (∀ α β, u₂ * b α β = fr m s (fr m t₁ α) * fr m t₁ β - fr m t₁ α * fr m s (fr m t₁ β)) ∧
      (∀ x y, fr m t₃ (u₃ * c x y) = u₂ * x * fr m t₁ y) := by
  classical
  obtain ⟨s, j₀, u, hu, hs, hfix, hbf⟩ := bilin_normal_form hK hq hb1 hb2 hψ₂ halt hnd1
  have finv : ∀ x : K, fr m j₀ (fr m (-j₀) x) = x := fun x => by
    rw [fr_fr hK, add_neg_cancel, fr_zero_idx]
  have finv' : ∀ x : K, fr m (-j₀) (fr m j₀ x) = x := fun x => by
    rw [fr_fr hK, neg_add_cancel, fr_zero_idx]
  have hb' : ∀ α β, u * b (fr m (-j₀) α) (fr m (-j₀) β) = fr m s α * β - α * fr m s β := by
    intro α β
    rw [hbf, finv, finv]
  obtain ⟨y₀, hy₀⟩ : ∃ y : K, fr m s y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := fun x _ => by
      rcases hfix x (hcon x) with h | h | h <;> simp [h]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h3 : ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
    omega
  have hψ₂' : ∀ κ : K, κ ≠ 0 → ψ₂ (fr m (-j₀) κ) = κ * fr m s κ := by
    intro κ hκ
    have h1 := hψ₂ (fr m (-j₀) κ) ((fr_eq_zero_iff _ _).not.2 hκ) (fr m (-j₀) 1) (fr m (-j₀) y₀)
    have h2 := hb' (κ * 1) (κ * y₀)
    rw [fr_mul_arg, fr_mul_arg, h1] at h2
    have h3 := hb' 1 y₀
    have key : (ψ₂ (fr m (-j₀) κ) - κ * fr m s κ) * (y₀ - fr m s y₀) = 0 := by
      simp only [fr_one_arg, fr_mul_arg, mul_one, one_mul] at h2 h3
      linear_combination h2 - ψ₂ (fr m (-j₀) κ) * h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right (sub_ne_zero.2 (Ne.symm hy₀)))
  set c' : K → K → K := fun x y => c (u⁻¹ * x) (fr m (-j₀) y) with hc'
  have hc'1 : ∀ x x' y, c' (x + x') y = c' x y + c' x' y := fun x x' y => by
    simp only [hc', mul_add, hc1]
  have hc'2 : ∀ x y y', c' x (y + y') = c' x y + c' x y' := fun x y y' => by
    simp only [hc', fr_add_arg, hc2]
  have hψ' : ∀ κ : K, κ ≠ 0 → ∀ x y,
      c' (κ * fr m s κ * x) (κ * y) = ψ₃ (fr m (-j₀) κ) * c' x y := by
    intro κ hκ x y
    simp only [hc']
    rw [← hψ₃ _ ((fr_eq_zero_iff _ _).not.2 hκ), hψ₂' κ hκ, fr_mul_arg]
    congr 1
    ring
  have hjac' : ∀ α β γ, c' (fr m s α * β - α * fr m s β) γ + c' (fr m s β * γ - β * fr m s γ) α
      + c' (fr m s γ * α - γ * fr m s α) β = 0 := by
    intro α β γ
    simp only [hc', ← hb', ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
    exact hjac _ _ _
  have hnd' : ∀ x y, y ≠ 0 → c' x y = 0 → x = 0 := by
    intro x y hy h
    have := hnd2 _ _ ((fr_eq_zero_iff _ _).not.2 hy) h
    simpa [hu] using this
  obtain ⟨i₀, C, hC, hcases⟩ := trilin_normal_form hK hm hs hc'1 hc'2 hψ' hjac' hnd'
  have hcc : ∀ x y, c x y = c' (u * x) (fr m j₀ y) := fun x y => by
    simp only [hc', ← mul_assoc, inv_mul_cancel₀ hu, one_mul, finv']
  have hfi : ∀ x : K, fr m (-i₀) (fr m i₀ x) = x := fun x => by
    rw [fr_fr hK, neg_add_cancel, fr_zero_idx]
  rcases hcases with h | h
  · refine ⟨s, j₀, -i₀, u, C⁻¹, hu, inv_ne_zero hC, hs, hfix, hbf, fun x y => ?_⟩
    rw [hcc, h, ← mul_assoc, inv_mul_cancel₀ hC, one_mul, hfi]
  · refine ⟨-s, s + j₀, -i₀, -u, -C⁻¹, neg_ne_zero.2 hu, neg_ne_zero.2 (inv_ne_zero hC),
      neg_ne_zero.2 hs, fun x hx => hfix x ?_, fun α β => ?_, fun x y => ?_⟩
    · have := congrArg (fr m s) hx
      rwa [fr_fr hK, add_neg_cancel, fr_zero_idx, eq_comm] at this
    · have e1 : ∀ z : K, fr m (-s) (fr m (s + j₀) z) = fr m j₀ z := fun z => by
        rw [fr_fr hK, neg_add_cancel_left]
      have e2 : ∀ z : K, fr m (s + j₀) z = fr m s (fr m j₀ z) := fun z => by rw [fr_fr hK]
      rw [e1, e1, e2, e2, neg_mul, hbf]
      ring
    · rw [hcc, h, neg_mul, ← mul_assoc, inv_mul_cancel₀ hC, one_mul, fr_neg_arg, hfi, fr_fr hK]
      ring

end CFSG.Walter.Ree.Thompson1
