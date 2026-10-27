module

public import CFSG.Quasithin.Background.D2Decomp
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open scoped Pointwise

abbrev D33 : Type := DihedralGroup 3 × DihedralGroup 3

theorem omsh_exp6 : ∀ x : D33, x ^ 6 = 1 := by decide

theorem omsh_mul_mem : ∀ x y : D33, x ^ 3 = 1 → y ^ 3 = 1 → (x * y) ^ 3 = 1 := by decide

theorem omsh_comm : ∀ x y : D33, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x := by decide

theorem omsh_cent : ∀ x : D33, (∀ a : D33, a ^ 3 = 1 → x * a = a * x) → x ^ 3 = 1 := by decide

theorem omsh_inv_or_eigen : ∀ d : D33, d * d = 1 → d ≠ 1 →
    (∀ a : D33, a ^ 3 = 1 → d * a * d⁻¹ = a⁻¹) ∨
    (∃ e₁ e₂ : D33, e₁ ^ 3 = 1 ∧ e₂ ^ 3 = 1 ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ d * e₁ * d⁻¹ = e₁ ∧
      d * e₂ * d⁻¹ = e₂⁻¹ ∧ ∀ a : D33, a ^ 3 = 1 → ∃ i < 3, ∃ j < 3, a = e₁ ^ i * e₂ ^ j) := by
  decide

theorem omsh_pair : ∀ s t : D33, s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 → s ≠ t → s * t = t * s →
    ¬ (∀ a : D33, a ^ 3 = 1 → s * a * s⁻¹ = a⁻¹) → ¬ (∀ a : D33, a ^ 3 = 1 → t * a * t⁻¹ = a⁻¹) →
    ∀ a : D33, a ^ 3 = 1 → (s * t) * a * (s * t)⁻¹ = a⁻¹ := by
  decide

theorem omsh_odd_iff (x : D33) : Odd (orderOf x) ↔ x ^ 3 = 1 := by
  constructor
  · intro ho
    have h6 : orderOf x ∣ 3 * 2 := orderOf_dvd_of_pow_eq_one (omsh_exp6 x)
    have hc : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr ho
    exact orderOf_dvd_iff_pow_eq_one.mp (Nat.Coprime.dvd_of_dvd_mul_right hc h6)
  · intro h3
    exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)

theorem omsh_two (x : D33) (k : ℕ) (hk : x ^ (2 ^ k) = 1) : x * x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one (omsh_exp6 x)
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have h4 : 4 ∣ orderOf x := by
      rw [hjo]
      exact (Nat.pow_dvd_pow 2 (by omega : 2 ≤ j))
    have : 4 ∣ 6 := h4.trans h2
    omega
  have : orderOf x ∣ 2 := by
    rw [hjo]
    exact (Nat.pow_dvd_pow 2 hj1)
  rw [← sq]
  exact orderOf_dvd_iff_pow_eq_one.mp this

@[expose] def omshA : Subgroup D33 where
  carrier := {x | x ^ 3 = 1}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => omsh_mul_mem a b ha hb
  inv_mem' := fun {a} ha => by
    show a⁻¹ ^ 3 = 1
    rw [inv_pow, show a ^ 3 = 1 from ha, inv_one]

instance : DecidablePred (· ∈ omshA) := fun x => inferInstanceAs (Decidable (x ^ 3 = 1))

theorem omsh_card_A : Nat.card omshA = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide

section Transport

variable {B : Type*} [Group B] (X : Subgroup B) (e : ↥X ≃* D33)

@[expose] def omshφ : D33 →* B := X.subtype.comp e.symm.toMonoidHom

theorem omshφ_inj : Function.Injective (omshφ X e) :=
  X.subtype_injective.comp e.symm.injective

theorem omshφ_mem (d : D33) : omshφ X e d ∈ X := (e.symm d).2

theorem omshφ_eq {x : B} (hx : x ∈ X) : omshφ X e (e ⟨x, hx⟩) = x := by
  simp [omshφ]

theorem omshφ_orderOf (d : D33) : orderOf (omshφ X e d) = orderOf d :=
  orderOf_injective _ (omshφ_inj X e) d

theorem omsh_oTwoUpper : oTwoUpper X = omshA.map (omshφ X e) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨hxX, hxo⟩ := hx
    refine ⟨e ⟨x, hxX⟩, ?_, omshφ_eq X e hxX⟩
    have : Odd (orderOf (e ⟨x, hxX⟩)) := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hxo
    exact (omsh_odd_iff _).mp this
  · rintro _ ⟨d, hd, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨omshφ_mem X e d, ?_⟩
    rw [omshφ_orderOf]
    exact (omsh_odd_iff d).mpr hd

theorem omsh_mem_O {a : B} : a ∈ oTwoUpper X ↔ ∃ d : D33, d ^ 3 = 1 ∧ omshφ X e d = a := by
  rw [omsh_oTwoUpper X e]
  exact ⟨fun ⟨d, hd, h⟩ => ⟨d, hd, h⟩, fun ⟨d, hd, h⟩ => ⟨d, hd, h⟩⟩

theorem omsh_exists_elt {x : B} (hx : x ∈ X) : ∃ d : D33, omshφ X e d = x :=
  ⟨e ⟨x, hx⟩, omshφ_eq X e hx⟩

end Transport

structure OmShape {B : Type*} [Group B] (X : Subgroup B) : Prop where
  card_X : Nat.card X = 36
  card_O : Nat.card (oTwoUpper X) = 9
  comm_O : ∀ a ∈ oTwoUpper X, ∀ b ∈ oTwoUpper X, a * b = b * a
  exp_O : ∀ a ∈ oTwoUpper X, a ^ 3 = 1
  centralizer_O : ∀ x ∈ X, (∀ a ∈ oTwoUpper X, x * a = a * x) → x ∈ oTwoUpper X
  two_elements : ∀ x ∈ X, (∃ k : ℕ, x ^ (2 ^ k) = 1) → x * x = 1
  inv_or_eigen : ∀ s ∈ X, s * s = 1 → s ≠ 1 →
    (∀ a ∈ oTwoUpper X, s * a * s⁻¹ = a⁻¹) ∨
    (∃ e₁ ∈ oTwoUpper X, ∃ e₂ ∈ oTwoUpper X, e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ s * e₁ * s⁻¹ = e₁ ∧
      s * e₂ * s⁻¹ = e₂⁻¹ ∧ ∀ a ∈ oTwoUpper X, ∃ i j : ℕ, a = e₁ ^ i * e₂ ^ j)
  pair : ∀ s ∈ X, ∀ t ∈ X, s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 → s ≠ t → s * t = t * s →
    ¬ (∀ a ∈ oTwoUpper X, s * a * s⁻¹ = a⁻¹) → ¬ (∀ a ∈ oTwoUpper X, t * a * t⁻¹ = a⁻¹) →
    ∀ a ∈ oTwoUpper X, (s * t) * a * (s * t)⁻¹ = a⁻¹

theorem omShape_of_iso {B : Type*} [Group B] (X : Subgroup B)
    (e : ↥X ≃* DihedralGroup 3 × DihedralGroup 3) : OmShape X := by
  have hφ := omshφ_inj X e
  have hmem : ∀ d : D33, d ^ 3 = 1 → omshφ X e d ∈ oTwoUpper X := fun d hd =>
    (omsh_mem_O X e).mpr ⟨d, hd, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
  · rw [omsh_oTwoUpper X e, Subgroup.card_map_of_injective hφ, omsh_card_A]
  · intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := (omsh_mem_O X e).mp ha
    obtain ⟨d', hd', rfl⟩ := (omsh_mem_O X e).mp hb
    rw [← map_mul, ← map_mul, omsh_comm d d' hd hd']
  · intro a ha
    obtain ⟨d, hd, rfl⟩ := (omsh_mem_O X e).mp ha
    rw [← map_pow, hd, map_one]
  · intro x hx hc
    obtain ⟨d, rfl⟩ := omsh_exists_elt X e hx
    have hc' : ∀ a : D33, a ^ 3 = 1 → d * a = a * d := by
      intro a ha
      apply hφ
      rw [map_mul, map_mul]
      exact hc _ (hmem a ha)
    exact hmem _ (omsh_cent _ hc')
  · intro x hx ⟨k, hk⟩
    obtain ⟨d, rfl⟩ := omsh_exists_elt X e hx
    have h1 : d ^ (2 ^ k) = 1 := hφ (by rw [map_pow, map_one]; exact hk)
    rw [← map_mul, omsh_two d k h1, map_one]
  · intro s hs hss hs1
    obtain ⟨d, rfl⟩ := omsh_exists_elt X e hs
    have hd2 : d * d = 1 := hφ (by rw [map_mul, map_one]; exact hss)
    have hd1 : d ≠ 1 := fun h => hs1 (by rw [h, map_one])
    rcases omsh_inv_or_eigen d hd2 hd1 with h | ⟨e₁, e₂, h31, h32, h1, h2, hc1, hc2, hgen⟩
    · left
      intro a ha
      obtain ⟨d', hd', rfl⟩ := (omsh_mem_O X e).mp ha
      rw [← map_mul, ← map_inv, ← map_mul, h d' hd', map_inv]
    · right
      refine ⟨omshφ X e e₁, hmem e₁ h31, omshφ X e e₂, hmem e₂ h32, ?_, ?_, ?_, ?_, ?_⟩
      · intro h; exact h1 (hφ (h.trans (map_one _).symm))
      · intro h; exact h2 (hφ (h.trans (map_one _).symm))
      · rw [← map_mul, ← map_inv, ← map_mul, hc1]
      · rw [← map_mul, ← map_inv, ← map_mul, hc2, map_inv]
      · intro a ha
        obtain ⟨d', hd', rfl⟩ := (omsh_mem_O X e).mp ha
        obtain ⟨i, -, j, -, hij⟩ := hgen d' hd'
        exact ⟨i, j, by rw [hij, map_mul, map_pow, map_pow]⟩
  · intro s hs t ht hss htt hs1 ht1 hst hcomm hns hnt
    obtain ⟨d, rfl⟩ := omsh_exists_elt X e hs
    obtain ⟨d', rfl⟩ := omsh_exists_elt X e ht
    have hd2 : d * d = 1 := hφ (by rw [map_mul, map_one]; exact hss)
    have hd2' : d' * d' = 1 := hφ (by rw [map_mul, map_one]; exact htt)
    have hd1 : d ≠ 1 := fun h => hs1 (by rw [h, map_one])
    have hd1' : d' ≠ 1 := fun h => ht1 (by rw [h, map_one])
    have hdd' : d ≠ d' := fun h => hst (by rw [h])
    have hc : d * d' = d' * d := hφ (by rw [map_mul, map_mul]; exact hcomm)
    have hn1 : ¬ ∀ a : D33, a ^ 3 = 1 → d * a * d⁻¹ = a⁻¹ := by
      intro h; apply hns; intro a ha
      obtain ⟨d'', hd'', rfl⟩ := (omsh_mem_O X e).mp ha
      rw [← map_mul, ← map_inv, ← map_mul, h d'' hd'', map_inv]
    have hn2 : ¬ ∀ a : D33, a ^ 3 = 1 → d' * a * d'⁻¹ = a⁻¹ := by
      intro h; apply hnt; intro a ha
      obtain ⟨d'', hd'', rfl⟩ := (omsh_mem_O X e).mp ha
      rw [← map_mul, ← map_inv, ← map_mul, h d'' hd'', map_inv]
    intro a ha
    obtain ⟨d'', hd'', rfl⟩ := (omsh_mem_O X e).mp ha
    have := omsh_pair d d' hd2 hd2' hd1 hd1' hdd' hc hn1 hn2 d'' hd''
    rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, this, map_inv]

@[expose] def Om4IsoStatement : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (X : Subgroup (MulAut V)), IsOmegaFourPlus X →
    Nonempty (↥X ≃* DihedralGroup 3 × DihedralGroup 3)

theorem omShape_of_isOmegaFourPlus (h : Om4IsoStatement) {V : Type} [CommGroup V] [Finite V]
    {X : Subgroup (MulAut V)} (hX : IsOmegaFourPlus X) : OmShape X :=
  omShape_of_iso X (h V X hX).some

end CFSG.Quasithin
