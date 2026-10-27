module

public import CFSG.Quasithin.EmptyFaithful.S152Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.Background.ThreePrimeGroup

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_pow_three_le {n : ℕ} {P : Subgroup G} (hP : IsZ3TimesZ3Pow n ↥P) :
    Nat.card {x : ↥P // x ^ 3 = 1} ≤ 9 := by
  obtain ⟨φ⟩ := hP
  have : NeZero (3 ^ n) := ⟨by positivity⟩
  classical
  let f : {x : ↥P // x ^ 3 = 1} → {a : Multiplicative (ZMod 3) // a ^ 3 = 1} ×
      {b : Multiplicative (ZMod (3 ^ n)) // b ^ 3 = 1} :=
    fun x => (⟨(φ x.1).1, by
      have := congrArg (fun z => (z : Multiplicative (ZMod 3) × Multiplicative (ZMod (3 ^ n))).1)
        (show φ (x.1 ^ 3) = φ 1 by rw [x.2])
      simpa using this⟩, ⟨(φ x.1).2, by
      have := congrArg (fun z => (z : Multiplicative (ZMod 3) × Multiplicative (ZMod (3 ^ n))).2)
        (show φ (x.1 ^ 3) = φ 1 by rw [x.2])
      simpa using this⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply φ.injective
    exact Prod.ext (congrArg (fun z => z.1.1) hxy) (congrArg (fun z => z.2.1) hxy)
  have hA : Nat.card {a : Multiplicative (ZMod 3) // a ^ 3 = 1} ≤ 3 := by
    have := Finite.card_subtype_le (α := Multiplicative (ZMod 3)) fun a => a ^ 3 = 1
    rwa [show Nat.card (Multiplicative (ZMod 3)) = 3 from by
      rw [Nat.card_congr Multiplicative.toAdd]; exact Nat.card_zmod 3] at this
  have hB : Nat.card {b : Multiplicative (ZMod (3 ^ n)) // b ^ 3 = 1} ≤ 3 := by
    have := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod (3 ^ n))) (n := 3)
      (by norm_num)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact this
  calc Nat.card {x : ↥P // x ^ 3 = 1} ≤ Nat.card
        ({a : Multiplicative (ZMod 3) // a ^ 3 = 1} ×
          {b : Multiplicative (ZMod (3 ^ n)) // b ^ 3 = 1}) := Nat.card_le_card_of_injective f hf
    _ = Nat.card {a : Multiplicative (ZMod 3) // a ^ 3 = 1} *
        Nat.card {b : Multiplicative (ZMod (3 ^ n)) // b ^ 3 = 1} := Nat.card_prod _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul hA hB
    _ = 9 := by norm_num

theorem isThreePrimeGroup_of_sylow {M C D : Subgroup G} (hCM : C ≤ M)
    (hMC : M ≤ Subgroup.normalizer (C : Set G)) (hDM : D ≤ M) (hD3 : IsPGroup 3 D)
    (hDc : Nat.card D = 9) (hDe : ∀ x ∈ D, x ^ 3 = 1) (hDC : D ⊓ C = ⊥) {n : ℕ}
    (hP : ∀ P : Subgroup G, IsSylowIn 3 P M → IsZ3TimesZ3Pow n ↥P) : IsThreePrimeGroup C := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  obtain ⟨P, hPS, hDP⟩ := exists_isSylowIn_ge 3 hDM hD3
  have hcard : Nat.card {x : G | x ∈ P ∧ x ^ 3 = 1} ≤ 9 := by
    have e : {x : G | x ∈ P ∧ x ^ 3 = 1} ≃ {x : ↥P // x ^ 3 = 1} :=
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext (by simpa using x.2.2)⟩
        invFun := fun x => ⟨x.1.1, x.1.2, by simpa using congrArg Subtype.val x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [Nat.card_congr e]
    exact card_pow_three_le (hP P hPS)
  have hDset : (D : Set G) ⊆ {x : G | x ∈ P ∧ x ^ 3 = 1} := fun x hx => ⟨hDP hx, hDe x hx⟩
  have hfin : ({x : G | x ∈ P ∧ x ^ 3 = 1}).Finite := Set.toFinite _
  have hDcard : (D : Set G).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hDc
  have hsetcard : ({x : G | x ∈ P ∧ x ^ 3 = 1}).ncard ≤ (D : Set G).ncard := by
    rw [hDcard, ← Nat.card_coe_set_eq]
    exact hcard
  have hDeq := Set.eq_of_subset_of_ncard_le hDset hsetcard hfin
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 P M :=
    (CFSG.ABGLocalTools.isSylowOf_iff).mpr ⟨hPS.1, hPS.2.1, hPS.2.2⟩
  have hSylC := hSyl.inf_of_le_normalizer hCM hMC
  have h3C : 3 ∣ Nat.card C := h3
  have hcardPC : 3 ∣ Nat.card ↥(P ⊓ C) := by
    rw [hSylC.card_eq]
    have hpos : 0 < (Nat.card C).factorization 3 :=
      Nat.pos_of_ne_zero fun h0 => by
        have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3C
        omega
    exact dvd_pow_self 3 hpos.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hcardPC
  have hc3 : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hc
  have hcP : (c : G) ∈ P := c.2.1
  have hcC : (c : G) ∈ C := c.2.2
  have hcD : (c : G) ∈ D := by
    have : (c : G) ∈ {x : G | x ∈ P ∧ x ^ 3 = 1} :=
      ⟨hcP, by rw [← hc3]; exact pow_orderOf_eq_one _⟩
    rw [← hDeq] at this
    exact this
  have : (c : G) ∈ D ⊓ C := ⟨hcD, hcC⟩
  rw [hDC, Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hc3
  omega

end CFSG.Quasithin.S15221
