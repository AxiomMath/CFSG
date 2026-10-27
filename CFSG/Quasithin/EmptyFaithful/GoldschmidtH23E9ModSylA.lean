module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.QuasithinUnique

section Cosets

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_two_mul_of_cover {A B : Subgroup G} (hBA : B ≤ A) {x : G} (hxA : x ∈ A)
    (hxB : x ∉ B) (hcover : ∀ a ∈ A, a ∈ B ∨ a * x ∈ B) : Nat.card A = 2 * Nat.card B := by
  have hidx : (B.subgroupOf A).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨x, hxA⟩, fun h => hxB (Subgroup.mem_subgroupOf.mp h), fun b => ?_⟩
    rcases hcover b.1 b.2 with h | h
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr h)
    · exact Or.inl (Subgroup.mem_subgroupOf.mpr h)
  have h1 := Subgroup.card_mul_index (B.subgroupOf A)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv] at h1
  omega

theorem isSylowTwoOf_inf_of_two_cosets {H K T : Subgroup G} (hKH : K ≤ H) (hT : IsPGroup 2 T)
    {x : G} (hxH : x ∈ H) (hxT : x ∈ T) (hxK : x ∉ K) (hcover : ∀ h ∈ H, h ∈ K ∨ h * x ∈ K)
    (hS : IsSylowTwoOf (T ⊓ K) K) : IsSylowTwoOf (T ⊓ H) H := by
  have hH : Nat.card H = 2 * Nat.card K := card_eq_two_mul_of_cover hKH hxH hxK hcover
  have hP : Nat.card ↥(T ⊓ H) = 2 * Nat.card ↥(T ⊓ K) := by
    refine card_eq_two_mul_of_cover (inf_le_inf_left T hKH) ⟨hxT, hxH⟩ (fun h => hxK h.2) ?_
    intro a ha
    rcases hcover a ha.2 with h | h
    · exact Or.inl ⟨ha.1, h⟩
    · exact Or.inr ⟨T.mul_mem ha.1 hxT, h⟩
  have htwo : twoPart H = 2 * twoPart K := by
    unfold twoPart
    rw [hH, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, pow_add, pow_one]
  refine isSylowTwoOf_of_card_eq inf_le_right (hT.to_inf_left) ?_
  rw [hP, hS.card_eq, htwo]

end Cosets

section Five

variable {Γ : Type*} [Group Γ]

theorem conj_cases_five {a g : Γ} (ha : orderOf a = 5)
    (h : g * a * g⁻¹ ∈ Subgroup.zpowers a) :
    g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹ ∨ g * g * a * (g * g)⁻¹ = a⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have hmodeq : ∀ i j : ℤ, i ≡ j [ZMOD 5] → a ^ i = a ^ j := fun i j hij =>
    zpow_eq_zpow_iff_modEq.mpr (by rw [ha]; exact_mod_cast hij)
  have ha4 : a ^ (4 : ℤ) = a⁻¹ := by
    have h5 : a ^ 5 = 1 := by
      have := pow_orderOf_eq_one a
      rwa [ha] at this
    apply eq_inv_of_mul_eq_one_left
    calc a ^ (4 : ℤ) * a = a ^ 5 := by
          rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, ← pow_succ]
      _ = 1 := h5
  have hgg : g * g * a * (g * g)⁻¹ = a ^ (k * k) := by
    calc g * g * a * (g * g)⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := by group
      _ = g * a ^ k * g⁻¹ := by rw [hk]
      _ = (g * a * g⁻¹) ^ k := conj_zpow.symm
      _ = (a ^ k) ^ k := by rw [hk]
      _ = a ^ (k * k) := by rw [← zpow_mul]
  have hne : g * a * g⁻¹ ≠ 1 := by
    intro e
    have : a = 1 := by
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [e]; group
    rw [this, orderOf_one] at ha
    omega
  have hkcases : (k : ZMod 5) = 1 ∨ (k : ZMod 5) = 4 ∨ (k : ZMod 5) = 2 ∨ (k : ZMod 5) = 3 ∨
      (k : ZMod 5) = 0 := by
    generalize (k : ZMod 5) = x
    revert x
    decide
  have hmod : ∀ c : ℤ, (k : ZMod 5) = (c : ZMod 5) → k ≡ c [ZMOD 5] := fun c hc =>
    (ZMod.intCast_eq_intCast_iff k c 5).mp hc
  rcases hkcases with h1 | h4 | h2 | h3 | h0
  · left
    rw [← hk, hmodeq k 1 (hmod 1 (by simpa using h1)), zpow_one]
  · right
    left
    rw [← hk, hmodeq k 4 (hmod 4 (by simpa using h4)), ha4]
  · right
    right
    have hk2 : k ≡ 2 [ZMOD 5] := hmod 2 (by simpa using h2)
    rw [hgg, hmodeq (k * k) 4 (by simpa using hk2.mul hk2), ha4]
  · right
    right
    have hk3 : k ≡ 3 [ZMOD 5] := hmod 3 (by simpa using h3)
    rw [hgg, hmodeq (k * k) 4 (by have := hk3.mul hk3; exact this.trans (by decide)), ha4]
  · exfalso
    apply hne
    rw [← hk, hmodeq k 0 (hmod 0 (by simpa using h0)), zpow_zero]

end Five

end CFSG.Quasithin.SixData151b
