module

public import CFSG.Quasithin.EmptyFaithful.S153E58Sv

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153E58

open S153E57

@[expose] def Hyp57Two {W : Type*} [Group W] (H : Subgroup (MulAut W)) (a : MulAut W) (s : ℕ) : Prop :=
  ∀ Kst : Subgroup (MulAut W), Kst ≤ H → Kst ≠ ⊥ → oTwoUpper Kst = Kst →
    (∀ h ∈ H, ∀ k ∈ Kst, h * k * h⁻¹ ∈ Kst) →
    (∀ W₀ : Subgroup W, IsIrrOn153 Kst W₀ → 8 ≤ Nat.card W₀) →
    ⁅Kst, Subgroup.zpowers a⁆ ≠ ⊥ ∧
      (IsIrrOn153 Kst ⊤ ∨
        ∃ W₁ W₂ : Subgroup W, IsIrrOn153 Kst W₁ ∧ IsIrrOn153 Kst W₂ ∧ W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ = ⊥ ∧
          Nat.card W₁ = 2 ^ (s + 2) ∧ Nat.card W₂ = 2 ^ (s + 2) ∧
          (∀ v ∈ Subgroup.zpowers a, ∀ w ∈ W₁, v w ∈ W₁) ∧
          (∀ v ∈ Subgroup.zpowers a, ∀ w ∈ W₂, v w ∈ W₂) ∧
          Nat.card ↥(commIn153 (Subgroup.zpowers a) W₁) = 2 ∧
          Nat.card ↥(commIn153 (Subgroup.zpowers a) W₂) = 2)

section Abelian

variable {W : Type} [CommGroup W] [Finite W]

theorem abelian_minNormal_false (hW : ∀ w : W, w ^ 2 = 1)
    {H K : Subgroup (MulAut W)} (hKmin : IsMinNormalIn H K)
    (hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hHirr : IsIrrOn153 H ⊤)
    (hH2 : CFSG.Open.pCoreOf 2 H = ⊥) {a : MulAut W} (haH : a ∈ H) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hc4 : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2) {s : ℕ} (hs : 0 < s)
    (hcard : Nat.card W = 2 ^ (2 * (s + 2)))
    (F3 : ∀ h ∈ H, orderOf h = 3 → h * a ≠ a * h)
    {D : Subgroup (MulAut W)} (hDH : D ≤ H) (hDa : ∀ d ∈ D, d * a = a * d) (haD : a ∈ ⁅D, D⁆)
    (h57 : Hyp57Two H a s) : False := by
  have : Finite (MulAut W) := finite_mulAut_of_finite W
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  obtain ⟨p, hp, hpK⟩ := IsMinNormalIn.exists_isPGroup hKmin hab
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKH, hKn, hK1, -⟩ := hKmin
  have hKnorm : H ≤ Subgroup.normalizer (K : Set (MulAut W)) := fun h hh =>
    mem_normalizer_of_forall' (hKn h hh)
  by_cases hp2 : p = 2
  ·
    subst hp2
    have : K ≤ CFSG.Open.pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 hKH hKnorm hpK
    rw [hH2, le_bot_iff] at this
    exact hK1 this
  by_cases hp3 : p = 3
  · subst hp3
    have hfix := fix_eq_one_of_normal hHirr hKn hK1
    have hCK : ∀ k ∈ K, a * k * a⁻¹ = k → k = 1 := by
      intro k hk hkc
      by_contra hk1
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hpK) ⟨k, hk⟩
      rw [Subgroup.orderOf_mk] at hj
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hj
        exact hk1 hj
      have h3 : 3 ∣ orderOf k := by
        rw [hj]
        exact dvd_pow_self 3 hj0
      set k' := k ^ (orderOf k / 3) with hk'
      have hord : orderOf k' = 3 :=
        orderOf_pow_orderOf_div (orderOf_pos k).ne' h3
      have hk'K : k' ∈ K := K.pow_mem hk _
      have hcomm : k' * a = a * k' := by
        have : Commute k a := by
          show k * a = a * k
          have h1 : a * k * a⁻¹ = k := hkc
          calc k * a = (a * k * a⁻¹) * a := by rw [h1]
            _ = a * k := by group
        exact (this.pow_left _).eq
      exact F3 k' (hKH hk'K) hord hcomm
    have hc4' : Nat.card ↥((⊤ : Subgroup W).map (phi a)) = 2 ^ 2 := by
      rw [← commV_zpowers_eq_map ha2]
      exact hc4
    exact false_of_three_group hW' hpK (by rw [← pow_two]; exact ha2) (fun k hk => hKn a haH k hk) hCK hfix
      hc4' hs hcard
  · have hp5 : 5 ≤ p := by
      by_contra h
      have hp4 : p = 4 := by have := hp.two_le; omega
      rw [hp4] at hp
      exact absurd hp (by decide)
    have hfix := fix_eq_one_of_normal hHirr hKn hK1
    have hK5 : ∀ W₀ : Subgroup W, IsIrrOn153 K W₀ → 8 ≤ Nat.card W₀ :=
      fun W₀ h => eight_le_card_of_irr hW' (fun α _ hα f => eq_one_of_isPGroup_perm hp hp5 hpK α hα f)
        hfix h
    have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
    have hoT : oTwoUpper K = K := by
      refine oTwoUpper_eq_of_odd fun x hx => ?_
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hpK) ⟨x, hx⟩
      rw [Subgroup.orderOf_mk] at hj
      rw [hj]
      exact hpodd.pow
    obtain ⟨hcommne, -⟩ := h57 K hKH hK1 hoT hKn hK5
    have hL5 := input15358Solv W hW H K a p hp (by omega) haH ha1 ha2 hc4 hKH hKn hpK hab hcommne
    exact false_of_L_five haH hDH hKn hab ha2 hDa haD hL5

end Abelian

end S153E58

end CFSG.Quasithin
