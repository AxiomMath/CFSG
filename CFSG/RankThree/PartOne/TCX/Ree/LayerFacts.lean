module

public import CFSG.RankThree.PartOne.TCX.Ree.SL2Facts
public import CFSG.RankThree.PartOne.TCX.Ree.SzFacts
public import CFSG.RankThree.PartOne.KLCE.TypeSL

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.LieType.Ree Matrix
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.LocalCores (isQuasisimple_of_mulEquiv)

structure LayerFacts (p : ℕ) {M : Type} [Group M] (Q P P₀ : Subgroup M) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥P
  cent : ∀ q ∈ Q, (∀ u ∈ P, q * u = u * q) → q = 1
  model : ∃ (t' : StatedLieTag) (n' f'' : ℕ), 1 ≤ f'' ∧
    LieModel (↥P ⧸ Subgroup.center ↥P) t' n' 2 (p * f'')
  pair : ∃ e₁ e₂ : M, e₁ ∈ P₀ ∧ e₂ ∈ P₀ ∧ (∃ k : ℕ, orderOf e₁ = 2 ^ k) ∧
    (∃ k : ℕ, orderOf e₂ = 2 ^ k) ∧ e₁ * e₂ ≠ e₂ * e₁ ∧
    ∀ d ∈ P, d * e₁ = e₁ * d → ∃ k : ℕ, orderOf d = 2 ^ k
  finite : Finite ↥P₀
  smaller : Nat.card ↥P₀ < Nat.card ↥P

section SL2

variable {M : Type} [Group M] {p f₀ : ℕ} {K₀ K : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
  [Field K] [Finite K] [CharP K 2]

theorem LayerFacts.of_sl2 (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ (p * f₀))
    (hK₀ : Nat.card K₀ = 2 ^ f₀) {Q P P₀ : Subgroup M} (hPP : P₀ ≤ P)
    (eK : SpecialLinearGroup (Fin 2) K ≃* ↥P) (e₀ : SpecialLinearGroup (Fin 2) K₀ ≃* ↥P₀)
    (hcent : ∀ q ∈ Q, (∀ u ∈ P, q * u = u * q) → q = 1) : LayerFacts p Q P P₀ := by
  have hpf : 5 ≤ p * f₀ := by nlinarith
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h01 : (0 : Fin (0 + 2)) ≠ 1 := by simp
  have h10 : (1 : Fin (0 + 2)) ≠ 0 := by simp
  refine ⟨isQuasisimple_of_mulEquiv eK (sl2_isQuasisimple h4), hcent,
    ⟨.PSL, 2, f₀, hf₀, sl2_lieModel hp5 hf₀ hK eK⟩, ?_, Finite.of_equiv _ e₀.toEquiv, ?_⟩
  · let t₁ : SpecialLinearGroup (Fin 2) K₀ := SpecialLinearGroup.transvection h01 (1 : K₀)
    let t₂ : SpecialLinearGroup (Fin 2) K₀ := SpecialLinearGroup.transvection h10 (1 : K₀)
    have ho₁ : orderOf t₁ = 2 := CFSG.RankThree.PartOne.KLCE.orderOf_transvection_one h01
    have ho₂ : orderOf t₂ = 2 := CFSG.RankThree.PartOne.KLCE.orderOf_transvection_one h10
    have hnc : t₁ * t₂ ≠ t₂ * t₁ := CFSG.RankThree.PartOne.KLCE.transvection_noncomm
    refine ⟨((e₀ t₁ : ↥P₀) : M), ((e₀ t₂ : ↥P₀) : M), (e₀ t₁).2, (e₀ t₂).2, ⟨1, ?_⟩, ⟨1, ?_⟩,
      ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ho₁, pow_one]
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ho₂, pow_one]
    · intro h
      exact hnc (e₀.injective (by rw [map_mul, map_mul]; exact Subtype.ext h))
    · intro d hd hcomm
      set s : SpecialLinearGroup (Fin 2) K := eK.symm ⟨((e₀ t₁ : ↥P₀) : M), hPP (e₀ t₁).2⟩ with hs
      have hsord : orderOf s = 2 := by
        rw [hs, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
          ho₁]
      have hs1 : s ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hsord
        omega
      have hss : s * s = 1 := by
        rw [← pow_two]
        exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hsord])
      have hc : eK.symm ⟨d, hd⟩ * s = s * eK.symm ⟨d, hd⟩ := by
        rw [hs, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hcomm
      have h1 := sl2_mul_self_of_comm hss hs1 hc
      have h2 : orderOf d ∣ 2 := by
        have : orderOf (eK.symm ⟨d, hd⟩) ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 (by rw [pow_two]; exact h1)
        rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at this
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
  · rw [Nat.card_congr e₀.toEquiv.symm, Nat.card_congr eK.toEquiv.symm]
    have h2 : 2 ≤ Nat.card K₀ := by
      rw [hK₀]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
    have hlt : Nat.card K₀ < Nat.card K := by
      rw [hK₀, hK]
      exact Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
    exact sl2_card_lt h2 hlt

end SL2

section Sz

variable {M : Type} [Group M] {p f₀ a a₀ : ℕ} {K₀ K : Type}
  [Field K₀] [Finite K₀] [CharP K₀ 2] [Field K] [Finite K] [CharP K 2]

theorem sz_card_lt_aux {x y : ℕ} (hx : 2 ≤ x) (hxy : x < y) :
    x ^ 2 * (x - 1) * (x ^ 2 + 1) < y ^ 2 * (y - 1) * (y ^ 2 + 1) := by
  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hx' : 1 ≤ x' := by omega
  have hxy' : x' < y' := by omega
  have h1 : (x' + 1) ^ 2 < (y' + 1) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h2 : (x' + 1) ^ 2 + 1 < (y' + 1) ^ 2 + 1 := by omega
  exact Nat.mul_lt_mul'' (Nat.mul_lt_mul'' h1 hxy') h2

theorem LayerFacts.of_sz (hf₀ : 1 ≤ f₀) (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hK₀ : Nat.card K₀ = 2 ^ (2 * a₀ + 1)) (hf : p * f₀ = 2 * a + 1) (hlt : Nat.card K₀ < Nat.card K)
    {Q P P₀ : Subgroup M} (hPP : P₀ ≤ P) (eK : suzukiGroup a K ≃* ↥P)
    (e₀ : suzukiGroup a₀ K₀ ≃* ↥P₀) (hcent : ∀ q ∈ Q, (∀ u ∈ P, q * u = u * q) → q = 1) :
    LayerFacts p Q P P₀ := by
  obtain ⟨t₁, t₂, ho₁, ho₂, hnc⟩ := sz_noncomm_involutions hK₀
  refine ⟨isQuasisimple_of_mulEquiv eK (sz_isQuasisimple ha hK), hcent,
    ⟨.twistedB2, 0, f₀, hf₀, sz_lieModel ha hK eK hf⟩, ?_, Finite.of_equiv _ e₀.toEquiv, ?_⟩
  · refine ⟨((e₀ t₁ : ↥P₀) : M), ((e₀ t₂ : ↥P₀) : M), (e₀ t₁).2, (e₀ t₂).2, ⟨1, ?_⟩, ⟨1, ?_⟩,
      ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ho₁, pow_one]
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ho₂, pow_one]
    · intro h
      exact hnc (e₀.injective (by rw [map_mul, map_mul]; exact Subtype.ext h))
    · intro d hd hcomm
      set s : suzukiGroup a K := eK.symm ⟨((e₀ t₁ : ↥P₀) : M), hPP (e₀ t₁).2⟩ with hs
      have hsord : orderOf s = 2 := by
        rw [hs, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
          ho₁]
      have hc : eK.symm ⟨d, hd⟩ * s = s * eK.symm ⟨d, hd⟩ := by
        rw [hs, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hcomm
      obtain ⟨k, hk⟩ := sz_two_element_of_comm hK hsord hc
      exact ⟨k, by rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at hk⟩
  · rw [Nat.card_congr e₀.toEquiv.symm, Nat.card_congr eK.toEquiv.symm,
      suzuki_order hK₀, suzuki_order hK, ← hK₀, ← hK]
    have h2 : 2 ≤ Nat.card K₀ := by
      rw [hK₀]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a₀ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact sz_card_lt_aux h2 hlt

end Sz

end CFSG.RankThree.PartOne.TCX.Ree
