module

public import CFSG.Quasithin.Vol2.Ch10SecC3D

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Assembly.LowTwoRank
open scoped Matrix IsMulCommutative

theorem card_mul_card_fixV_lt_of_le_img {A : Subgroup (MulAut WMod)} (hAN : A ≤ norm)
    (hA : IsElemAbelian2 A) (hne : A ≠ ⊥) (hI : A ≤ img) :
    Nat.card A * Nat.card ↥(fixV A) < 2 ^ 9 := by
  obtain ⟨s₀, hs₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have h64 := card_fixV_le_of_mem hAN hA s₀.2 (fun h => hs₀ (Subtype.ext h))
  set A' := A.comap rho with hA'
  have hcard : Nat.card A = Nat.card A' := by
    rw [← Subgroup.map_comap_eq_self (f := rho) hI]
    exact Subgroup.card_map_of_injective rho_injective
  have hc : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := fun x hx y hy =>
    rho_injective (by rw [map_mul, map_mul]; exact hA.1 _ hx _ hy)
  have h2 : ∀ x ∈ A', x * x = 1 := fun x hx =>
    rho_injective (by rw [map_mul, map_one, ← sq]; exact hA.2 _ hx)
  set P₁ := A'.map (MonoidHom.fst ↥SL32 ↥SL32) with hP₁def
  set P₂ := A'.map (MonoidHom.snd ↥SL32 ↥SL32) with hP₂def
  have hP₁ : Nat.card P₁ ≤ 4 := card_le_four_of_elem
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact congrArg Prod.fst (hc x hx y hy))
    (by rintro _ ⟨x, hx, rfl⟩; exact congrArg Prod.fst (h2 x hx))
  have hP₂ : Nat.card P₂ ≤ 4 := card_le_four_of_elem
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; exact congrArg Prod.snd (hc x hx y hy))
    (by rintro _ ⟨x, hx, rfl⟩; exact congrArg Prod.snd (h2 x hx))
  rw [hcard]
  by_cases hb : (∃ c : ↥SL32, c ≠ 1 ∧ (c, 1) ∈ A') ∧ ∃ d : ↥SL32, d ≠ 1 ∧ ((1 : ↥SL32), d) ∈ A'
  · obtain ⟨⟨c, hc1, hcA⟩, d, hd1, hdA⟩ := hb
    have h16 := card_fixV_le_sixteen (A := A) hcA hdA hc1 hd1
    have hA16 : Nat.card A' ≤ 16 := by
      have hle : A' ≤ P₁.prod P₂ := fun x hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
      calc Nat.card A' ≤ Nat.card (P₁.prod P₂) := Subgroup.card_le_of_le hle
        _ = Nat.card P₁ * Nat.card P₂ := by
          rw [Nat.card_congr (Subgroup.prodEquiv P₁ P₂).toEquiv, Nat.card_prod]
        _ ≤ 4 * 4 := Nat.mul_le_mul hP₁ hP₂
        _ = 16 := by norm_num
    calc Nat.card A' * Nat.card ↥(fixV A) ≤ 16 * 16 := Nat.mul_le_mul hA16 h16
      _ < 2 ^ 9 := by norm_num
  · have hA4 : Nat.card A' ≤ 4 := by
      by_cases h1 : ∃ c : ↥SL32, c ≠ 1 ∧ (c, 1) ∈ A'
      · have h1' : ∀ d : ↥SL32, ((1 : ↥SL32), d) ∈ A' → d = 1 := fun d hd => by
          by_contra hd1
          exact hb ⟨h1, d, hd1, hd⟩
        refine le_trans (Nat.card_le_card_of_injective
          (fun x : ↥A' => (⟨x.1.1, x.1, x.2, rfl⟩ : ↥P₁)) ?_) hP₁
        intro x y hxy
        have hfst : x.1.1 = y.1.1 := congrArg Subtype.val hxy
        have hmem : x.1 * y.1⁻¹ ∈ A' := A'.mul_mem x.2 (A'.inv_mem y.2)
        have e : x.1 * y.1⁻¹ = (1, x.1.2 * y.1.2⁻¹) :=
          Prod.ext (by simp [hfst]) rfl
        rw [e] at hmem
        exact Subtype.ext (Prod.ext hfst (mul_inv_eq_one.mp (h1' _ hmem)))
      · have h1' : ∀ c : ↥SL32, (c, (1 : ↥SL32)) ∈ A' → c = 1 := fun c hc => by
          by_contra hc1
          exact h1 ⟨c, hc1, hc⟩
        refine le_trans (Nat.card_le_card_of_injective
          (fun x : ↥A' => (⟨x.1.2, x.1, x.2, rfl⟩ : ↥P₂)) ?_) hP₂
        intro x y hxy
        have hsnd : x.1.2 = y.1.2 := congrArg Subtype.val hxy
        have hmem : x.1 * y.1⁻¹ ∈ A' := A'.mul_mem x.2 (A'.inv_mem y.2)
        have e : x.1 * y.1⁻¹ = (x.1.1 * y.1.1⁻¹, 1) :=
          Prod.ext rfl (by simp [hsnd])
        rw [e] at hmem
        exact Subtype.ext (Prod.ext (mul_inv_eq_one.mp (h1' _ hmem)) hsnd)
    calc Nat.card A' * Nat.card ↥(fixV A) ≤ 4 * 64 := Nat.mul_le_mul hA4 h64
      _ < 2 ^ 9 := by norm_num

end CFSG.Quasithin.Vol2.Ch10.C3
