module

public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace Q9

theorem ordA_two_ge {q : ℕ} (hq : 4 ≤ q) : 20160 ≤ ordA 2 q := by
  have hprod : ∏ i ∈ Finset.Icc 2 3, (q ^ i - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  have hd : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hd0 : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h3 : 64 ≤ q ^ 3 :=
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq _
  have h2 : 15 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 :=
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq _
    omega
  have h3' : 63 ≤ q ^ 3 - 1 := by omega
  unfold ordA
  rw [show 2 * (2 + 1) / 2 = 3 by norm_num, show 2 + 1 = 3 by norm_num, hprod]
  rw [Nat.le_div_iff_mul_le hd0]
  calc 20160 * Nat.gcd 3 (q - 1) ≤ 20160 * 3 := Nat.mul_le_mul_left _ hd
    _ ≤ 64 * (15 * 63) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul h2 h3')

theorem ordBC_two_gt {q : ℕ} (hq : 4 ≤ q) : 20160 < ordBC 2 q := by
  have hprod : ∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  have hd : Nat.gcd 2 (q - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  have hd0 : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h4 : 256 ≤ q ^ (2 * 2) :=
    calc 256 = 4 ^ (2 * 2) := by norm_num
      _ ≤ q ^ (2 * 2) := Nat.pow_le_pow_left hq _
  have h2 : 15 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 :=
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq _
    omega
  have h3 : 255 ≤ q ^ 4 - 1 := by
    have : 256 ≤ q ^ 4 :=
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq _
    omega
  unfold ordBC
  rw [hprod]
  refine Nat.lt_of_lt_of_le (show 20160 < 20161 by norm_num) ?_
  rw [Nat.le_div_iff_mul_le hd0]
  calc 20161 * Nat.gcd 2 (q - 1) ≤ 20161 * 2 := Nat.mul_le_mul_left _ hd
    _ ≤ 256 * (15 * 255) := by norm_num
    _ ≤ q ^ (2 * 2) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := Nat.mul_le_mul h4 (Nat.mul_le_mul h2 h3)

theorem sixty_le_card_statedSL3 {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    60480 ≤ Nat.card (StatedSL 3 K) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
  have hprod : ∏ j ∈ Finset.Icc 2 3, (Nat.card K ^ j - 1) =
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  rw [hprod, show 3 * (3 - 1) / 2 = 3 by norm_num]
  generalize Nat.card K = q at hK ⊢
  have h3 : 64 ≤ q ^ 3 :=
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hK _
  have h2 : 15 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 :=
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hK _
    omega
  have h3' : 63 ≤ q ^ 3 - 1 := by omega
  calc 60480 = 64 * (15 * 63) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul h3 (Nat.mul_le_mul h2 h3')

theorem a128FourList_of_exactType {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : IsPSL 3 2 n X ∨ IsSL3 (2 ^ n) X ∨ IsPSp4 2 n X) (hne : ¬ IsPSL 3 2 2 X) :
    A128FourList X := by
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard : 20160 ≤ Nat.card X := by
    rcases h with hL | ⟨K, _, _, hK, ⟨e⟩⟩ | hS
    · have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hL).1 rfl
      rw [h1]
      exact ordA_two_ge hq
    · rw [Nat.card_congr e.toEquiv]
      have := sixty_le_card_statedSL3 (K := K) (by rw [hK]; exact hq)
      omega
    · have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hS).2.2.1 rfl
      rw [h1]
      exact (ordBC_two_gt hq).le
  have hL1 : ¬ IsPSL 3 2 1 X := fun hL => by
    have h3 := (CFSG.Timmesfeld.card_statedClassicalModel_two hL).1 rfl
    have h4 : ordA (3 - 1) (2 ^ 1) = 168 := by decide
    omega
  unfold A128FourList
  iterate 14 right
  refine ⟨Or.inl ⟨n, ?_⟩, hL1, hne⟩
  rcases h with hL | hSL | hS
  · exact Or.inl ⟨by omega, hL⟩
  · exact Or.inr (Or.inl ⟨by omega, hSL⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hn, hS⟩))

@[expose] def L34Maximal : Prop :=
  ∀ (G : Type) [Group G] [Finite G], quasithinIsQTKECat G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → ∀ T K : Subgroup G, quasithinIsSylowTwo T →
      quasithinIsLocal T K → T ≤ Subgroup.normalizer (K : Set G) → IsPSL 3 2 2 (ModO2 K) →
      E2.IsDiagramNontrivial T K (T ⊓ K) → quasithinIsMaximalLocal T K

end Q9

end CFSG.Quasithin
