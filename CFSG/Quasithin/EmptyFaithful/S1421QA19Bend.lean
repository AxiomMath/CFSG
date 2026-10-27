module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.GH74.Uniqueness.Bender

namespace QA19

@[expose] def benderOrder (n i : ℕ) : ℕ :=
  ((2 ^ n) ^ i + 1) * ((2 ^ n) ^ i * ((2 ^ n - 1) *
    (if i = 3 then (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) else 1)))

@[expose] def benderLs : List ℕ := [1920, 7680, 245760, 258048, 86775571046077562880]

@[expose] def benderN (ℓ n : ℕ) : Prop :=
  ((ℓ = 1920 ∨ ℓ = 7680 ∨ ℓ = 245760) ∧ n = 2) ∨ (ℓ = 258048 ∧ n = 3) ∨
    (ℓ = 86775571046077562880 ∧ (n = 2 ∨ n = 3 ∨ n = 5))

instance (ℓ n : ℕ) : Decidable (benderN ℓ n) := by unfold benderN; infer_instance

theorem benderOrder_dvd_table_lt :
    ∀ ℓ ∈ benderLs, ∀ n < 67, 2 ≤ n → ∀ i ∈ [1, 2, 3], (i = 2 → n % 2 = 1) →
      benderOrder n i ∣ ℓ → i = 1 ∧ benderN ℓ n := by
  decide +kernel

theorem two_pow_le_benderOrder {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : 2 ^ n ≤ benderOrder n i := by
  unfold benderOrder
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hi : 2 ^ n ≤ (2 ^ n) ^ i ∨ i = 0 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact Or.inr h
    · exact Or.inl (by simpa using Nat.pow_le_pow_right (by omega : 0 < 2 ^ n) h)
  have hc : 1 ≤ 2 ^ n - 1 := by omega
  have he : 1 ≤ (if i = 3 then (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) else 1) := by
    split_ifs
    · apply Nat.div_pos
      · exact Nat.gcd_le_right _ (by omega)
      · exact Nat.gcd_pos_of_pos_left _ (by norm_num)
    · exact le_rfl
  rcases hi with hi | hi
  · calc 2 ^ n ≤ (2 ^ n) ^ i := hi
      _ ≤ (2 ^ n) ^ i * ((2 ^ n - 1) *
            (if i = 3 then (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) else 1)) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos hc he)
      _ ≤ ((2 ^ n) ^ i + 1) * ((2 ^ n) ^ i * ((2 ^ n - 1) *
            (if i = 3 then (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) else 1))) :=
          Nat.le_mul_of_pos_left _ (by omega)
  · subst hi
    have h0 : ¬ ((0 : ℕ) = 3) := by norm_num
    simp only [h0, ↓reduceIte, pow_zero, mul_one]
    omega

theorem benderOrder_dvd_table {ℓ n i : ℕ} (hℓ : ℓ ∈ benderLs) (hn : 2 ≤ n)
    (hi : i = 1 ∨ i = 2 ∨ i = 3) (hodd : i = 2 → n % 2 = 1) (hdvd : benderOrder n i ∣ ℓ) :
    i = 1 ∧ benderN ℓ n := by
  by_cases hlt : n < 67
  · exact benderOrder_dvd_table_lt ℓ hℓ n hlt hn i (by simpa using hi) hodd hdvd
  · exfalso
    push Not at hlt
    have h1 : 2 ^ 67 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
    have h2 := two_pow_le_benderOrder (by omega : 1 ≤ n) i
    have hℓ0 : 0 < ℓ := by
      simp only [benderLs, List.mem_cons, List.not_mem_nil, or_false] at hℓ
      rcases hℓ with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have h3 := Nat.le_of_dvd hℓ0 hdvd
    have h4 : ℓ < 2 ^ 67 := by
      simp only [benderLs, List.mem_cons, List.not_mem_nil, or_false] at hℓ
      rcases hℓ with rfl | rfl | rfl | rfl | rfl <;> norm_num
    omega

theorem benderOrder_of_benderType {K : Type*} [Group K] [Finite K]
    {n i e : ℕ} (h : BenderType K n i e) : Nat.card K = benderOrder n i := by
  rw [h.card_eq]
  rcases h.cases' with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> simp [benderOrder]

theorem IsBenderQuot.isL2Quot_of_dvd {n : ℕ} (hn : 2 ≤ n)
    {X : Type} [Group X] [Finite X] (hX : IsBenderQuot n X) {ℓ : ℕ} (hℓ : ℓ ∈ benderLs)
    (hdvd : Nat.card X ∣ ℓ) : IsL2Quot n X ∧ benderN ℓ n := by
  rcases hX with hL | ⟨a, rfl, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · obtain ⟨e⟩ := hL
    have hB : BenderType X n 1 1 := BenderType.linear n hn e
    have h := benderOrder_dvd_table hℓ hn (Or.inl rfl) (fun h => absurd h (by norm_num))
      (by rw [← benderOrder_of_benderType hB]; exact hdvd)
    exact ⟨⟨e⟩, h.2⟩
  · exfalso
    have hB : BenderType X (2 * a + 1) 2 1 :=
      BenderType.suzuki a (by omega) (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
    have h := benderOrder_dvd_table hℓ hn (Or.inr (Or.inl rfl)) (fun _ => by omega)
      (by rw [← benderOrder_of_benderType hB]; exact hdvd)
    exact absurd h.1 (by norm_num)
  · exfalso
    set S0 : Subgroup (StatedSU 3 (2 ^ n) F) :=
      (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) with hS0
    let π : X →* StatedProj (StatedSU 3 (2 ^ n) F) :=
      (QuotientGroup.mk' S0).comp e.toMonoidHom
    have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective S0).comp e.surjective
    have : Finite (StatedProj (StatedSU 3 (2 ^ n) F)) := Finite.of_surjective π hπ
    obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    have h := benderOrder_dvd_table hℓ hn (Or.inr (Or.inr rfl)) (fun h => absurd h (by norm_num))
      (by
        rw [← benderOrder_of_benderType hB]
        exact (Subgroup.card_dvd_of_surjective hπ).trans hdvd)
    exact absurd h.1 (by norm_num)
  · exfalso
    obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    have hB' : BenderType X n 3 e' := hB.of_mulEquiv e.symm
    have h := benderOrder_dvd_table hℓ hn (Or.inr (Or.inr rfl)) (fun h => absurd h (by norm_num))
      (by rw [← benderOrder_of_benderType hB']; exact hdvd)
    exact absurd h.1 (by norm_num)

end QA19

end CFSG.Quasithin
