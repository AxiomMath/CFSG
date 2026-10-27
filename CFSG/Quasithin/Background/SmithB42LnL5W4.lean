module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Gen
public import Mathlib

public section

namespace CFSG.Quasithin.B42Ln

open Matrix

abbrev G4 : Type := Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def pr4' : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

@[expose] def w4 (g : 𝕄₄) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun k l => g (pr4' k).1 (pr4' l).1 * g (pr4' k).2 (pr4' l).2 -
    g (pr4' k).1 (pr4' l).2 * g (pr4' k).2 (pr4' l).1

@[expose] def IsUp4 (M : 𝕄₄) : Prop := ∀ a b : Fin 4, (b < a → M a b = 0) ∧ (a = b → M a b = 1)

@[expose] def bt (c : Fin 64) (k : ℕ) : ZMod 2 := if (c : ℕ).testBit k then 1 else 0

@[expose] def up4 (c : Fin 64) : 𝕄₄ :=
  !![1, bt c 0, bt c 1, bt c 2; 0, 1, bt c 3, bt c 4; 0, 0, 1, bt c 5; 0, 0, 0, 1]

@[expose] def code4 (M : 𝕄₄) : Fin 64 :=
  ⟨((M 0 1).val + 2 * (M 0 2).val + 4 * (M 0 3).val + 8 * (M 1 2).val + 16 * (M 1 3).val +
    32 * (M 2 3).val) % 64, Nat.mod_lt _ (by norm_num)⟩

theorem up4_code4_aux : ∀ c₀ c₁ c₂ c₃ c₄ c₅ : ZMod 2,
    up4 (code4 !![1, c₀, c₁, c₂; 0, 1, c₃, c₄; 0, 0, 1, c₅; 0, 0, 0, 1]) =
      !![1, c₀, c₁, c₂; 0, 1, c₃, c₄; 0, 0, 1, c₅; 0, 0, 0, 1] := by
  decide

theorem eq_mat_of_isUp4 {M : 𝕄₄} (hM : IsUp4 M) :
    M = !![1, M 0 1, M 0 2, M 0 3; 0, 1, M 1 2, M 1 3; 0, 0, 1, M 2 3; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [(hM _ _).1, (hM _ _).2]

theorem up4_code4 {M : 𝕄₄} (hM : IsUp4 M) : up4 (code4 M) = M := by
  conv_rhs => rw [eq_mat_of_isUp4 hM]
  conv_lhs => rw [eq_mat_of_isUp4 hM]
  exact up4_code4_aux _ _ _ _ _ _

theorem code4_injective {M N : 𝕄₄} (hM : IsUp4 M) (hN : IsUp4 N) (h : code4 M = code4 N) :
    M = N := by
  rw [← up4_code4 hM, ← up4_code4 hN, h]

theorem up4_zero : up4 0 = 1 := by decide

set_option maxRecDepth 100000 in
theorem fix_one_le : ∀ c : Fin 64, up4 c * up4 c = 1 → c ≠ 0 →
    (Finset.univ.filter fun x : Fin 6 → ZMod 2 => w4 (up4 c) *ᵥ x = x).card ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fix_two_le : ∀ c d : Fin 64, up4 c * up4 c = 1 → up4 d * up4 d = 1 → c ≠ 0 → d ≠ 0 →
    c ≠ d → up4 c * up4 d = up4 d * up4 c →
    (Finset.univ.filter fun x : Fin 6 → ZMod 2 =>
      w4 (up4 c) *ᵥ x = x ∧ w4 (up4 d) *ᵥ x = x).card ≤ 8 := by
  decide +kernel

@[expose] def InQ4 (c : Fin 64) : Prop := (c : ℕ) % 2 = 0 ∧ (c : ℕ) < 32

instance : DecidablePred InQ4 := fun c => by unfold InQ4; infer_instance

set_option maxRecDepth 100000 in
theorem mem_q4 : ∀ c : Fin 64, up4 c * up4 c = 1 →
    16 ≤ (Finset.univ.filter fun d : Fin 64 =>
      up4 d * up4 d = 1 ∧ up4 c * up4 d = up4 d * up4 c).card → InQ4 c := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fix_q4_le : (Finset.univ.filter fun x : Fin 6 → ZMod 2 =>
    ∀ c : Fin 64, InQ4 c → w4 (up4 c) *ᵥ x = x).card ≤ 4 := by
  decide +kernel

theorem card_q4 : (Finset.univ.filter InQ4).card = 16 := by decide

theorem card_subtype_eq {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {x // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_subtype_mono {α : Type*} [Finite α] {p q : α → Prop} (h : ∀ x, p x → q x) :
    Nat.card {x // p x} ≤ Nat.card {x // q x} :=
  Nat.card_le_card_of_injective (Subtype.impEmbedding p q h) (Subtype.impEmbedding p q h).2

theorem card_mul_fix4_le {E : Subgroup G4} (hU : ∀ M ∈ E, IsUp4 (M : 𝕄₄))
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) :
    Nat.card E * Nat.card {x : Fin 6 → ZMod 2 // ∀ M ∈ E, w4 (M : 𝕄₄) *ᵥ x = x} ≤ 64 := by
  classical
  have hsq : ∀ M ∈ E, up4 (code4 (M : 𝕄₄)) * up4 (code4 (M : 𝕄₄)) = 1 := by
    intro M hM
    rw [up4_code4 (hU M hM), ← Matrix.SpecialLinearGroup.coe_mul, h2 M hM,
      Matrix.SpecialLinearGroup.coe_one]
  have hne : ∀ M ∈ E, M ≠ 1 → code4 (M : 𝕄₄) ≠ 0 := by
    intro M hM hM1 h0
    apply hM1
    apply Subtype.ext
    rw [← up4_code4 (hU M hM), h0, up4_zero, Matrix.SpecialLinearGroup.coe_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq E h2).exists_card_eq
  set S : Finset (Fin 64) := Finset.univ.image fun M : ↥E => code4 (M : 𝕄₄) with hS
  have hinj : Function.Injective fun M : ↥E => code4 (M : 𝕄₄) := fun M N h =>
    Subtype.ext (Subtype.ext (code4_injective (hU M M.2) (hU N N.2) h))
  have hcardS : S.card = Nat.card E := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
  have hfix64 : Nat.card {x : Fin 6 → ZMod 2 // ∀ M ∈ E, w4 (M : 𝕄₄) *ᵥ x = x} ≤ 64 := by
    calc _ ≤ Nat.card (Fin 6 → ZMod 2) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = 64 := by rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]; rfl
  have hex1 : 1 < Nat.card E → ∃ M ∈ E, M ≠ 1 := by
    intro h
    by_contra hall
    push Not at hall
    have : Nat.card E ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      constructor
      intro a b
      exact Subtype.ext ((hall a a.2).trans (hall b b.2).symm)
    omega
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  ·
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hk, pow_zero, one_mul]
      exact hfix64
    · have h1 : 1 < Nat.card E := by
        rw [hk]
        exact Nat.one_lt_two_pow (by omega)
      obtain ⟨M, hM, hM1⟩ := hex1 h1
      have h16 : Nat.card {x : Fin 6 → ZMod 2 // ∀ M ∈ E, w4 (M : 𝕄₄) *ᵥ x = x} ≤ 16 := by
        refine (card_subtype_mono (q := fun x => w4 (up4 (code4 (M : 𝕄₄))) *ᵥ x = x)
          fun x hx => ?_).trans ?_
        · rw [up4_code4 (hU M hM)]
          exact hx M hM
        · rw [card_subtype_eq]
          exact fix_one_le _ (hsq M hM) (hne M hM hM1)
      have hE4 : Nat.card E ≤ 4 := by
        rw [hk]
        calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 4 := by norm_num
      calc Nat.card E * _ ≤ 4 * 16 := Nat.mul_le_mul hE4 h16
        _ = 64 := by norm_num
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  ·
    have hk3' : k = 3 := by omega
    subst hk3'
    have h1 : 1 < Nat.card E := by rw [hk]; norm_num
    obtain ⟨M, hM, hM1⟩ := hex1 h1
    obtain ⟨N, hN, hN1, hNM⟩ : ∃ N ∈ E, N ≠ 1 ∧ N ≠ M := by
      by_contra hall
      push Not at hall
      have : Nat.card E ≤ 2 := by
        have hinj' : Function.Injective fun N : ↥E => decide ((N : G4) = 1) := by
          intro a b hab
          by_cases ha : (a : G4) = 1 <;> by_cases hb : (b : G4) = 1
          · exact Subtype.ext (ha.trans hb.symm)
          · simp [ha, hb] at hab
          · simp [ha, hb] at hab
          · exact Subtype.ext ((hall a a.2 ha).trans (hall b b.2 hb).symm)
        have := Nat.card_le_card_of_injective _ hinj'
        simpa using this
      omega
    have hcd : code4 (M : 𝕄₄) ≠ code4 (N : 𝕄₄) := fun h =>
      hNM (Subtype.ext (code4_injective (hU N hN) (hU M hM) h.symm))
    have h8 : Nat.card {x : Fin 6 → ZMod 2 // ∀ M ∈ E, w4 (M : 𝕄₄) *ᵥ x = x} ≤ 8 := by
      refine (card_subtype_mono (q := fun x => w4 (up4 (code4 (M : 𝕄₄))) *ᵥ x = x ∧
        w4 (up4 (code4 (N : 𝕄₄))) *ᵥ x = x) fun x hx => ?_).trans ?_
      · rw [up4_code4 (hU M hM), up4_code4 (hU N hN)]
        exact ⟨hx M hM, hx N hN⟩
      · rw [card_subtype_eq]
        refine fix_two_le _ _ (hsq M hM) (hsq N hN) (hne M hM hM1) (hne N hN hN1) hcd ?_
        rw [up4_code4 (hU M hM), up4_code4 (hU N hN), ← Matrix.SpecialLinearGroup.coe_mul,
          hc M hM N hN, Matrix.SpecialLinearGroup.coe_mul]
    rw [hk]
    calc 2 ^ 3 * _ ≤ 2 ^ 3 * 8 := Nat.mul_le_mul_left _ h8
      _ = 64 := by norm_num
  ·
    have h16 : 16 ≤ Nat.card E := by
      rw [hk]
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
    have hSQ : ∀ c ∈ S, InQ4 c := by
      intro c hcS
      obtain ⟨M, -, rfl⟩ := Finset.mem_image.1 hcS
      refine mem_q4 _ (hsq M M.2) ?_
      refine h16.trans (hcardS ▸ Finset.card_le_card fun d hd => ?_)
      obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hd
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hsq N N.2, ?_⟩
      rw [up4_code4 (hU M M.2), up4_code4 (hU N N.2), ← Matrix.SpecialLinearGroup.coe_mul,
        hc M M.2 N N.2, Matrix.SpecialLinearGroup.coe_mul]
    have hSsub : S ⊆ Finset.univ.filter InQ4 := fun c hc =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hSQ c hc⟩
    have hEle : Nat.card E ≤ 16 := by
      rw [← hcardS, ← card_q4]
      exact Finset.card_le_card hSsub
    have hSeq : S = Finset.univ.filter InQ4 :=
      Finset.eq_of_subset_of_card_le hSsub (by rw [card_q4, hcardS]; exact h16)
    have hQE : ∀ c : Fin 64, InQ4 c → ∃ M ∈ E, (M : 𝕄₄) = up4 c := by
      intro c hc
      have : c ∈ S := by rw [hSeq]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩
      obtain ⟨M, -, hMc⟩ := Finset.mem_image.1 this
      exact ⟨M, M.2, by rw [← hMc, up4_code4 (hU M M.2)]⟩
    have h4 : Nat.card {x : Fin 6 → ZMod 2 // ∀ M ∈ E, w4 (M : 𝕄₄) *ᵥ x = x} ≤ 4 := by
      refine (card_subtype_mono (q := fun x => ∀ c : Fin 64, InQ4 c → w4 (up4 c) *ᵥ x = x)
        fun x hx c hc => ?_).trans ?_
      · obtain ⟨M, hM, hMc⟩ := hQE c hc
        rw [← hMc]
        exact hx M hM
      · rw [card_subtype_eq]
        exact fix_q4_le
    calc Nat.card E * _ ≤ 16 * 4 := Nat.mul_le_mul hEle h4
      _ = 64 := by norm_num

end CFSG.Quasithin.B42Ln
