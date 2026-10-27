module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7FLCode

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Gap7

namespace FL

theorem map_prodSel {M N F : Type} [Monoid M] [Monoid N] [FunLike F M N] [MonoidHomClass F M N]
    (φ : F) : ∀ (bs : List Bool) (xs : List M), φ (prodSel bs xs) = prodSel bs (xs.map φ)
  | b :: bs, x :: xs => by
    simp only [prodSel, List.map_cons, map_mul, map_prodSel φ bs xs]
    cases b <;> simp
  | [], _ => by simp [prodSel]
  | _ :: _, [] => by simp [prodSel]

theorem prodSel_eq_one {M : Type} [Monoid M] :
    ∀ (bs : List Bool) (xs : List M), (∀ x ∈ xs, x = 1) → prodSel bs xs = 1
  | b :: bs, x :: xs, h => by
    rw [prodSel, h x (List.mem_cons_self ..), prodSel_eq_one bs xs fun y hy =>
      h y (List.mem_cons_of_mem _ hy)]
    cases b <;> simp
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

theorem prodSel_map_congr {M : Type} [Monoid M] (p q : ℕ → Bool) (x : ℕ → M) :
    ∀ L : List ℕ, (∀ l ∈ L, p l = q l ∨ x l = 1) →
      prodSel (L.map p) (L.map x) = prodSel (L.map q) (L.map x)
  | [], _ => rfl
  | l :: L, h => by
    simp only [List.map_cons, prodSel]
    rw [prodSel_map_congr p q x L fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]
    rcases h l (List.mem_cons_self ..) with h1 | h1
    · rw [h1]
    · rw [h1]; cases p l <;> cases q l <;> rfl

theorem xorSel_append : ∀ (bs bs' : List Bool) (xs xs' : List ℕ), bs.length = xs.length →
    xorSel (bs ++ bs') (xs ++ xs') = xorSel bs xs ^^^ xorSel bs' xs'
  | [], _, [], _, _ => by simp [xorSel]
  | b :: bs, bs', x :: xs, xs', h => by
    simp only [List.cons_append, xorSel]
    rw [xorSel_append bs bs' xs xs' (by simpa using h), Nat.xor_assoc]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

theorem xorSel_map (φ : ℕ → ℕ) (hφ : ∀ a b, φ (a ^^^ b) = φ a ^^^ φ b) (h0 : φ 0 = 0) :
    ∀ (bs : List Bool) (xs : List ℕ), φ (xorSel bs xs) = xorSel bs (xs.map φ)
  | b :: bs, x :: xs => by
    simp only [xorSel, List.map_cons, hφ, xorSel_map φ hφ h0 bs xs]
    cases b <;> simp [h0]
  | [], _ => by simp [xorSel, h0]
  | _ :: _, [] => by simp [xorSel, h0]

theorem xorSel_map_eq_zero (φ : ℕ → ℕ) (hφ : ∀ a b, φ (a ^^^ b) = φ a ^^^ φ b) (h0 : φ 0 = 0) :
    ∀ (bs : List Bool) (xs : List ℕ), (∀ x ∈ xs, φ x = 0) → φ (xorSel bs xs) = 0
  | b :: bs, x :: xs, h => by
    simp only [xorSel, hφ]
    rw [xorSel_map_eq_zero φ hφ h0 bs xs fun y hy => h y (List.mem_cons_of_mem _ hy)]
    cases b <;> simp [h0, h x (List.mem_cons_self ..)]
  | [], _, _ => by simp [xorSel, h0]
  | _ :: _, [], _ => by simp [xorSel, h0]

theorem xor_eq_zero_iff {x y : ℕ} : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    calc x = (x ^^^ y) ^^^ y := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      _ = y := by rw [h, Nat.zero_xor]
  · rintro rfl; exact Nat.xor_self x

theorem fld_xor (a b p w : ℕ) : fld (a ^^^ b) p w = fld a p w ^^^ fld b p w := by
  simp only [fld, Nat.shiftRight_xor_distrib, Nat.xor_mod_two_pow]

theorem fld_zero (p w : ℕ) : fld 0 p w = 0 := by simp [fld]

theorem nb_xor (a b i : ℕ) : nb (a ^^^ b) i = nb a i ^^^ nb b i := by
  have h := fld_xor a b (4 * i) 4
  simpa [fld, nb] using h

theorem nb_zero (i : ℕ) : nb 0 i = 0 := by simp [nb]

theorem pY_xor (a b : ℕ) : pY (a ^^^ b) = pY a ^^^ pY b := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  simp only [pY, Nat.shiftRight_xor_distrib, h4, ← Nat.xor_mod_two_pow]
  congr 1
  ac_rfl

theorem pY_zero : pY 0 = 0 := by simp [pY]

theorem nb_eq (x i : ℕ) : nb x i = fld x (4 * i) 2 + 4 * fld x (4 * i + 2) 2 := by
  unfold nb fld
  rw [Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (x >>> (4 * i)) 2]
  generalize x >>> (4 * i) = y
  have : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [this]
  omega

theorem fld_two_lt (x p : ℕ) : fld x p 2 < 4 := Nat.mod_lt _ (by norm_num)

theorem fld_of_shiftRight_eq_zero {x : ℕ} (h : x >>> OC = 0) (p w : ℕ) : fld x (OC + p) w = 0 := by
  simp [fld, Nat.shiftRight_add, h]

theorem goodN_iff : ∀ a < 4, ∀ b < 4, goodN (a + 4 * b) = true ↔ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  decide

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem fnz_spec (x : ℕ) : ∀ n ≤ 30,
    (fnz x n = 0 ∧ ∀ i, 30 - n ≤ i → i < 30 → nb x i = 0) ∨
      (∃ i, 30 - n ≤ i ∧ i < 30 ∧ fnz x n = nb x i ∧ nb x i ≠ 0)
  | 0, _ => Or.inl ⟨rfl, fun i h1 h2 => by omega⟩
  | n + 1, hn => by
    rcases fnz_spec x n (by omega) with ⟨h0, hz⟩ | ⟨i, hi1, hi2, hi3, hi4⟩
    · by_cases hb : nb x (29 - n) = 0
      · left
        refine ⟨?_, fun i h1 h2 => ?_⟩
        · simp [fnz, hb, h0]
        · rcases Nat.lt_or_ge i (30 - n) with h | h
          · have : i = 29 - n := by omega
            rw [this]; exact hb
          · exact hz i h h2
      · right
        refine ⟨29 - n, by omega, by omega, ?_, hb⟩
        simp [fnz, beq_false hb]
    · by_cases hb : nb x (29 - n) = 0
      · right
        refine ⟨i, by omega, hi2, ?_, hi4⟩
        simp [fnz, hb, hi3]
      · right
        refine ⟨29 - n, by omega, by omega, ?_, hb⟩
        simp [fnz, beq_false hb]

theorem allIn_of (x v : ℕ) : ∀ n, (∀ i < n, nb x i = 0 ∨ nb x i = v) → allIn x v n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [allIn, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq]
    exact ⟨h n (by omega), allIn_of x v n fun i hi => h i (by omega)⟩

theorem pChk_of (x : ℕ) (h1 : ∀ i < 30, ∀ j < 30, nb x i = 0 ∨ nb x j = 0 ∨ nb x i = nb x j)
    (h2 : ∀ i < 30, nb x i ≠ 0 → goodN (nb x i) = true) : pChk x = true := by
  simp only [pChk, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq]
  rcases fnz_spec x 30 le_rfl with ⟨h0, hz⟩ | ⟨i0, -, hi0, hv, hne⟩
  · rw [h0]
    exact ⟨Or.inl rfl, allIn_of x 0 30 fun i hi => Or.inl (hz i (by omega) hi)⟩
  · rw [hv]
    refine ⟨Or.inr (h2 i0 hi0 hne), allIn_of x _ 30 fun i hi => ?_⟩
    rcases h1 i hi i0 hi0 with h | h | h
    · exact Or.inl h
    · exact absurd h hne
    · exact Or.inr h

theorem fnz_congr {x y : ℕ} (h : ∀ i < 30, nb x i = nb y i) : ∀ n ≤ 30, fnz x n = fnz y n
  | 0, _ => rfl
  | n + 1, hn => by
    simp only [fnz, h (29 - n) (by omega), fnz_congr h n (by omega)]

theorem allIn_congr {x y : ℕ} (v : ℕ) : ∀ n, (∀ i < n, nb x i = nb y i) →
    allIn x v n = allIn y v n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [allIn, h n (by omega), allIn_congr v n fun i hi => h i (by omega)]

theorem pChk_congr {x y : ℕ} (h : ∀ i < 30, nb x i = nb y i) : pChk x = pChk y := by
  simp only [pChk, fnz_congr h 30 le_rfl, allIn_congr _ 30 h]

theorem enumN_sound : ∀ (cs : List ℕ) (acc : ℕ), enumN cs acc = true →
    ∀ bs : List Bool, bs.length = cs.length → leafN (acc ^^^ xorSel bs cs) = true
  | [], acc, h, [], _ => by simpa [xorSel, enumN] using h
  | [], _, _, _ :: _, hl => by simp at hl
  | c :: cs, acc, h, b :: bs, hl => by
    simp only [enumN, Bool.and_eq_true] at h
    simp only [xorSel]
    cases b
    · simpa using enumN_sound cs acc h.1 bs (by simpa using hl)
    · have := enumN_sound cs (acc ^^^ c) h.2 bs (by simpa using hl)
      simpa [Nat.xor_assoc] using this
  | _ :: _, _, _, [], hl => by simp at hl

theorem enumP_sound (cN : List ℕ) : ∀ (cs : List ℕ) (acc : ℕ), enumP cN cs acc = true →
    ∀ bs : List Bool, bs.length = cs.length → pChk (acc ^^^ xorSel bs cs) = true →
      enumN cN (acc ^^^ xorSel bs cs) = true
  | [], acc, h, [], _, hp => by
    simp only [xorSel, Nat.xor_zero] at hp ⊢
    simpa [enumP, hp] using h
  | [], _, _, _ :: _, hl, _ => by simp at hl
  | c :: cs, acc, h, b :: bs, hl, hp => by
    simp only [enumP, Bool.and_eq_true] at h
    simp only [xorSel] at hp ⊢
    cases b
    · simp only [Bool.cond_false, Nat.zero_xor] at hp ⊢
      exact enumP_sound cN cs acc h.1 bs (by simpa using hl) hp
    · simp only [Bool.cond_true, ← Nat.xor_assoc] at hp ⊢
      exact enumP_sound cN cs (acc ^^^ c) h.2 bs (by simpa using hl) hp
  | _ :: _, _, _, [], hl, _ => by simp at hl

theorem exists_witAt {x : ℕ} : ∀ n, witAny x n = true → ∃ i < n, witAt x i = true
  | 0, h => by simp [witAny] at h
  | n + 1, h => by
    simp only [witAny, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨n, by omega, h⟩
    · obtain ⟨i, hi, hw⟩ := exists_witAt n h
      exact ⟨i, by omega, hw⟩

end FL

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
