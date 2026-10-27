module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RCore

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes

@[expose] def flagScaleLab (F : ℕ) (l : TcrLab) : TcrLab := ⟨l.t, l.r, l.n * F⟩

section Flag

theorem flagTransfer_refl (p F : ℕ) : FlagTransfer p F F :=
  fun _ => ⟨id, id, fun _ => id⟩

theorem flag_div_two_mul {n F : ℕ} (hn : n % 2 = 0) : n * F / 2 = n / 2 * F := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
  rw [show 2 * m / 2 = m by omega, show 2 * m * F = 2 * (m * F) by ring]
  exact Nat.mul_div_cancel_left (m * F) (by norm_num)

theorem flagComponentLabel_scale (r N : ℕ) (k : TcrKind) (e F : ℕ) :
    tcrComponentLabel r N k (e * F) = flagScaleLab F (tcrComponentLabel r N k e) := by
  cases k <;> simp only [tcrComponentLabel, flagScaleLab] <;> (try split_ifs) <;> rfl

theorem flagLabelClass_scale {F : ℕ} (hF : F % 2 = 1) (l : TcrLab) :
    tcrLabelClass (flagScaleLab F l) = (tcrLabelClass l).map (flagScaleLab F) := by
  obtain ⟨t, r, n⟩ := l
  have hpar : n * F % 2 = n % 2 := by rw [Nat.mul_mod, hF]; omega
  show tcrLabelClass ⟨t, r, n * F⟩ = (tcrLabelClass ⟨t, r, n⟩).map (flagScaleLab F)
  simp only [tcrLabelClass, List.map_cons]
  congr 1
  cases t
  ·
    simp only [hpar]
    split_ifs with h1 h2
    · rfl
    · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h2
      obtain ⟨-, hn⟩ := h2
      simp only [flagScaleLab, flag_div_two_mul hn, List.map_cons, List.map_nil]
    · rfl
  ·
    simp only
    split_ifs <;> rfl
  ·
    simp only
    split_ifs <;> rfl
  ·
    simp only
    split_ifs with h1 h2
    · rfl
    · simp only [flagScaleLab, mul_assoc, List.map_cons, List.map_nil]
    · rfl
  all_goals simp only [List.map_nil]

theorem flagLabsOf_scale {F : ℕ} (hF : F % 2 = 1) (d : TcrCData) :
    tcrLabsOf d F = (tcrLabsOf d 1).map (flagScaleLab F) := by
  unfold tcrLabsOf
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [mul_one, flagComponentLabel_scale, flagLabelClass_scale hF]

theorem flagTwoPow_sub_one (m : ℕ) : ((2 ^ m - 1) % 3 == 0) = (m % 2 == 0) := by
  have h := tc_two_pow_mod_three m
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  split_ifs at h <;> omega

theorem flagTwoPow_add_one (m : ℕ) : ((2 ^ m + 1) % 3 == 0) = (m % 2 == 1) := by
  have h := tc_two_pow_mod_three m
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  split_ifs at h <;> omega

theorem flagSplit_three_congr {t : TcrTg} {r n n' : ℕ} (hpar : n % 2 = n' % 2)
    (h1 : (n == 1) = (n' == 1)) :
    tcrSplitT 3 ⟨t, r, n⟩ = tcrSplitT 3 ⟨t, r, n'⟩ := by
  have ha : ((2 ^ n - 1) % 3 == 0) = ((2 ^ n' - 1) % 3 == 0) := by
    rw [flagTwoPow_sub_one, flagTwoPow_sub_one, hpar]
  have hb : ((2 ^ n + 1) % 3 == 0) = ((2 ^ n' + 1) % 3 == 0) := by
    rw [flagTwoPow_add_one, flagTwoPow_add_one, hpar]
  simp only [tcrSplitT, ha, hb, h1]

theorem flagHalfSplit_three_congr {t : TcrTg} {r n n' : ℕ} (hpar : n % 2 = n' % 2)
    (h1 : (n == 1) = (n' == 1)) :
    tcrHalfSplitT 3 ⟨t, r, n⟩ = tcrHalfSplitT 3 ⟨t, r, n'⟩ := by
  have ha : ((2 ^ n - 1) % 3 == 0) = ((2 ^ n' - 1) % 3 == 0) := by
    rw [flagTwoPow_sub_one, flagTwoPow_sub_one, hpar]
  have hb : ((2 ^ n + 1) % 3 == 0) = ((2 ^ n' + 1) % 3 == 0) := by
    rw [flagTwoPow_add_one, flagTwoPow_add_one, hpar]
  simp only [tcrHalfSplitT, flagSplit_three_congr hpar h1, ha, hb, Nat.reduceBEq,
    Bool.and_false, Bool.or_false]

theorem flagScale_congr {F : ℕ} (hF : F % 2 = 1) (h3 : 3 ≤ F) (n : ℕ) :
    n * F % 2 = n * 3 % 2 ∧ ((n * F == 1) = (n * 3 == 1)) := by
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_mod, hF]; omega
  · have h1 : n * F ≠ 1 := by
      intro h
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp at h
      · have : F ≤ n * F := Nat.le_mul_of_pos_left F hn
        omega
    have h2 : n * 3 ≠ 1 := by omega
    simp [h1, h2]

theorem flagSplit_scale_eq {F : ℕ} (hF : F % 2 = 1) (h3 : 3 ≤ F) (l : TcrLab) :
    tcrSplitT 3 (flagScaleLab F l) = tcrSplitT 3 (flagScaleLab 3 l) := by
  obtain ⟨t, r, n⟩ := l
  obtain ⟨h1, h2⟩ := flagScale_congr hF h3 n
  exact flagSplit_three_congr h1 h2

theorem flagHalfSplit_scale_eq {F : ℕ} (hF : F % 2 = 1) (h3 : 3 ≤ F) (l : TcrLab) :
    tcrHalfSplitT 3 (flagScaleLab F l) = tcrHalfSplitT 3 (flagScaleLab 3 l) := by
  obtain ⟨t, r, n⟩ := l
  obtain ⟨h1, h2⟩ := flagScale_congr hF h3 n
  exact flagHalfSplit_three_congr h1 h2

theorem flagScale_injective {F : ℕ} (hF : F % 2 = 1) : Function.Injective (flagScaleLab F) := by
  rintro ⟨t, r, n⟩ ⟨t', r', n'⟩ h
  have hpos : 0 < F := by omega
  simp only [flagScaleLab, TcrLab.mk.injEq] at h
  obtain ⟨rfl, rfl, h3⟩ := h
  rw [Nat.eq_of_mul_eq_mul_right hpos h3]

theorem flagAnyContains {F : ℕ} (hF : F % 2 = 1) (L1 L2 : List TcrLab) :
    (L2.map (flagScaleLab F)).any (fun l => (L1.map (flagScaleLab F)).contains l) =
      L2.any (fun l => L1.contains l) := by
  have hinj := flagScale_injective hF
  rw [List.any_map]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff]
  simp [hinj.eq_iff]

theorem flagTransfer_three {F : ℕ} (hF : F % 2 = 1) (h3 : 3 ≤ F) : FlagTransfer 3 F 3 := by
  have h3odd : (3 : ℕ) % 2 = 1 := by norm_num
  intro d
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp only [flagLabsOf_scale hF, flagLabsOf_scale h3odd, List.any_map, Function.comp_def,
      flagSplit_scale_eq hF h3] at h ⊢
    exact h
  · intro h
    simp only [flagLabsOf_scale hF, flagLabsOf_scale h3odd, List.any_map, Function.comp_def,
      flagHalfSplit_scale_eq hF h3] at h ⊢
    exact h
  · intro d2 h
    simp only [flagLabsOf_scale hF, flagLabsOf_scale h3odd, flagAnyContains hF,
      flagAnyContains h3odd] at h ⊢
    exact h

theorem flagComponentLabel_n (r N : ℕ) (k : TcrKind) (n : ℕ) :
    (tcrComponentLabel r N k n).n = n := by
  cases k <;> simp only [tcrComponentLabel] <;> (try split_ifs) <;> rfl

theorem flagLabelClass_scale_even {m : ℕ} (l : TcrLab) (hl : l.n % 2 = 0) :
    tcrLabelClass (flagScaleLab m l) = (tcrLabelClass l).map (flagScaleLab m) := by
  obtain ⟨t, r, n⟩ := l
  have hl' : n % 2 = 0 := hl
  have hpar : n * m % 2 = 0 := by rw [Nat.mul_mod, hl']; simp
  show tcrLabelClass ⟨t, r, n * m⟩ = (tcrLabelClass ⟨t, r, n⟩).map (flagScaleLab m)
  simp only [tcrLabelClass, List.map_cons]
  congr 1
  cases t
  · simp only [hpar, hl']
    split_ifs with h1 h2
    · rfl
    · simp only [flagScaleLab, flag_div_two_mul hl', List.map_cons, List.map_nil]
    · rfl
  · simp only
    split_ifs <;> rfl
  · simp only
    split_ifs <;> rfl
  · simp only
    split_ifs with h1 h2
    · rfl
    · simp only [flagScaleLab, mul_assoc, List.map_cons, List.map_nil]
    · rfl
  all_goals simp only [List.map_nil]

theorem flagLabsOf_scale_even {m : ℕ} (d : TcrCData) :
    tcrLabsOf d (2 * m) = (tcrLabsOf d 2).map (flagScaleLab m) := by
  unfold tcrLabsOf
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [show d.e * (2 * m) = d.e * 2 * m by ring, flagComponentLabel_scale]
  exact flagLabelClass_scale_even _ (by simp [flagComponentLabel_n])

theorem flagClass_parity (l : TcrLab) (hl : l.n % 2 = 0) :
    ∀ l' ∈ tcrLabelClass l, l'.n % 2 = 0 ∨ l'.t = TcrTg.twD := by
  intro l' hl'
  obtain ⟨t, r, n⟩ := l
  have hl0 : n % 2 = 0 := hl
  unfold tcrLabelClass at hl'
  rw [List.mem_cons] at hl'
  rcases hl' with rfl | h
  · exact Or.inl hl0
  · cases t <;> simp only [List.not_mem_nil] at h <;>
      (try split_ifs at h) <;> simp_all

theorem flagSplit_twD (r n : ℕ) : tcrSplitT 3 ⟨TcrTg.twD, r, n⟩ = true := by
  have h1 := flagTwoPow_sub_one n
  have h2 := flagTwoPow_add_one n
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [tcrSplitT, tcrUntw, h1, h2, h]
  · simp [tcrSplitT, tcrUntw, h1, h2, h]

theorem flagSplit_even_scale {m : ℕ} (_hm : 0 < m) (l : TcrLab)
    (hl : l.n % 2 = 0 ∨ l.t = TcrTg.twD) :
    tcrSplitT 3 (flagScaleLab m l) = tcrSplitT 3 l := by
  obtain ⟨t, r, n⟩ := l
  rcases hl with hl | hl
  · have hl0 : n % 2 = 0 := hl
    have hpar : n * m % 2 = 0 := by rw [Nat.mul_mod, hl0]; simp
    have hn1 : n ≠ 1 := by omega
    have hnm1 : n * m ≠ 1 := by omega
    exact flagSplit_three_congr (by rw [hpar, hl0]) (by simp [hn1, hnm1])
  · have ht : t = TcrTg.twD := hl
    subst ht
    rw [flagSplit_twD]
    exact flagSplit_twD _ _

theorem flagHalfSplit_even_scale {m : ℕ} (_hm : 0 < m) (l : TcrLab)
    (hl : l.n % 2 = 0 ∨ l.t = TcrTg.twD) :
    tcrHalfSplitT 3 (flagScaleLab m l) = tcrHalfSplitT 3 l := by
  obtain ⟨t, r, n⟩ := l
  rcases hl with hl | hl
  · have hl0 : n % 2 = 0 := hl
    have hpar : n * m % 2 = 0 := by rw [Nat.mul_mod, hl0]; simp
    have hn1 : n ≠ 1 := by omega
    have hnm1 : n * m ≠ 1 := by omega
    exact flagHalfSplit_three_congr (by rw [hpar, hl0]) (by simp [hn1, hnm1])
  · have ht : t = TcrTg.twD := hl
    subst ht
    have h1 : tcrSplitT 3 (flagScaleLab m ⟨TcrTg.twD, r, n⟩) = true := flagSplit_twD r (n * m)
    have h2 : tcrSplitT 3 ⟨TcrTg.twD, r, n⟩ = true := flagSplit_twD r n
    simp only [tcrHalfSplitT, h1, h2, Bool.true_or]

theorem flagScale_injective_pos {F : ℕ} (hpos : 0 < F) : Function.Injective (flagScaleLab F) := by
  rintro ⟨t, r, n⟩ ⟨t', r', n'⟩ h
  simp only [flagScaleLab, TcrLab.mk.injEq] at h
  obtain ⟨rfl, rfl, h3⟩ := h
  rw [Nat.eq_of_mul_eq_mul_right hpos h3]

theorem flagAnyContains_pos {F : ℕ} (hpos : 0 < F) (L1 L2 : List TcrLab) :
    (L2.map (flagScaleLab F)).any (fun l => (L1.map (flagScaleLab F)).contains l) =
      L2.any (fun l => L1.contains l) := by
  have hinj := flagScale_injective_pos hpos
  rw [List.any_map]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [Bool.eq_iff_iff]
  simp [hinj.eq_iff]

theorem flagTransfer_even {F : ℕ} (hF : F % 2 = 0) (h2 : 2 ≤ F) : FlagTransfer 3 F 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, F = 2 * m := ⟨F / 2, by omega⟩
  have hm : 0 < m := by omega
  have hgood : ∀ d : TcrCData, ∀ l ∈ tcrLabsOf d 2, l.n % 2 = 0 ∨ l.t = TcrTg.twD := by
    intro d l hl
    unfold tcrLabsOf at hl
    rw [List.mem_flatMap] at hl
    obtain ⟨k, -, hk⟩ := hl
    exact flagClass_parity _ (by simp [flagComponentLabel_n]) l hk
  intro d
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [flagLabsOf_scale_even, List.any_map] at h
    rw [List.any_eq_true] at h ⊢
    obtain ⟨l, hl, hs⟩ := h
    refine ⟨l, hl, ?_⟩
    simpa [Function.comp_apply, flagSplit_even_scale hm l (hgood d l hl)] using hs
  · intro h
    rw [flagLabsOf_scale_even, List.any_map] at h
    rw [List.any_eq_true] at h ⊢
    obtain ⟨l, hl, hs⟩ := h
    refine ⟨l, hl, ?_⟩
    simpa [Function.comp_apply, flagHalfSplit_even_scale hm l (hgood d l hl)] using hs
  · intro d2 h
    simp only [flagLabsOf_scale_even, flagAnyContains_pos hm] at h ⊢
    exact h

end Flag

end CFSG.StandardType.TableCRes

end
