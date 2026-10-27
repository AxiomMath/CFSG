module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Uni

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix

variable {F : Type} [Field F]

@[expose] def stdF (F : Type) [Field F] (h : ℕ) : Submodule F (Ix3 → F) where
  carrier := {w | InF h w}
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c _ hw k hk => by rw [Pi.smul_apply, hw k hk, smul_zero]

theorem mem_stdF {h : ℕ} {w : Ix3 → F} : w ∈ stdF F h ↔ InF h w := Iff.rfl

theorem stdF_mono {h h' : ℕ} (hh : h ≤ h') : stdF F h ≤ stdF F h' := fun _ hw => hw.mono hh

theorem stdF_six : stdF F 6 = ⊤ := eq_top_iff.mpr fun w _ => inF_six w

theorem stdF_zero : stdF F 0 = ⊥ :=
  eq_bot_iff.mpr fun _ hw => (Submodule.mem_bot F).mpr (eq_zero_of_inF_zero hw)

theorem card_ht_lt {h : ℕ} (hh : h ≤ 6) : Nat.card {k : Ix3 // ht k < h} = h := by
  rw [Nat.card_eq_fintype_card]
  interval_cases h <;> decide

theorem card_stdF [Finite F] {h : ℕ} (hh : h ≤ 6) : Nat.card (stdF F h) = Nat.card F ^ h := by
  classical
  let e : stdF F h ≃ ({k : Ix3 // ht k < h} → F) :=
    { toFun := fun w k => (w : Ix3 → F) k.1
      invFun := fun φ => ⟨fun k => if hk : ht k < h then φ ⟨k, hk⟩ else 0, fun k hk => by
        simp [show ¬ ht k < h by omega]⟩
      left_inv := fun w => by
        apply Subtype.ext
        funext k
        by_cases hk : ht k < h
        · simp [hk]
        · simp only [hk, dite_false]
          exact (w.2 k (by omega)).symm
      right_inv := fun φ => by
        funext k
        simp [k.2] }
  rw [Nat.card_congr e, Nat.card_fun, card_ht_lt hh]

@[expose] def bv : ℕ → Ix3
  | 0 => .inl 0
  | 1 => .inr 2
  | 2 => .inr 1
  | 3 => .inl 1
  | 4 => .inl 2
  | _ => .inr 0

theorem ht_bv {t : ℕ} (ht6 : t < 6) : ht (bv t) = t := by
  interval_cases t <;> rfl

theorem eq_bv_of_ht {k : Ix3} {t : ℕ} (h : ht k = t) : k = bv t := by
  subst h
  rcases k with k | k <;> fin_cases k <;> rfl

theorem ne_zero_of_not_inF {t : ℕ} {w : Ix3 → F} (h1 : InF (t + 1) w) (h0 : ¬ InF t w) :
    w (bv t) ≠ 0 := by
  intro hz
  apply h0
  intro k hk
  rcases Nat.lt_or_ge (ht k) (t + 1) with hlt | hge
  · rw [eq_bv_of_ht (show ht k = t by omega)]
    exact hz
  · exact h1 k hge

omit [Field F] in
theorem q6_apply_inl0 (a b c d e f : F) : q6 a b c d e f (.inl 0) = a := rfl
omit [Field F] in
theorem q6_apply_inl1 (a b c d e f : F) : q6 a b c d e f (.inl 1) = b := rfl
omit [Field F] in
theorem q6_apply_inl2 (a b c d e f : F) : q6 a b c d e f (.inl 2) = c := rfl
omit [Field F] in
theorem q6_apply_inr0 (a b c d e f : F) : q6 a b c d e f (.inr 0) = d := rfl
omit [Field F] in
theorem q6_apply_inr1 (a b c d e f : F) : q6 a b c d e f (.inr 1) = e := rfl
omit [Field F] in
theorem q6_apply_inr2 (a b c d e f : F) : q6 a b c d e f (.inr 2) = f := rfl

theorem inF_q6_iff {h : ℕ} {a b c d e f : F} :
    InF h (q6 a b c d e f) ↔
      (h ≤ 0 → a = 0) ∧ (h ≤ 3 → b = 0) ∧ (h ≤ 4 → c = 0) ∧ (h ≤ 5 → d = 0) ∧
        (h ≤ 2 → e = 0) ∧ (h ≤ 1 → f = 0) := by
  constructor
  · intro hw
    exact ⟨fun hh => hw (.inl 0) hh, fun hh => hw (.inl 1) hh, fun hh => hw (.inl 2) hh,
      fun hh => hw (.inr 0) hh, fun hh => hw (.inr 1) hh, fun hh => hw (.inr 2) hh⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ k hk
    rcases k with k | k <;> fin_cases k
    · exact h0 hk
    · exact h1 hk
    · exact h2 hk
    · exact h3 hk
    · exact h4 hk
    · exact h5 hk

@[expose] def U0Stable [CharP F 2] (S : Submodule F (Ix3 → F)) : Prop :=
  ∀ g ∈ U0 F, ∀ w ∈ S, g2Act g w ∈ S

variable [CharP F 2]

theorem stdF_stable (h : ℕ) : U0Stable (stdF F h) := fun _ hg _ hw => FlagUni.mem hg hw

@[expose] def yE1 (F : Type) [Field F] [CharP F 2] : ↥(cayleyGroup F) := g2Y ![0, 1, 0]

@[expose] def gE12 (F : Type) [Field F] [CharP F 2] : ↥(cayleyGroup F) := g2A (uSL 0 0 1)

theorem yE1_mem_U0 : yE1 F ∈ U0 F := by
  rw [yE1]
  exact g2Y_mem_U0 1 0

theorem gE12_mem_U0 : gE12 F ∈ U0 F := by
  rw [gE12]
  exact g2A_mem_U0 0 0 1

theorem g2Act_yE1_sub (w : Ix3 → F) :
    g2Act (yE1 F) w - w = q6 (w (.inr 2)) 0 (w (.inr 0)) 0 (w (.inl 1)) 0 := by
  rw [yE1, g2Act_g2Y_e12]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem g2Act_gE12_sub (w : Ix3 → F) :
    g2Act (gE12 F) w - w = q6 0 (w (.inl 2)) 0 0 0 (w (.inr 1)) := by
  rw [gE12, g2Act_g2A_uSL]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

theorem exists_lower {S : Submodule F (Ix3 → F)} (hS : U0Stable S) {t : ℕ} (ht5 : t < 5)
    {w : Ix3 → F} (hwS : w ∈ S) (hw : InF (t + 2) w) (hw0 : w (bv (t + 1)) ≠ 0) :
    ∃ w' ∈ S, InF (t + 1) w' ∧ w' (bv t) ≠ 0 := by
  have hy : g2Act (yE1 F) w - w ∈ S := S.sub_mem (hS _ yE1_mem_U0 w hwS) hwS
  have hg : g2Act (gE12 F) w - w ∈ S := S.sub_mem (hS _ gE12_mem_U0 w hwS) hwS
  rw [g2Act_yE1_sub] at hy
  rw [g2Act_gE12_sub] at hg
  conv at hw => rw [q6_eta w]
  rw [inF_q6_iff] at hw
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := hw
  interval_cases t
  · refine ⟨_, hy, ?_, ?_⟩
    · rw [inF_q6_iff]
      exact ⟨by omega, fun _ => rfl, fun _ => h3 (by omega), fun _ => rfl,
        fun _ => h1 (by omega), fun _ => rfl⟩
    · exact hw0
  · refine ⟨_, hg, ?_, ?_⟩
    · rw [inF_q6_iff]
      exact ⟨fun _ => rfl, fun _ => h2 (by omega), fun _ => rfl, fun _ => rfl, fun _ => rfl,
        by omega⟩
    · exact hw0
  · refine ⟨_, hy, ?_, ?_⟩
    · rw [inF_q6_iff]
      exact ⟨by omega, fun _ => rfl, fun _ => h3 (by omega), fun _ => rfl, by omega,
        fun _ => rfl⟩
    · exact hw0
  · refine ⟨_, hg, ?_, ?_⟩
    · rw [inF_q6_iff]
      exact ⟨fun _ => rfl, by omega, fun _ => rfl, fun _ => rfl, fun _ => rfl, by omega⟩
    · exact hw0
  · refine ⟨_, hy, ?_, ?_⟩
    · rw [inF_q6_iff]
      exact ⟨by omega, fun _ => rfl, by omega, fun _ => rfl, by omega, fun _ => rfl⟩
    · exact hw0

theorem stdF_le_of_mem {S : Submodule F (Ix3 → F)} (hS : U0Stable S) {t : ℕ} (ht6 : t < 6) :
    ∀ w ∈ S, InF (t + 1) w → w (bv t) ≠ 0 → stdF F (t + 1) ≤ S := by
  induction t with
  | zero =>
    intro w hwS hw hw0 x hx
    have e : x = (x (bv 0) / w (bv 0)) • w := by
      funext k
      rw [Pi.smul_apply, smul_eq_mul]
      by_cases hk : ht k = 0
      · rw [eq_bv_of_ht hk, div_mul_cancel₀ _ hw0]
      · rw [hx k (by omega), hw k (by omega), mul_zero]
    rw [e]
    exact S.smul_mem _ hwS
  | succ t ih =>
    intro w hwS hw hw0 x hx
    obtain ⟨w', hw'S, hw', hw'0⟩ := exists_lower hS (by omega) hwS hw hw0
    have hle := ih (by omega) w' hw'S hw' hw'0
    have hd : x - (x (bv (t + 1)) / w (bv (t + 1))) • w ∈ stdF F (t + 1) := by
      intro k hk
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hkt : ht k = t + 1
      · rw [eq_bv_of_ht hkt, div_mul_cancel₀ _ hw0, sub_self]
      · rw [hx k (by omega), hw k (by omega), mul_zero, sub_zero]
    have := S.add_mem (hle hd) (S.smul_mem (x (bv (t + 1)) / w (bv (t + 1))) hwS)
    rwa [sub_add_cancel] at this

theorem eq_stdF_of_stable {S : Submodule F (Ix3 → F)} (hS : U0Stable S) :
    ∃ h ≤ 6, S = stdF F h := by
  classical
  have hex : ∃ h, S ≤ stdF F h := ⟨6, by rw [stdF_six]; exact le_top⟩
  obtain ⟨h, hSh, hmin⟩ : ∃ h, S ≤ stdF F h ∧ ∀ h' < h, ¬ S ≤ stdF F h' :=
    ⟨Nat.find hex, Nat.find_spec hex, fun h' hh' => Nat.find_min hex hh'⟩
  have h6 : h ≤ 6 := by
    by_contra hc
    exact hmin 6 (by omega) (by rw [stdF_six]; exact le_top)
  refine ⟨h, h6, le_antisymm hSh ?_⟩
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · rw [h0, stdF_zero]
    exact bot_le
  · obtain ⟨t, rfl⟩ : ∃ t, h = t + 1 := ⟨h - 1, by omega⟩
    have hnot : ¬ S ≤ stdF F t := hmin t (by omega)
    obtain ⟨w, hwS, hwt⟩ := Set.not_subset.mp hnot
    exact stdF_le_of_mem hS (by omega) w hwS (hSh hwS) (ne_zero_of_not_inF (hSh hwS) hwt)

theorem eq_stdF_of_card [Finite F] {S : Submodule F (Ix3 → F)} (hS : U0Stable S) {i : ℕ}
    (hi : Nat.card S = Nat.card F ^ i) : S = stdF F i := by
  obtain ⟨h, h6, rfl⟩ := eq_stdF_of_stable hS
  rw [card_stdF h6] at hi
  rw [Nat.pow_right_injective Finite.one_lt_card hi]

end CFSG.Quasithin.Vol2.Ch11.G2Q8
