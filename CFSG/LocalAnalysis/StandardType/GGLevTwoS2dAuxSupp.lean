module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxPhi
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxFormCoord

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

@[expose] def levTwoS2d_Z {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p) : Set (Fin n) :=
  {a | levTwoS2d_d n hn c a = 0}

@[expose] def levTwoS2d_Supp {p : ℕ} [Fact p.Prime] (n : ℕ) (_hn : 4 ≤ n) (_c : Fin n → ZMod p)
    (Φ : Set (Fin n → ℤ)) : Set (Fin n) :=
  {a | ∃ β ∈ Φ, toStdD n β a ≠ 0}

private theorem levTwoS2d_intCast_ne_zero {p : ℕ} [Fact p.Prime] {s : ℤ}
    (hs : s = 1 ∨ s = -1) : (s : ZMod p) ≠ 0 := by
  rcases hs with rfl | rfl
  · rw [Int.cast_one]; exact (one_ne_zero : (1 : ZMod p) ≠ 0)
  · rw [Int.cast_neg, Int.cast_one]
    exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0)

theorem levTwoS2d_suppRoot_side {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {β : Fin n → ℤ} (hβ : β ∈ Φ) :
    (∀ a, toStdD n β a ≠ 0 → levTwoS2d_d n hn c a = 0) ∨
    (∀ a, toStdD n β a ≠ 0 → levTwoS2d_d n hn c a ≠ 0) := by
  obtain ⟨i, j, s, t, hij, hs, ht, hcoord⟩ :=
    (levTwoS2d_isRt_iff n (by omega) β).1 (hΦ.isRt β hβ)
  have hlam := hΦ.fix β hβ
  rw [levTwoS2d_lam_eps n hn hp2 c hcoord] at hlam
  have hs0 := levTwoS2d_intCast_ne_zero (p := p) hs
  have ht0 := levTwoS2d_intCast_ne_zero (p := p) ht
  have hiff : levTwoS2d_d n hn c i = 0 ↔ levTwoS2d_d n hn c j = 0 := by
    constructor
    · intro hi
      have h : (t : ZMod p) * levTwoS2d_d n hn c j = 0 := by
        rw [hi, mul_zero, zero_add] at hlam; exact hlam
      exact (mul_eq_zero.mp h).resolve_left ht0
    · intro hj
      have h : (s : ZMod p) * levTwoS2d_d n hn c i = 0 := by
        rw [hj, mul_zero, add_zero] at hlam; exact hlam
      exact (mul_eq_zero.mp h).resolve_left hs0
  have hmem : ∀ a, toStdD n β a ≠ 0 → a = i ∨ a = j := by
    intro a ha
    rw [hcoord] at ha
    simp only [Pi.add_apply, Pi.single_apply] at ha
    by_cases hai : a = i
    · exact Or.inl hai
    · by_cases haj : a = j
      · exact Or.inr haj
      · simp [hai, haj] at ha
  by_cases hi : levTwoS2d_d n hn c i = 0
  · left
    intro a ha
    rcases hmem a ha with rfl | rfl
    · exact hi
    · exact hiff.mp hi
  · right
    intro a ha
    rcases hmem a ha with rfl | rfl
    · exact hi
    · intro hj
      exact hi (hiff.mpr hj)

theorem levTwoS2d_form_eq_zero_of_disjoint (n : ℕ) (hn : 4 ≤ n) {β γ : Fin n → ℤ}
    (h : ∀ a, toStdD n β a ≠ 0 → toStdD n γ a = 0) :
    form (isFiniteType_cartanD n) (toRat β) (toRat γ) = 0 := by
  obtain ⟨κ, -, hκ⟩ := levTwoS2d_form_coord n hn
  rw [hκ]
  have hsum : (∑ k, toStdD n β k * toStdD n γ k : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : toStdD n β k = 0
    · rw [hk, zero_mul]
    · rw [h k hk, mul_zero]
  rw [hsum, Int.cast_zero, mul_zero]

private theorem levTwoS2d_supp_nonempty (n : ℕ) (hn : 4 ≤ n) {v : Fin n → ℤ}
    (hv : IsRt (isFiniteType_cartanD n) v) : ∃ a, toStdD n v a ≠ 0 := by
  obtain ⟨i, j, s, t, hij, hs, ht, hcoord⟩ := (levTwoS2d_isRt_iff n (by omega) v).1 hv
  refine ⟨i, ?_⟩
  rw [hcoord]
  simp only [Pi.add_apply, Pi.single_apply]
  rcases hs with rfl | rfl <;> simp [hij]

theorem levTwoS2d_exists_mem_supp_of_form_ne_zero (n : ℕ) (hn : 4 ≤ n) {β γ : Fin n → ℤ}
    (h : form (isFiniteType_cartanD n) (toRat β) (toRat γ) ≠ 0) :
    ∃ a, toStdD n β a ≠ 0 ∧ toStdD n γ a ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (levTwoS2d_form_eq_zero_of_disjoint n hn fun a ha => hc a ha)

theorem levTwoS2d_side_iff_of_form_ne_zero {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n)
    (hp2 : p ≠ 2) (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {b cc : Fin n → ℤ}
    (hb : b ∈ Φ) (hc : cc ∈ Φ)
    (hform : form (isFiniteType_cartanD n) (toRat b) (toRat cc) ≠ 0) :
    (∀ a, toStdD n b a ≠ 0 → levTwoS2d_d n hn c a = 0) ↔
      (∀ a, toStdD n cc a ≠ 0 → levTwoS2d_d n hn c a = 0) := by
  obtain ⟨a', hba, hca⟩ := levTwoS2d_exists_mem_supp_of_form_ne_zero n hn hform
  have hsideb := levTwoS2d_suppRoot_side n hn hp2 c hΦ hb
  have hsidec := levTwoS2d_suppRoot_side n hn hp2 c hΦ hc
  constructor
  · intro hbZ
    exact hsidec.resolve_right fun hnc => hnc a' hca (hbZ a' hba)
  · intro hcZ
    exact hsideb.resolve_right fun hnb => hnb a' hba (hcZ a' hca)

theorem levTwoS2d_Phi_side {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) :
    (∀ β ∈ Φ, ∀ a, toStdD n β a ≠ 0 → levTwoS2d_d n hn c a = 0) ∨
    (∀ β ∈ Φ, ∀ a, toStdD n β a ≠ 0 → levTwoS2d_d n hn c a ≠ 0) := by
  obtain ⟨s, hsΦ, hlin, hcard, hcard2, hdet⟩ := hΦ.rank
  obtain ⟨α, hαs⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hαΦ : α ∈ Φ := hsΦ (show α ∈ (s : Set (Fin n → ℤ)) from Finset.mem_coe.mpr hαs)
  let Srel : (Fin n → ℤ) → (Fin n → ℤ) → Prop :=
    fun x y => y ∈ Φ ∧ form (isFiniteType_cartanD n) (toRat x) (toRat y) ≠ 0
  have key : ∀ y, Relation.ReflTransGen Srel α y →
      (((∀ a, toStdD n y a ≠ 0 → levTwoS2d_d n hn c a = 0) ↔
       (∀ a, toStdD n α a ≠ 0 → levTwoS2d_d n hn c a = 0)) ∧ y ∈ Φ) := by
    intro y hy
    induction hy with
    | refl => exact ⟨Iff.rfl, hαΦ⟩
    | tail hprev hstep ih =>
        exact ⟨((levTwoS2d_side_iff_of_form_ne_zero n hn hp2 c hΦ ih.2 hstep.1
          hstep.2).symm).trans ih.1, hstep.1⟩
  rcases levTwoS2d_suppRoot_side n hn hp2 c hΦ hαΦ with hαZ | hαZc
  · left
    intro β hβ a ha
    exact (key β (hΦ.irred α hαΦ β hβ)).1.mpr hαZ a ha
  · right
    intro β hβ a ha
    have hQβ := levTwoS2d_suppRoot_side n hn hp2 c hΦ hβ
    have hnPα : ¬(∀ a, toStdD n α a ≠ 0 → levTwoS2d_d n hn c a = 0) := by
      intro hP
      obtain ⟨a', ha'⟩ := levTwoS2d_supp_nonempty n hn (hΦ.isRt α hαΦ)
      exact hαZc a' ha' (hP a' ha')
    exact (hQβ.resolve_left fun hPβ =>
      hnPα ((key β (hΦ.irred α hαΦ β hβ)).1.mp hPβ)) a ha

theorem levTwoS2d_Supp_subset {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) :
    levTwoS2d_Supp n hn c Φ ⊆ levTwoS2d_Z n hn c ∨
    levTwoS2d_Supp n hn c Φ ⊆ (levTwoS2d_Z n hn c)ᶜ := by
  rcases levTwoS2d_Phi_side n hn hp2 c hΦ with hZ | hZc
  · left
    rintro a ⟨β, hβ, ha⟩
    exact hZ β hβ a ha
  · right
    rintro a ⟨β, hβ, ha⟩
    exact hZc β hβ a ha

@[expose] def levTwoS2d_Q {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (c : Fin n → ZMod p)
    (y : Fin n → ℤ) (c₀ : ZMod p) : Prop :=
  ∀ a, toStdD n y a ≠ 0 → levTwoS2d_d n hn c a = c₀ ∨ levTwoS2d_d n hn c a = -c₀

theorem levTwoS2d_d_supp_abs {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {β : Fin n → ℤ} (hβ : β ∈ Φ)
    {u v : Fin n} {s t : ℤ} (_huv : u ≠ v) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (hβuv : toStdD n β = Pi.single u s + Pi.single v t) :
    levTwoS2d_d n hn c u = levTwoS2d_d n hn c v ∨
    levTwoS2d_d n hn c u = - levTwoS2d_d n hn c v := by
  have hlam := hΦ.fix β hβ
  rw [levTwoS2d_lam_eps n hn hp2 c hβuv] at hlam
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp only [Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at hlam
  · exact Or.inr (eq_neg_of_add_eq_zero_left hlam)
  · exact Or.inl (add_neg_eq_zero.mp hlam)
  · exact Or.inl (neg_add_eq_zero.mp hlam)
  · exact Or.inr (neg_add_eq_zero.mp hlam)

private theorem levTwoS2d_sign_symm {p : ℕ} {x y : ZMod p} (h : x = y ∨ x = -y) :
    y = x ∨ y = -x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · refine Or.inr ?_
    rw [h]; ring

private theorem levTwoS2d_sign_trans {p : ℕ} {x y c₀ : ZMod p}
    (hxy : x = y ∨ x = -y) (hx : x = c₀ ∨ x = -c₀) : y = c₀ ∨ y = -c₀ := by
  rcases hxy with h | h
  · rcases hx with hx | hx
    · exact Or.inl (h.symm.trans hx)
    · exact Or.inr (h.symm.trans hx)
  · rcases hx with hx | hx
    · refine Or.inr ?_
      calc y = -x := by rw [h]; ring
        _ = -c₀ := by rw [hx]
    · refine Or.inl ?_
      calc y = -x := by rw [h]; ring
        _ = c₀ := by rw [hx]; ring

theorem levTwoS2d_Q_preserved {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ)
    {y z : Fin n → ℤ} (_hyΦ : y ∈ Φ) (hzΦ : z ∈ Φ)
    (hform : form (isFiniteType_cartanD n) (toRat y) (toRat z) ≠ 0) {c₀ : ZMod p}
    (_hc₀ : c₀ ≠ 0) : levTwoS2d_Q n hn c y c₀ → levTwoS2d_Q n hn c z c₀ := by
  intro hQy a ha
  obtain ⟨a', hya', hza'⟩ := levTwoS2d_exists_mem_supp_of_form_ne_zero n hn hform
  have hda' := hQy a' hya'
  obtain ⟨u, v, s, t, huv, hs, ht, hzu⟩ :=
    (levTwoS2d_isRt_iff n (by omega) z).1 (hΦ.isRt z hzΦ)
  have hzu_mem : ∀ a, toStdD n z a ≠ 0 → a = u ∨ a = v := by
    intro a ha
    rw [hzu] at ha
    simp only [Pi.add_apply, Pi.single_apply] at ha
    by_cases hu : a = u
    · exact Or.inl hu
    · by_cases hv : a = v
      · exact Or.inr hv
      · simp [hu, hv] at ha
  have hduv := levTwoS2d_d_supp_abs n hn hp2 c hΦ hzΦ huv hs ht hzu
  have ha' : a' = u ∨ a' = v := hzu_mem a' hza'
  have hdu : levTwoS2d_d n hn c u = c₀ ∨ levTwoS2d_d n hn c u = -c₀ := by
    rcases ha' with h | h
    · rw [h] at hda'; exact hda'
    · rw [h] at hda'
      exact levTwoS2d_sign_trans (levTwoS2d_sign_symm hduv) hda'
  have hdv : levTwoS2d_d n hn c v = c₀ ∨ levTwoS2d_d n hn c v = -c₀ := by
    rcases ha' with h | h
    · rw [h] at hda'
      exact levTwoS2d_sign_trans hduv hda'
    · rw [h] at hda'; exact hda'
  rcases hzu_mem a ha with rfl | rfl
  · exact hdu
  · exact hdv

theorem levTwoS2d_Phi_side_abs {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) :
    (∀ β ∈ Φ, ∀ a, toStdD n β a ≠ 0 → levTwoS2d_d n hn c a = 0) ∨
    (∃ c₀ : ZMod p, c₀ ≠ 0 ∧ ∀ β ∈ Φ, levTwoS2d_Q n hn c β c₀) := by
  obtain ⟨s, hsΦ, hlin, hcard, hcard2, hdet⟩ := hΦ.rank
  obtain ⟨α, hαs⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hαΦ : α ∈ Φ := hsΦ (show α ∈ (s : Set (Fin n → ℤ)) from Finset.mem_coe.mpr hαs)
  obtain ⟨i, j, si, sj, hij, hsi, hsj, hcoord⟩ :=
    (levTwoS2d_isRt_iff n (by omega) α).1 (hΦ.isRt α hαΦ)
  have hαi : toStdD n α i ≠ 0 := by
    rw [hcoord]
    simp only [Pi.add_apply, Pi.single_apply]
    rcases hsi with rfl | rfl <;> simp [hij]
  rcases levTwoS2d_suppRoot_side n hn hp2 c hΦ hαΦ with hαZ | hαZc
  · left
    rcases levTwoS2d_Phi_side n hn hp2 c hΦ with hZ | hZc
    · exact hZ
    · exfalso
      exact hZc α hαΦ i hαi (hαZ i hαi)
  · right
    let c₀ := levTwoS2d_d n hn c i
    have hc₀ : c₀ ≠ 0 := hαZc i hαi
    have hQα : levTwoS2d_Q n hn c α c₀ := by
      intro a ha
      have hmem : a = i ∨ a = j := by
        rw [hcoord] at ha
        simp only [Pi.add_apply, Pi.single_apply] at ha
        by_cases hi : a = i
        · exact Or.inl hi
        · by_cases hj : a = j
          · exact Or.inr hj
          · simp [hi, hj] at ha
      rcases hmem with rfl | rfl
      · exact Or.inl rfl
      · have := levTwoS2d_d_supp_abs n hn hp2 c hΦ hαΦ hij hsi hsj hcoord
        rcases this with h | h
        · refine Or.inl ?_
          rw [show c₀ = levTwoS2d_d n hn c i from rfl, h]
        · refine Or.inr ?_
          rw [show c₀ = levTwoS2d_d n hn c i from rfl, h]
          exact (neg_neg _).symm
    let Srel : (Fin n → ℤ) → (Fin n → ℤ) → Prop :=
      fun x y => y ∈ Φ ∧ form (isFiniteType_cartanD n) (toRat x) (toRat y) ≠ 0
    have keyQ : ∀ y, Relation.ReflTransGen Srel α y → levTwoS2d_Q n hn c y c₀ ∧ y ∈ Φ := by
      intro y hy
      induction hy with
      | refl => exact ⟨hQα, hαΦ⟩
      | tail hprev hstep ih =>
          exact ⟨levTwoS2d_Q_preserved n hn hp2 c hΦ ih.2 hstep.1 hstep.2 hc₀ ih.1, hstep.1⟩
    refine ⟨c₀, hc₀, ?_⟩
    intro β hβ
    exact (keyQ β (hΦ.irred α hαΦ β hβ)).1

end CFSG.StandardType.LevTwo

