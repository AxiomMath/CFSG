module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bPhi
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

@[expose] def levTwoS2b_Z {n p : ℕ} (c : Fin n → ZMod p) : Set (Fin n) :=
  {a | levTwoS2b_D c a = 0}

@[expose] def levTwoS2b_Supp (n : ℕ) {p : ℕ} (_c : Fin n → ZMod p)
    (Φ : Set (Fin n → ℤ)) : Set (Fin n) :=
  {a | ∃ β ∈ Φ, levTwoS2b_coord n β a ≠ 0}

theorem levTwoS2b_lam_eps_gen (n p : ℕ) (c : Fin n → ZMod p) {a b : Fin n} (_hab : a ≠ b)
    {s t : ℤ} :
    lam c (levTwoS2b_ofCoord n (Pi.single a s + Pi.single b t)) =
      (s : ZMod p) * levTwoS2b_D c a + (t : ZMod p) * levTwoS2b_D c b := by
  rw [levTwoS2b_lam_ofCoord]
  rw [show (∑ k : Fin n,
      (((Pi.single a s + Pi.single b t : Fin n → ℤ) k : ℤ) : ZMod p) * levTwoS2b_D c k) =
      (s : ZMod p) * levTwoS2b_D c a + (t : ZMod p) * levTwoS2b_D c b from by
    simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Fintype.sum_eq_single a]
      · simp
      · intro k hk; simp [hk]
    · rw [Fintype.sum_eq_single b]
      · simp
      · intro k hk; simp [hk]]

theorem levTwoS2b_intCast_ne_zero' {p : ℕ} [Fact p.Prime] {s : ℤ}
    (hs : s = 1 ∨ s = -1) : (s : ZMod p) ≠ 0 := by
  rcases hs with rfl | rfl
  · rw [Int.cast_one]; exact one_ne_zero
  · rw [Int.cast_neg, Int.cast_one]
    exact neg_ne_zero.mpr one_ne_zero

theorem levTwoS2b_isLong_of_mem_Phi {p : ℕ} (n : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ) {β : Fin n → ℤ} (hβ : β ∈ Φ) :
    levTwoS2b_isLong n β := by
  have h := levTwoS2b_Phi_eq_PhiCase3 n hn p hp hp2 c Φ hΦ
  rw [h] at hβ
  exact hβ.2.1

theorem levTwoS2b_suppRoot_side {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 2 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ) {β : Fin n → ℤ} (hβ : β ∈ Φ) :
    (∀ a, levTwoS2b_coord n β a ≠ 0 → levTwoS2b_D c a = 0) ∨
    (∀ a, levTwoS2b_coord n β a ≠ 0 → levTwoS2b_D c a ≠ 0) := by
  have hlong : levTwoS2b_isLong n β :=
    levTwoS2b_isLong_of_mem_Phi n hn Fact.out hp2 c hΦ hβ
  obtain ⟨i, j, s, t, hij, hs, ht, hcoord⟩ := hlong
  have hβeq : β = levTwoS2b_ofCoord n (Pi.single i s + Pi.single j t) := by
    apply levTwoS2b_coord_injective n
    rw [levTwoS2b_coord_ofCoord, hcoord]
  have hlam := hΦ.fix β hβ
  rw [hβeq, levTwoS2b_lam_eps_gen n p c hij] at hlam
  have hs0 := levTwoS2b_intCast_ne_zero' (p := p) hs
  have ht0 := levTwoS2b_intCast_ne_zero' (p := p) ht
  have hiff : levTwoS2b_D c i = 0 ↔ levTwoS2b_D c j = 0 := by
    constructor
    · intro hi
      have h : (t : ZMod p) * levTwoS2b_D c j = 0 := by
        rw [hi, mul_zero, zero_add] at hlam; exact hlam
      exact (mul_eq_zero.mp h).resolve_left ht0
    · intro hj
      have h : (s : ZMod p) * levTwoS2b_D c i = 0 := by
        rw [hj, mul_zero, add_zero] at hlam; exact hlam
      exact (mul_eq_zero.mp h).resolve_left hs0
  have hmem : ∀ a, levTwoS2b_coord n β a ≠ 0 → a = i ∨ a = j := by
    intro a ha
    rw [hcoord] at ha
    simp only [Pi.add_apply, Pi.single_apply] at ha
    by_cases hai : a = i
    · exact Or.inl hai
    · by_cases haj : a = j
      · exact Or.inr haj
      · simp [hai, haj] at ha
  by_cases hi : levTwoS2b_D c i = 0
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

theorem levTwoS2b_form_eq_zero_of_disjoint (n : ℕ) (hn : 1 ≤ n) {β γ : Fin n → ℤ}
    (h : ∀ a, levTwoS2b_coord n β a ≠ 0 → levTwoS2b_coord n γ a = 0) :
    form (isFiniteType_cartanB n) (toRat β) (toRat γ) = 0 := by
  rw [levTwoS2b_form_coord_kappa n hn]
  have hsum : (∑ k, ((levTwoS2b_coord n β k : ℤ) : ℚ) *
      ((levTwoS2b_coord n γ k : ℤ) : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : levTwoS2b_coord n β k = 0
    · rw [hk, Int.cast_zero, zero_mul]
    · rw [h k hk, Int.cast_zero, mul_zero]
  rw [hsum, mul_zero]

theorem levTwoS2b_supp_nonempty (n : ℕ) {v : Fin n → ℤ} (hv : levTwoS2b_isLong n v) :
    ∃ a, levTwoS2b_coord n v a ≠ 0 := by
  obtain ⟨i, j, s, t, hij, hs, ht, hcoord⟩ := hv
  refine ⟨i, ?_⟩
  rw [hcoord]
  simp only [Pi.add_apply, Pi.single_apply]
  rcases hs with rfl | rfl <;> simp [hij]

theorem levTwoS2b_exists_mem_supp_of_form_ne_zero (n : ℕ) (hn : 1 ≤ n) {β γ : Fin n → ℤ}
    (h : form (isFiniteType_cartanB n) (toRat β) (toRat γ) ≠ 0) :
    ∃ a, levTwoS2b_coord n β a ≠ 0 ∧ levTwoS2b_coord n γ a ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (levTwoS2b_form_eq_zero_of_disjoint n hn fun a ha => hc a ha)

theorem levTwoS2b_side_iff_of_form_ne_zero {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 2 ≤ n)
    (hp2 : p ≠ 2) (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ) {b cc : Fin n → ℤ}
    (hb : b ∈ Φ) (hc : cc ∈ Φ)
    (hform : form (isFiniteType_cartanB n) (toRat b) (toRat cc) ≠ 0) :
    (∀ a, levTwoS2b_coord n b a ≠ 0 → levTwoS2b_D c a = 0) ↔
      (∀ a, levTwoS2b_coord n cc a ≠ 0 → levTwoS2b_D c a = 0) := by
  obtain ⟨a', hba, hca⟩ := levTwoS2b_exists_mem_supp_of_form_ne_zero n (by omega) hform
  have hsideb := levTwoS2b_suppRoot_side n hn hp2 c hΦ hb
  have hsidec := levTwoS2b_suppRoot_side n hn hp2 c hΦ hc
  constructor
  · intro hbZ
    exact hsidec.resolve_right fun hnc => hnc a' hca (hbZ a' hba)
  · intro hcZ
    exact hsideb.resolve_right fun hnb => hnb a' hba (hcZ a' hca)

theorem levTwoS2b_Phi_side {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 2 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ) :
    (∀ β ∈ Φ, ∀ a, levTwoS2b_coord n β a ≠ 0 → levTwoS2b_D c a = 0) ∨
    (∀ β ∈ Φ, ∀ a, levTwoS2b_coord n β a ≠ 0 → levTwoS2b_D c a ≠ 0) := by
  obtain ⟨s, hsΦ, hlin, hcard, hcard2, hdet⟩ := hΦ.rank
  obtain ⟨α, hαs⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hαΦ : α ∈ Φ := hsΦ (Finset.mem_coe.mpr hαs)
  let Srel : (Fin n → ℤ) → (Fin n → ℤ) → Prop :=
    fun x y => y ∈ Φ ∧ form (isFiniteType_cartanB n) (toRat x) (toRat y) ≠ 0
  have key : ∀ y, Relation.ReflTransGen Srel α y →
      (((∀ a, levTwoS2b_coord n y a ≠ 0 → levTwoS2b_D c a = 0) ↔
       (∀ a, levTwoS2b_coord n α a ≠ 0 → levTwoS2b_D c a = 0)) ∧ y ∈ Φ) := by
    intro y hy
    induction hy with
    | refl => exact ⟨Iff.rfl, hαΦ⟩
    | tail hprev hstep ih =>
        exact ⟨((levTwoS2b_side_iff_of_form_ne_zero n hn hp2 c hΦ ih.2 hstep.1
          hstep.2).symm).trans ih.1, hstep.1⟩
  rcases levTwoS2b_suppRoot_side n hn hp2 c hΦ hαΦ with hαZ | hαZc
  · left
    intro β hβ a ha
    exact (key β (hΦ.irred α hαΦ β hβ)).1.mpr hαZ a ha
  · right
    intro β hβ a ha
    have hQβ := levTwoS2b_suppRoot_side n hn hp2 c hΦ hβ
    have hnPα : ¬(∀ a, levTwoS2b_coord n α a ≠ 0 → levTwoS2b_D c a = 0) := by
      intro hP
      obtain ⟨a', ha'⟩ := levTwoS2b_supp_nonempty n
        (levTwoS2b_isLong_of_mem_Phi n hn Fact.out hp2 c hΦ hαΦ)
      exact hαZc a' ha' (hP a' ha')
    exact (hQβ.resolve_left fun hPβ =>
      hnPα ((key β (hΦ.irred α hαΦ β hβ)).1.mp hPβ)) a ha

theorem levTwoS2b_Supp_subset {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 2 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ) :
    levTwoS2b_Supp n c Φ ⊆ levTwoS2b_Z c ∨
    levTwoS2b_Supp n c Φ ⊆ (levTwoS2b_Z c)ᶜ := by
  rcases levTwoS2b_Phi_side n hn hp2 c hΦ with hZ | hZc
  · left
    rintro a ⟨β, hβ, ha⟩
    exact hZ β hβ a ha
  · right
    rintro a ⟨β, hβ, ha⟩
    exact hZc β hβ a ha

@[expose] def levTwoS2b_Q {p : ℕ} (n : ℕ) (c : Fin n → ZMod p) (y : Fin n → ℤ)
    (c₀ : ZMod p) : Prop :=
  ∀ a, levTwoS2b_coord n y a ≠ 0 → levTwoS2b_D c a = c₀ ∨ levTwoS2b_D c a = -c₀

theorem levTwoS2b_d_supp_abs {p : ℕ} [Fact p.Prime] (n : ℕ) (_hn : 2 ≤ n) (_hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ) {β : Fin n → ℤ} (hβ : β ∈ Φ)
    {u v : Fin n} {s t : ℤ} (huv : u ≠ v) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (hβuv : levTwoS2b_coord n β = Pi.single u s + Pi.single v t) :
    levTwoS2b_D c u = levTwoS2b_D c v ∨ levTwoS2b_D c u = - levTwoS2b_D c v := by
  have hβeq : β = levTwoS2b_ofCoord n (Pi.single u s + Pi.single v t) := by
    apply levTwoS2b_coord_injective n
    rw [levTwoS2b_coord_ofCoord, hβuv]
  have hlam := hΦ.fix β hβ
  rw [hβeq, levTwoS2b_lam_eps_gen n p c huv] at hlam
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp only [Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at hlam
  · exact Or.inr (eq_neg_of_add_eq_zero_left hlam)
  · exact Or.inl (add_neg_eq_zero.mp hlam)
  · exact Or.inl (neg_add_eq_zero.mp hlam)
  · exact Or.inr (neg_add_eq_zero.mp hlam)

theorem levTwoS2b_sign_symm {p : ℕ} {x y : ZMod p} (h : x = y ∨ x = -y) :
    y = x ∨ y = -x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · refine Or.inr ?_
    rw [h]; ring

theorem levTwoS2b_sign_trans {p : ℕ} {x y c₀ : ZMod p}
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

theorem levTwoS2b_Q_preserved {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 2 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ)
    {y z : Fin n → ℤ} (_hyΦ : y ∈ Φ) (hzΦ : z ∈ Φ)
    (hform : form (isFiniteType_cartanB n) (toRat y) (toRat z) ≠ 0) {c₀ : ZMod p}
    (_hc₀ : c₀ ≠ 0) : levTwoS2b_Q n c y c₀ → levTwoS2b_Q n c z c₀ := by
  intro hQy a ha
  obtain ⟨a', hya', hza'⟩ := levTwoS2b_exists_mem_supp_of_form_ne_zero n (by omega) hform
  have hda' := hQy a' hya'
  obtain ⟨u, v, s, t, huv, hs, ht, hzu⟩ := levTwoS2b_isLong_of_mem_Phi n hn Fact.out hp2 c hΦ hzΦ
  have hzu_mem : ∀ a, levTwoS2b_coord n z a ≠ 0 → a = u ∨ a = v := by
    intro a ha
    rw [hzu] at ha
    simp only [Pi.add_apply, Pi.single_apply] at ha
    by_cases hu : a = u
    · exact Or.inl hu
    · by_cases hv : a = v
      · exact Or.inr hv
      · simp [hu, hv] at ha
  have hduv := levTwoS2b_d_supp_abs n hn hp2 c hΦ hzΦ huv hs ht hzu
  have ha' : a' = u ∨ a' = v := hzu_mem a' hza'
  have hdu : levTwoS2b_D c u = c₀ ∨ levTwoS2b_D c u = -c₀ := by
    rcases ha' with h | h
    · rw [h] at hda'; exact hda'
    · rw [h] at hda'
      exact levTwoS2b_sign_trans (levTwoS2b_sign_symm hduv) hda'
  have hdv : levTwoS2b_D c v = c₀ ∨ levTwoS2b_D c v = -c₀ := by
    rcases ha' with h | h
    · rw [h] at hda'
      exact levTwoS2b_sign_trans hduv hda'
    · rw [h] at hda'; exact hda'
  rcases hzu_mem a ha with rfl | rfl
  · exact hdu
  · exact hdv

theorem levTwoS2b_Phi_side_abs {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 2 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ) :
    (∀ β ∈ Φ, ∀ a, levTwoS2b_coord n β a ≠ 0 → levTwoS2b_D c a = 0) ∨
    (∃ c₀ : ZMod p, c₀ ≠ 0 ∧ ∀ β ∈ Φ, levTwoS2b_Q n c β c₀) := by
  obtain ⟨s, hsΦ, hlin, hcard, hcard2, hdet⟩ := hΦ.rank
  obtain ⟨α, hαs⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have hαΦ : α ∈ Φ := hsΦ (Finset.mem_coe.mpr hαs)
  obtain ⟨i, j, si, sj, hij, hsi, hsj, hcoord⟩ :=
    levTwoS2b_isLong_of_mem_Phi n hn Fact.out hp2 c hΦ hαΦ
  have hαi : levTwoS2b_coord n α i ≠ 0 := by
    rw [hcoord]
    simp only [Pi.add_apply, Pi.single_apply]
    rcases hsi with rfl | rfl <;> simp [hij]
  rcases levTwoS2b_suppRoot_side n hn hp2 c hΦ hαΦ with hαZ | hαZc
  · left
    rcases levTwoS2b_Phi_side n hn hp2 c hΦ with hZ | hZc
    · exact hZ
    · exfalso
      exact hZc α hαΦ i hαi (hαZ i hαi)
  · right
    let c₀ := levTwoS2b_D c i
    have hc₀ : c₀ ≠ 0 := hαZc i hαi
    have hQα : levTwoS2b_Q n c α c₀ := by
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
      · have := levTwoS2b_d_supp_abs n hn hp2 c hΦ hαΦ hij hsi hsj hcoord
        rcases this with h | h
        · refine Or.inl ?_
          rw [show c₀ = levTwoS2b_D c i from rfl, h]
        · refine Or.inr ?_
          rw [show c₀ = levTwoS2b_D c i from rfl, h]
          exact (neg_neg _).symm
    let Srel : (Fin n → ℤ) → (Fin n → ℤ) → Prop :=
      fun x y => y ∈ Φ ∧ form (isFiniteType_cartanB n) (toRat x) (toRat y) ≠ 0
    have keyQ : ∀ y, Relation.ReflTransGen Srel α y → levTwoS2b_Q n c y c₀ ∧ y ∈ Φ := by
      intro y hy
      induction hy with
      | refl => exact ⟨hQα, hαΦ⟩
      | tail hprev hstep ih =>
          exact ⟨levTwoS2b_Q_preserved n hn hp2 c hΦ ih.2 hstep.1 hstep.2 hc₀ ih.1, hstep.1⟩
    refine ⟨c₀, hc₀, ?_⟩
    intro β hβ
    exact (keyQ β (hΦ.irred α hαΦ β hβ)).1

end CFSG.StandardType.LevTwo
