module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bForm
public import CFSG.LocalAnalysis.StandardType.GGLevTwoTrans
import Mathlib.Algebra.Field.ZMod
import CFSG.ClassicalInvolution.ModelFacts.Families
import CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem levTwoS2b_dot_single_self (n : ℕ) (a : Fin n) (s : ℤ) :
    ∑ k : Fin n, ((Pi.single a s : Fin n → ℤ) k : ℚ) *
        ((Pi.single a s : Fin n → ℤ) k : ℚ) = (s : ℚ) * (s : ℚ) := by
  rw [Fintype.sum_eq_single a]
  · simp
  · intro k hk
    simp [hk]

theorem levTwoS2b_dot_single_ne (n : ℕ) {a b : Fin n} (hab : a ≠ b) (s t : ℤ) :
    ∑ k : Fin n, ((Pi.single a s : Fin n → ℤ) k : ℚ) *
        ((Pi.single b t : Fin n → ℤ) k : ℚ) = 0 := by
  rw [Fintype.sum_eq_single a]
  · simp [hab]
  · intro k hk
    simp [Pi.single_apply, hk]

theorem levTwoS2b_dot_add_self (n : ℕ) {a b : Fin n} (hab : a ≠ b) (s t : ℤ) :
    ∑ k : Fin n, ((Pi.single a s + Pi.single b t : Fin n → ℤ) k : ℚ) *
        ((Pi.single a s + Pi.single b t : Fin n → ℤ) k : ℚ) =
      (s : ℚ) * (s : ℚ) + (t : ℚ) * (t : ℚ) := by
  simp only [Pi.add_apply, Int.cast_add, add_mul, mul_add, Finset.sum_add_distrib]
  rw [levTwoS2b_dot_single_self n a s, levTwoS2b_dot_single_ne n hab s t,
    levTwoS2b_dot_single_ne n hab.symm t s, levTwoS2b_dot_single_self n b t]
  ring

theorem levTwoS2b_dot_single_mul (n : ℕ) (a b : Fin n) (s t : ℤ) :
    ∑ k : Fin n, ((Pi.single a s : Fin n → ℤ) k : ℚ) *
        ((Pi.single b t : Fin n → ℤ) k : ℚ) = if a = b then (s : ℚ) * (t : ℚ) else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [Fintype.sum_eq_single a]
    · simp
    · intro k hk
      simp [hk]
  · rw [Fintype.sum_eq_single a]
    · simp [hab]
    · intro k hk
      simp [Pi.single_apply, hk]

theorem levTwoS2b_form_self_short (n : ℕ) (hn : 1 ≤ n) {β : Fin n → ℤ}
    (hs : levTwoS2b_isShort n β) :
    form (isFiniteType_cartanB n) (toRat β) (toRat β) = levTwoS2b_kappa n hn := by
  simp only [levTwoS2b_isShort, levTwoS2b_shortCoord] at hs
  obtain ⟨a, s, hs', hcoord⟩ := hs
  rw [levTwoS2b_form_coord_kappa n hn, hcoord, levTwoS2b_dot_single_self]
  rcases hs' with rfl | rfl <;> ring

theorem levTwoS2b_form_self_long (n : ℕ) (hn : 1 ≤ n) {β : Fin n → ℤ}
    (hl : levTwoS2b_isLong n β) :
    form (isFiniteType_cartanB n) (toRat β) (toRat β) = 2 * levTwoS2b_kappa n hn := by
  simp only [levTwoS2b_isLong, levTwoS2b_longCoord] at hl
  obtain ⟨a, b, s, t, hab, hs, ht, hcoord⟩ := hl
  rw [levTwoS2b_form_coord_kappa n hn, hcoord, levTwoS2b_dot_add_self n hab s t]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> ring

theorem levTwoS2b_isShort_or_isLong (n : ℕ) {β : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_cartanB n) β) :
    levTwoS2b_isShort n β ∨ levTwoS2b_isLong n β := by
  rw [levTwoS2b_isRt_iff_coord] at hβ
  rcases hβ with ⟨i, j, s, t, hij, hs, ht, hcoord⟩ | ⟨i, s, hs, hcoord⟩
  · right
    simp only [levTwoS2b_isLong, levTwoS2b_longCoord]
    exact ⟨i, j, s, t, hij, hs, ht, hcoord⟩
  · left
    simp only [levTwoS2b_isShort, levTwoS2b_shortCoord]
    exact ⟨i, s, hs, hcoord⟩

theorem levTwoS2b_short_short_step (n : ℕ) (hn : 1 ≤ n) {γ β : Fin n → ℤ}
    (hγ : levTwoS2b_isShort n γ) (hβ : levTwoS2b_isShort n β)
    (h : form (isFiniteType_cartanB n) (toRat γ) (toRat β) ≠ 0) :
    levTwoS2b_coord n β = levTwoS2b_coord n γ ∨
      levTwoS2b_coord n β = -levTwoS2b_coord n γ := by
  simp only [levTwoS2b_isShort, levTwoS2b_shortCoord] at hγ hβ
  obtain ⟨a, s, hs, hcγ⟩ := hγ
  obtain ⟨b, t, ht, hcβ⟩ := hβ
  rw [levTwoS2b_form_coord_kappa n hn, hcγ, hcβ, levTwoS2b_dot_single_mul] at h
  have hκ : levTwoS2b_kappa n hn ≠ 0 := (levTwoS2b_kappa_pos n hn).ne'
  have h2 : (if a = b then (s : ℚ) * (t : ℚ) else 0) ≠ 0 := by
    intro h0
    exact h (by rw [h0, mul_zero])
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl] at h2
    rw [hcβ, hcγ]
    have hst : t * s = 1 ∨ t * s = -1 := by
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num
    have hsingle : (Pi.single a t : Fin n → ℤ) = (t * s) • Pi.single a s := by
      funext k
      by_cases hk : k = a
      · subst hk
        simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
        rw [mul_assoc, hss, mul_one]
      · simp [hk]
    rw [hsingle]
    rcases hst with h1 | h1
    · left
      rw [h1, one_smul]
    · right
      rw [h1, neg_one_smul]
  · rw [if_neg hab] at h2
    exact absurd rfl h2

theorem levTwoS2b_no_short (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_cartanB n) p c Φ) :
    ∀ β ∈ Φ, ¬ levTwoS2b_isShort n β := by
  intro β hβΦ hβshort
  have hn1 : 1 ≤ n := by omega
  have hallshort : ∀ γ ∈ Φ, levTwoS2b_isShort n γ := by
    intro γ hγΦ
    have hγRt := h.isRt γ hγΦ
    rcases levTwoS2b_isShort_or_isLong n hγRt with hs | hl
    · exact hs
    · exfalso
      have hlen := h.oneLen β hβΦ γ hγΦ
      rw [levTwoS2b_form_self_short n hn1 hβshort,
        levTwoS2b_form_self_long n hn1 hl] at hlen
      have hκpos := levTwoS2b_kappa_pos n hn1
      linarith
  obtain ⟨s, hs, h3, -⟩ := levTwoS2b_rank_bounds n hn p c Φ h
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨α, hαs⟩ := hne
  have hαΦ : α ∈ Φ := hs hαs
  set R : (Fin n → ℤ) → (Fin n → ℤ) → Prop :=
    fun a b => b ∈ Φ ∧ form (isFiniteType_cartanB n) (toRat a) (toRat b) ≠ 0
  have chain_mem : ∀ b, Relation.ReflTransGen R α b → b ∈ Φ := by
    intro b hb
    induction hb with
    | refl => exact hαΦ
    | tail hab hbc ih => exact hbc.1
  have hconn : ∀ δ, Relation.ReflTransGen R α δ →
      levTwoS2b_coord n δ = levTwoS2b_coord n α ∨
        levTwoS2b_coord n δ = -levTwoS2b_coord n α := by
    intro δ hirr
    induction hirr with
    | refl => exact Or.inl rfl
    | tail hab hbc ih =>
        have hbshort : levTwoS2b_isShort n _ := hallshort _ (chain_mem _ hab)
        have hδshort : levTwoS2b_isShort n _ := hallshort _ hbc.1
        rcases levTwoS2b_short_short_step n hn1 hbshort hδshort hbc.2 with hc | hc
        · rw [hc]; exact ih
        · rw [hc]
          rcases ih with hh | hh
          · exact Or.inr (by rw [hh])
          · exact Or.inl (by rw [hh, neg_neg])
  have hsub : Φ ⊆ ({α, -α} : Set (Fin n → ℤ)) := by
    intro δ hδΦ
    have hc := hconn δ (h.irred α hαΦ δ hδΦ)
    rcases hc with hc | hc
    · left
      exact levTwoS2b_coord_injective n hc
    · right
      apply levTwoS2b_coord_injective n
      rw [levTwoS2b_coord_neg, hc]
  have hle : s.card ≤ 2 := by
    have hsub' : s ⊆ ({α, -α} : Finset (Fin n → ℤ)) := by
      intro δ hδs
      have hmem := hsub (hs hδs)
      simpa using hmem
    calc s.card ≤ ({α, -α} : Finset (Fin n → ℤ)).card := Finset.card_le_card hsub'
      _ ≤ 2 := by
        have hcard := Finset.card_insert_le α ({-α} : Finset (Fin n → ℤ))
        simp only [Finset.card_singleton] at hcard
        omega
  omega

theorem levTwoS2b_Phi_eq_PhiCase3 (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_cartanB n) p c Φ) :
    Φ = levTwoS2b_PhiCase3 n p c := by
  have hn1 : 1 ≤ n := by omega
  ext β
  constructor
  · intro hβ
    have hRt := h.isRt β hβ
    have hlong : levTwoS2b_isLong n β := by
      rcases levTwoS2b_isShort_or_isLong n hRt with hs | hl
      · exact absurd hs (levTwoS2b_no_short n hn p hp hp2 c Φ h β hβ)
      · exact hl
    exact ⟨hRt, hlong, h.fix β hβ⟩
  · intro hβ
    obtain ⟨hRt, hlong, hlam⟩ := hβ
    obtain ⟨s, hs, h3, -⟩ := levTwoS2b_rank_bounds n hn p c Φ h
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨α, hαs⟩ := hne
    have hαΦ : α ∈ Φ := hs hαs
    have hαRt := h.isRt α hαΦ
    have hαlong : levTwoS2b_isLong n α := by
      rcases levTwoS2b_isShort_or_isLong n hαRt with hs' | hl
      · exact absurd hs' (levTwoS2b_no_short n hn p hp hp2 c Φ h α hαΦ)
      · exact hl
    have hlen : form (isFiniteType_cartanB n) (toRat α) (toRat α) =
        form (isFiniteType_cartanB n) (toRat β) (toRat β) := by
      rw [levTwoS2b_form_self_long n hn1 hαlong, levTwoS2b_form_self_long n hn1 hlong]
    obtain ⟨w, hw⟩ := exists_weylAction_eq_of_isRt (isFiniteType_cartanB n)
      (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanB (by omega)) hαRt hRt hlen
    exact h.sat β hRt hlam ⟨α, hαΦ, w, hw⟩

theorem levTwoS2b_isRt_ofCoord_long (n : ℕ) {a b : Fin n} {s t : ℤ} (hab : a ≠ b)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    IsRt (isFiniteType_cartanB n) (levTwoS2b_ofCoord n (Pi.single a s + Pi.single b t)) := by
  rw [levTwoS2b_isRt_iff_coord, levTwoS2b_coord_ofCoord]
  exact Or.inl ⟨a, b, s, t, hab, hs, ht, rfl⟩

theorem levTwoS2b_isLong_ofCoord_long (n : ℕ) {a b : Fin n} {s t : ℤ} (hab : a ≠ b)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    levTwoS2b_isLong n (levTwoS2b_ofCoord n (Pi.single a s + Pi.single b t)) := by
  simp only [levTwoS2b_isLong, levTwoS2b_longCoord, levTwoS2b_coord_ofCoord]
  exact ⟨a, b, s, t, hab, hs, ht, rfl⟩

theorem levTwoS2b_isRt_ofCoord_sub (n : ℕ) {a b : Fin n} (hab : a ≠ b) :
    IsRt (isFiniteType_cartanB n)
      (levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1)) := by
  simpa only [sub_eq_add_neg, Pi.single_neg] using
    levTwoS2b_isRt_ofCoord_long n hab (Or.inl rfl) (Or.inr rfl)

theorem levTwoS2b_isLong_ofCoord_sub (n : ℕ) {a b : Fin n} (hab : a ≠ b) :
    levTwoS2b_isLong n (levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1)) := by
  simpa only [sub_eq_add_neg, Pi.single_neg] using
    levTwoS2b_isLong_ofCoord_long n hab (Or.inl rfl) (Or.inr rfl)

theorem levTwoS2b_isRt_ofCoord_sub' (n : ℕ) {a b : Fin n} (hab : a ≠ b) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    IsRt (isFiniteType_cartanB n)
      (levTwoS2b_ofCoord n (Pi.single a s - Pi.single b s)) := by
  have ht : (-s : ℤ) = 1 ∨ (-s : ℤ) = -1 := by rcases hs with h | h <;> simp [h]
  have h := levTwoS2b_isRt_ofCoord_long n hab hs ht
  convert h using 2
  rw [sub_eq_add_neg, Pi.single_neg]

theorem levTwoS2b_isLong_ofCoord_sub' (n : ℕ) {a b : Fin n} (hab : a ≠ b) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    levTwoS2b_isLong n (levTwoS2b_ofCoord n (Pi.single a s - Pi.single b s)) := by
  have ht : (-s : ℤ) = 1 ∨ (-s : ℤ) = -1 := by rcases hs with h | h <;> simp [h]
  have h := levTwoS2b_isLong_ofCoord_long n hab hs ht
  convert h using 2
  rw [sub_eq_add_neg, Pi.single_neg]

theorem levTwoS2b_eps_sub_mem (n : ℕ) (p : ℕ) (c : Fin n → ZMod p) {a b : Fin n}
    (hab : a ≠ b) :
    levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1) ∈ levTwoS2b_PhiCase3 n p c ↔
      levTwoS2b_D c a = levTwoS2b_D c b := by
  simp only [levTwoS2b_PhiCase3, Set.mem_setOf_eq]
  constructor
  · intro hv
    have h0 : levTwoS2b_D c a - levTwoS2b_D c b = 0 := by
      rw [← levTwoS2b_lam_eps_sub n p c a b]
      exact hv.2.2
    exact sub_eq_zero.mp h0
  · intro h
    exact ⟨levTwoS2b_isRt_ofCoord_sub n hab, levTwoS2b_isLong_ofCoord_sub n hab,
      by rw [levTwoS2b_lam_eps_sub, h, sub_self]⟩

theorem levTwoS2b_eps_add_mem (n : ℕ) (p : ℕ) (c : Fin n → ZMod p) {a b : Fin n}
    (hab : a ≠ b) :
    levTwoS2b_ofCoord n (Pi.single a 1 + Pi.single b 1) ∈ levTwoS2b_PhiCase3 n p c ↔
      levTwoS2b_D c a = - levTwoS2b_D c b := by
  simp only [levTwoS2b_PhiCase3, Set.mem_setOf_eq]
  constructor
  · intro hv
    have h0 : levTwoS2b_D c a + levTwoS2b_D c b = 0 := by
      rw [← levTwoS2b_lam_eps_add n p c a b]
      exact hv.2.2
    exact (add_eq_zero_iff_eq_neg.mp h0)
  · intro h
    exact ⟨levTwoS2b_isRt_ofCoord_long n hab (Or.inl rfl) (Or.inl rfl),
      levTwoS2b_isLong_ofCoord_long n hab (Or.inl rfl) (Or.inl rfl),
      by rw [levTwoS2b_lam_eps_add, h, neg_add_cancel]⟩

theorem levTwoS2b_allLong_of_D_zero (n : ℕ) (p : ℕ) (c : Fin n → ZMod p)
    (hD : ∀ a : Fin n, levTwoS2b_D c a = 0) :
    levTwoS2b_PhiCase3 n p c = levTwoS2b_allLong n := by
  ext v
  simp only [levTwoS2b_PhiCase3, levTwoS2b_allLong, Set.mem_setOf_eq]
  constructor
  · intro hv
    exact ⟨hv.1, hv.2.1⟩
  · intro hv
    exact ⟨hv.1, hv.2, by rw [levTwoS2b_lam_coord]; simp [hD]⟩

theorem levTwoS2b_coord_apply_long (n : ℕ) {v : Fin n → ℤ} (hl : levTwoS2b_isLong n v)
    (k : Fin n) :
    levTwoS2b_coord n v k = 0 ∨ levTwoS2b_coord n v k = 1 ∨ levTwoS2b_coord n v k = -1 := by
  simp only [levTwoS2b_isLong, levTwoS2b_longCoord] at hl
  obtain ⟨a, b, s, t, hab, hs, ht, hcoord⟩ := hl
  rw [hcoord]
  simp only [Pi.add_apply]
  by_cases hka : k = a
  · have h2 : (Pi.single b t : Fin n → ℤ) a = 0 := by simp [hab]
    rw [hka, Pi.single_eq_same, h2, add_zero]
    rcases hs with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · by_cases hkb : k = b
    · have h1 : (Pi.single a s : Fin n → ℤ) b = 0 := by simp [Ne.symm hab]
      rw [hkb, Pi.single_eq_same, h1, zero_add]
      rcases ht with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · have h1 : (Pi.single a s : Fin n → ℤ) k = 0 := by simp [hka]
      have h2 : (Pi.single b t : Fin n → ℤ) k = 0 := by simp [hkb]
      rw [h1, h2, add_zero]
      exact Or.inl rfl

theorem levTwoS2b_int_eq_zero_of_cast_eq_zero (p : ℕ) (hp : p.Prime) {m : ℤ}
    (hm : m = 0 ∨ m = 1 ∨ m = -1) (h : (m : ZMod p) = 0) : m = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hm with h0 | h1 | h1
  · exact h0
  · rw [h1, Int.cast_one] at h
    exact absurd h one_ne_zero
  · rw [h1, Int.cast_neg, Int.cast_one] at h
    exact absurd (neg_eq_zero.mp h) one_ne_zero

theorem levTwoS2b_case2_of_single_nonzero (n : ℕ) (p : ℕ) (hp : p.Prime) (c : Fin n → ZMod p)
    (k : Fin n) (hk : levTwoS2b_D c k ≠ 0) (hZ : ∀ a : Fin n, a ≠ k → levTwoS2b_D c a = 0) :
    levTwoS2b_PhiCase3 n p c = levTwoS2b_PhiCase2 n k := by
  have : Fact p.Prime := ⟨hp⟩
  ext v
  simp only [levTwoS2b_PhiCase3, levTwoS2b_PhiCase2, Set.mem_setOf_eq]
  have hlam : ∀ w : Fin n → ℤ,
      lam c w = (levTwoS2b_coord n w k : ZMod p) * levTwoS2b_D c k := by
    intro w
    rw [levTwoS2b_lam_coord]
    rw [Finset.sum_eq_single k]
    · intro j _ hj
      rw [hZ j hj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  constructor
  · intro hv
    refine ⟨hv.1, hv.2.1, ?_⟩
    have h0 : (levTwoS2b_coord n v k : ZMod p) * levTwoS2b_D c k = 0 := by
      rw [← hlam v]
      exact hv.2.2
    have hcast : ((levTwoS2b_coord n v k : ℤ) : ZMod p) = 0 :=
      (mul_eq_zero.mp h0).resolve_right hk
    exact levTwoS2b_int_eq_zero_of_cast_eq_zero p hp
      (levTwoS2b_coord_apply_long n hv.2.1 k) hcast
  · intro hv
    refine ⟨hv.1, hv.2.1, ?_⟩
    rw [hlam v, hv.2.2, Int.cast_zero, zero_mul]

theorem levTwoS2b_eta_of_support_all (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (c : Fin n → ZMod p)
    (hne : ∀ a : Fin n, levTwoS2b_D c a ≠ 0)
    (hclass : ∀ a b : Fin n, levTwoS2b_D c a = levTwoS2b_D c b ∨
      levTwoS2b_D c a = - levTwoS2b_D c b) :
    ∃ (a₀ : Fin n) (η : Fin n → ℤ), (∀ a : Fin n, η a = 1 ∨ η a = -1) ∧
      levTwoS2b_D c a₀ ≠ 0 ∧ (∀ a : Fin n, levTwoS2b_D c a = η a * levTwoS2b_D c a₀) := by
  refine ⟨⟨0, hn⟩, fun a => if levTwoS2b_D c a = levTwoS2b_D c ⟨0, hn⟩ then 1 else -1,
    ?_, hne _, ?_⟩
  · intro a
    by_cases h : levTwoS2b_D c a = levTwoS2b_D c ⟨0, hn⟩ <;> simp [h]
  · intro a
    by_cases h : levTwoS2b_D c a = levTwoS2b_D c ⟨0, hn⟩
    · simp [h]
    · have h' : levTwoS2b_D c a = - levTwoS2b_D c ⟨0, hn⟩ := by
        rcases hclass a ⟨0, hn⟩ with hh | hh
        · exact absurd hh h
        · exact hh
      simp [h']

end CFSG.StandardType.LevTwo
