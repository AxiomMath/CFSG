module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
import CFSG.Quasithin.Recognition.Stroth.Str83RqOddComm
import CFSG.Quasithin.Recognition.Stroth.Str83RqOddZ
import CFSG.Quasithin.Recognition.Stroth.Str83RqSzEnd
import CFSG.Quasithin.Recognition.Stroth.Str83Rq411O7
import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRadius
import CFSG.Quasithin.Recognition.Stroth.Str83RqB3
import CFSG.Quasithin.Recognition.Stroth.Str83RqL2End
import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackMove

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem IsMaxArc.odd_isFixRadius_reflect {c : ℤ} (hc : ¬ Even c) {v : ℤ} {b : ℕ}
    (h : t.IsFixRadius v b) : t.IsFixRadius (c + 1 - v) b := by
  refine ⟨?_, ?_⟩
  · have h1 := Subgroup.map_mono (f := (MulAut.conj (t.edgeElt c)).toMonoidHom) h.le_Gw
    rw [t.map_Zv_edgeElt c v, t.map_Gw_edgeElt c (v - b) (v + b), if_neg hc, if_neg hc] at h1
    convert h1 using 2 <;> ring
  · intro hle
    have h1 := Subgroup.map_mono (f := (MulAut.conj (t.edgeElt c)).toMonoidHom) hle
    rw [t.map_Zv_edgeElt c (c + 1 - v), t.map_Gv_edgeElt c (c + 1 - v + b + 1),
      if_neg hc, if_neg hc] at h1
    rw [show c + 1 - (c + 1 - v) = v by ring,
      show c + 1 - (c + 1 - v + b + 1) = v - b - 1 by ring] at h1
    exact IsFixRadius.not_le_Gv_sub t h h1

private theorem IsMaxArc.odd_numbers
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1) {ε : ℤ} {n b₀ b₁ : ℕ}
    (h : t.IsMaxArc ε n) (h₀ : t.IsFixRadius ε b₀) (h₁ : t.IsFixRadius (ε + 1) b₁)
    (hb₀ : Odd b₀) (hb₁ : Odd b₁) (hlt : b₀ < b₁) : n = 2 * b₁ ∧ b₀ + 2 = b₁ := by
  obtain ⟨m, hm⟩ := IsMaxArc.even t hfr h hrq
  obtain rfl : n = 2 * m := by omega
  have h1 := IsMaxArc.fixRadius_add_one t hfr h h₁
  have h2 := IsMaxArc.fixRadius_self t hfr h h₀
  obtain ⟨u, hu⟩ := hb₀
  obtain ⟨v, hv⟩ := hb₁
  omega

private theorem IsMaxArc.odd_normalize {ε : ℤ} {n b₀ b₁ : ℕ} (h : t.IsMaxArc ε n)
    (h₀ : t.IsFixRadius ε b₀) (h₁ : t.IsFixRadius (ε + 1) b₁) :
    (t.IsMaxArc 0 n ∧ t.IsFixRadius 0 b₀ ∧ t.IsFixRadius 1 b₁) ∨
      (t.IsMaxArc (1 - n) n ∧ t.IsFixRadius 1 b₀ ∧ t.IsFixRadius 0 b₁) := by
  rcases Int.even_or_odd ε with he | ho
  · obtain ⟨k, hk⟩ := he
    refine Or.inl ⟨?_, ?_, ?_⟩
    · exact (show ε + 2 * (-k) = 0 by omega) ▸ IsMaxArc.shift t h (-k)
    · exact (show ε + 2 * (-k) = 0 by omega) ▸ IsFixRadius.shift t h₀ (-k)
    · exact (show ε + 1 + 2 * (-k) = 1 by omega) ▸ IsFixRadius.shift t h₁ (-k)
  · have hc : ¬ Even ε := Int.not_even_iff_odd.mpr ho
    obtain ⟨k, hk⟩ := ho
    refine Or.inr ⟨?_, ?_, ?_⟩
    · exact (show 2 * (k + 1) - ε - n = 1 - n by omega) ▸ IsMaxArc.reflect t h (k + 1)
    · exact (show ε + 1 - ε = 1 by ring) ▸ IsMaxArc.odd_isFixRadius_reflect t hc h₀
    · exact (show ε + 1 - (ε + 1) = 0 by ring) ▸ IsMaxArc.odd_isFixRadius_reflect t hc h₁

private theorem IsMaxArc.odd_sz_data {n b₀ b₁ : ℕ} (hγ : t.IsMaxArc 0 n)
    (r0 : t.IsFixRadius 0 b₀) (r1 : t.IsFixRadius 1 b₁) (hn : n = 2 * b₁) (hb : b₀ + 2 = b₁)
    (hb₁ : Odd b₁) :
    t.IsMaxArc (1 - b₁) n ∧ t.Zv 1 ≤ t.Gw (1 - b₁) (1 - b₁ + n) ∧
      t.Zv 1 ≤ t.Gw (2 - (b₁ + 1)) (b₁ + 1) ∧ ¬ t.Zv 1 ≤ t.Gv (b₁ + 1 + 1) ∧
      t.Zv (b₁ + 1) ≤ t.Gw 3 4 := by
  obtain ⟨k, hk⟩ := hb₁
  have hb3 : 3 ≤ b₁ := by omega
  have hγ' : t.IsMaxArc (1 - b₁) n :=
    (show (0 : ℤ) + 2 * (-k) = 1 - b₁ by omega) ▸ IsMaxArc.shift t hγ (-k)
  have r0' : t.IsFixRadius ((b₁ : ℤ) + 1) b₀ :=
    (show (0 : ℤ) + 2 * (k + 1) = (b₁ : ℤ) + 1 by omega) ▸ IsFixRadius.shift t r0 (k + 1)
  have hZ1 : t.Zv 1 ≤ t.Gw (1 - b₁) (1 - b₁ + n) :=
    (show (1 : ℤ) - b₁ + n = 1 + b₁ by omega).symm ▸ r1.le_Gw
  have hZ1' : t.Zv 1 ≤ t.Gw (2 - (b₁ + 1)) (b₁ + 1) := by
    have h := r1.le_Gw
    rw [show t.Gw (1 - (b₁ : ℤ)) (1 + (b₁ : ℤ)) =
      t.Gw (2 - ((b₁ : ℤ) + 1)) ((b₁ : ℤ) + 1) by congr 1 <;> ring] at h
    exact h
  have hZ1'' : ¬ t.Zv 1 ≤ t.Gv (b₁ + 1 + 1) :=
    (show (1 : ℤ) + b₁ + 1 = b₁ + 1 + 1 by ring) ▸ r1.not_le_Gv
  have hZh : t.Zv (b₁ + 1) ≤ t.Gw 3 4 := by
    have h' : t.Zv ((b₁ : ℤ) + 1) ≤ t.Gw 3 (2 * (b₁ : ℤ) - 1) :=
      (show ((b₁ : ℤ) + 1) - b₀ = 3 by omega) ▸
        (show ((b₁ : ℤ) + 1) + b₀ = 2 * (b₁ : ℤ) - 1 by omega) ▸ r0'.le_Gw
    exact h'.trans (win_mono (by norm_num) (by omega))
  exact ⟨hγ', hZ1, hZ1', hZ1'', hZh⟩

private theorem IsMaxArc.odd_l2_data {n b₀ b₁ : ℕ} (hγ : t.IsMaxArc (1 - n) n)
    (r1 : t.IsFixRadius 1 b₀) (r0 : t.IsFixRadius 0 b₁) (hn : n = 2 * b₁) (hb : b₀ + 2 = b₁)
    (hb₁ : Odd b₁) :
    t.IsMaxArc (-(b₁ : ℤ)) n ∧ t.Zv 0 ≤ t.Gw (-(b₁ : ℤ)) (-(b₁ : ℤ) + n) ∧
      t.Zv 0 ≤ t.Gw (-(b₁ : ℤ)) b₁ ∧ (∀ u : ℤ, pCoreOf 2 (t.Gw u (u + 2 * b₁ + 1)) = ⊥) ∧
      ¬ t.Zv 1 ≤ t.Gv (-(b₀ : ℤ)) ∧ t.Zv (-(b₁ : ℤ)) ≤ t.Gv (-2) := by
  obtain ⟨k, hk⟩ := hb₁
  have hb3 : 3 ≤ b₁ := by omega
  have hγ' : t.IsMaxArc (-(b₁ : ℤ)) n :=
    (show (1 : ℤ) - n + 2 * k = -(b₁ : ℤ) by omega) ▸ IsMaxArc.shift t hγ k
  have hZ0 : t.Zv 0 ≤ t.Gw (-(b₁ : ℤ)) (-(b₁ : ℤ) + n) :=
    (show -(b₁ : ℤ) + n = b₁ by omega).symm ▸ by
      simpa only [zero_sub, zero_add] using r0.le_Gw
  have hZ0' : t.Zv 0 ≤ t.Gw (-(b₁ : ℤ)) b₁ := by
    simpa only [zero_sub, zero_add] using r0.le_Gw
  have hmax : ∀ u : ℤ, pCoreOf 2 (t.Gw u (u + 2 * b₁ + 1)) = ⊥ := by
    intro u
    refine hγ.pCoreOf_eq_bot u (u + 2 * (b₁ : ℤ) + 1) ?_
    omega
  have hZ1 : ¬ t.Zv 1 ≤ t.Gv (-(b₀ : ℤ)) :=
    (show (1 : ℤ) - b₀ - 1 = -(b₀ : ℤ) by ring) ▸ IsFixRadius.not_le_Gv_sub t r1
  have hZb : t.Zv (-(b₁ : ℤ)) ≤ t.Gv (-2) := by
    have r1' : t.IsFixRadius (-(b₁ : ℤ)) b₀ :=
      (show (1 : ℤ) + 2 * (-(k : ℤ) - 1) = -(b₁ : ℤ) by omega) ▸
        IsFixRadius.shift t r1 (-(k : ℤ) - 1)
    have h' : t.Zv (-(b₁ : ℤ)) ≤ t.Gw (-2 * (b₁ : ℤ) + 2) (-2) :=
      (show -(b₁ : ℤ) - b₀ = -2 * (b₁ : ℤ) + 2 by omega) ▸
        (show -(b₁ : ℤ) + b₀ = -2 by omega) ▸ r1'.le_Gw
    exact h'.trans (win_le_qv (a := -2 * (b₁ : ℤ) + 2) (b := -2) (i := -2) (by omega) le_rfl)
  exact ⟨hγ', hZ0, hZ0', hmax, hZ1, hZb⟩

private theorem IsMaxArc.odd_card_Zv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {u : ℤ} {n : ℕ} (hγ : t.IsMaxArc u n) {v : ℤ}
    (hZ : t.Zv v ≤ t.Gw u (u + n)) :
    Nat.card (t.Zv v) = if Even u then 2 ^ (2 * a + 1) else 2 ^ f := by
  rw [IsMaxArc.Zv_eq_omegaOneCenterOf t hfr hγ hZ]
  exact IsMaxArc.card_omegaOneCenterOf t hfr hγ (Or.inl rfl)

private theorem IsMaxArc.odd_eq_Zv_of_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {u : ℤ} {n : ℕ} (hγ : t.IsMaxArc u n) {v : ℤ}
    (hZ : t.Zv v ≤ t.Gw u (u + n)) :
    ∀ X : Subgroup G, X ≤ t.Zv v → X ≠ ⊥ → t.K ≤ normalizer (X : Set G) → X = t.Zv v := by
  have hZeq := IsMaxArc.Zv_eq_omegaOneCenterOf t hfr hγ hZ
  intro X hX hXne hXK
  have hXQ : X ≤ pCoreOf 2 (t.Gw u (u + n)) :=
    hX.trans (hZeq.le.trans (A4.omegaOneCenterOf_le _))
  exact le_antisymm hX (hZeq.le.trans (IsMaxArc.omegaOneCenterOf_le t hfr hγ hXQ hXne hXK))

private theorem IsMaxArc.odd_false_of_sz
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1)
    {n b₀ b₁ : ℕ} (hγ : t.IsMaxArc 0 n) (r0 : t.IsFixRadius 0 b₀) (r1 : t.IsFixRadius 1 b₁)
    (hn : n = 2 * b₁) (hb : b₀ + 2 = b₁) (hb₁ : Odd b₁) : False := by
  obtain ⟨hγ', hZγ, hZ1, hZ1', hZh⟩ := IsMaxArc.odd_sz_data t hγ r0 r1 hn hb hb₁
  obtain ⟨k, hk⟩ := hb₁
  have hev : Even (1 - (b₁ : ℤ)) := ⟨-(k : ℤ), by omega⟩
  have hcard := IsMaxArc.odd_card_Zv t hfr hγ' hZγ
  rw [if_pos hev] at hcard
  have hZL := L2_le_centralizer_Zv_one_of_minimal t hfr (IsMaxArc.odd_eq_Zv_of_le t hfr hγ' hZγ)
  have hev' : Even ((b₁ : ℤ) + 1) := ⟨(k : ℤ) + 1, by omega⟩
  exact hrq (eq_two_mul_add_one_of_sz t hfr (h := (b₁ : ℤ) + 1) (by omega) hev' hZ1 hZ1' hZh
    hZL hcard.le)

private theorem IsMaxArc.odd_false_of_l2
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {n b₀ b₁ : ℕ}
    (hγ : t.IsMaxArc (1 - n) n) (r1 : t.IsFixRadius 1 b₀) (r0 : t.IsFixRadius 0 b₁)
    (hn : n = 2 * b₁) (hb : b₀ + 2 = b₁) (hb₁ : Odd b₁) : False := by
  obtain ⟨hγ', hZγ, hZ0, hmax, hZ1, hZb⟩ := IsMaxArc.odd_l2_data t hγ r1 r0 hn hb hb₁
  have hodd : ¬ Even (-(b₁ : ℤ)) := by
    rw [Int.not_even_iff_odd]
    obtain ⟨k, hk⟩ := hb₁
    exact ⟨-(k : ℤ) - 1, by omega⟩
  have hcard := IsMaxArc.odd_card_Zv t hfr hγ' hZγ
  rw [if_neg hodd] at hcard
  have hZL := L1_le_centralizer_Zv_zero_of_minimal t hfr (IsMaxArc.odd_eq_Zv_of_le t hfr hγ' hZγ)
  rcases (show b₁ = 3 ∨ 5 ≤ b₁ by obtain ⟨k, hk⟩ := hb₁; omega) with h3 | h5
  · subst b₁
    have h0 : b₀ = 1 := by omega
    subst b₀
    have hZ0' : t.Zv 0 ≤ t.Gw (-3) 3 := by simpa using hZ0
    have hZ1' : ¬ t.Zv 1 ≤ t.Gv (-1) := by simpa using hZ1
    have hmax' : ∀ u : ℤ, pCoreOf 2 (t.Gw u (u + 7)) = ⊥ := by
      intro u
      have h := hmax u
      ring_nf at h ⊢
      exact h
    exact false_of_b_eq_three t hfr hZ0' hZ1' hmax' hZL hcard.ge
  · have hC0 : t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥ := by
      refine Zv_one_inf_centralizer_eq_bot_of_Lv_zero t hfr ?_
      rw [t.Lv_zero]
      refine sup_le hZL ?_
      rw [← t.Qv_zero]
      exact Subgroup.le_centralizer_iff.mpr (t.Zv_le_centralizer 0)
    have hR2 := commutator_Zv_zero_Zv_neg_le_Qv_neg_two t hfr (b := (b₁ : ℤ)) (by omega) hZ0 hZb
    have hR := commutator_commutator_Zv_zero_Zv_neg_eq_bot t hfr (b := (b₁ : ℤ)) (by omega)
      hZ0 hR2 hZL hC0
    exact false_of_five_le_b t hfr (b := (b₁ : ℤ)) (by omega) ((Int.odd_coe_nat b₁).mpr hb₁)
      hZ0 hmax hZL hcard.ge hR

theorem IsMaxArc.commutator_le_inf_of_odd
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1)
    {ε : ℤ} {n b₀ b₁ : ℕ} (h : t.IsMaxArc ε n) (h₀ : t.IsFixRadius ε b₀)
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₀ : Odd b₀) :
    ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁) := by
  by_cases ha : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁)
  · exact ha
  exfalso
  obtain ⟨-, hb₁, hlt⟩ := (IsFixRadius.commutator_le_inf_or t h₀ h₁).resolve_left ha
  obtain ⟨hn, hb⟩ := IsMaxArc.odd_numbers t hfr hrq h h₀ h₁ hb₀ hb₁ hlt
  rcases IsMaxArc.odd_normalize t h h₀ h₁ with ⟨hγ, r0, r1⟩ | ⟨hγ, r1, r0⟩
  · exact IsMaxArc.odd_false_of_sz t hfr hrq hγ r0 r1 hn hb hb₁
  · exact IsMaxArc.odd_false_of_l2 t hfr hγ r1 r0 hn hb hb₁

end Track

end CFSG.Quasithin.Stroth.Rq
