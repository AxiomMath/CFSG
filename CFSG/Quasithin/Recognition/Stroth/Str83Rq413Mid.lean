module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackModule

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Walter.Bender1970.S2.Basic
public import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRoot

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem IsMaxArc.eq_one_of_commutator_inf_ne_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₁ : ℕ} (h : t.IsMaxArc ε (2 * (b₁ + 1)))
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₁ : Odd b₁)
    (hX : ⁅t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1), t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)⁆ ≠ ⊥) :
    b₁ = 1 := by
  by_contra hne
  obtain ⟨m, hm⟩ := hb₁
  have hb1pos : 1 ≤ b₁ := IsFixRadius.one_le t hfr h₁
  have hb2 : 2 ≤ b₁ := by omega
  have hb1Z : (b₁ : ℤ) = 2 * (m : ℤ) + 1 := by rw [hm]; push_cast; ring
  have hZ1 : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) ≤ t.Zv (ε + 1) := inf_le_left
  have hQ1 : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) ≤ t.Qv (ε + 1 + b₁) := inf_le_right
  have hYG : t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1) ≤ t.Gv (ε + 1) := inf_le_right
  have hYZ : t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1) ≤ t.Zv (ε + 2 + b₁) := inf_le_left
  have hXZ : ⁅t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1), t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)⁆
      ≤ t.Zv (ε + 1) :=
    (Subgroup.commutator_mono_right
      (H := t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1)) hZ1).trans
      ((Subgroup.le_normalizer_iff_commutator_le_right
        (H := t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1)) (K := t.Zv (ε + 1))).mp
        (hYG.trans (t.Gv_le_normalizer_Zv (ε + 1))))
  have hXZ2 : ⁅t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1), t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)⁆
      ≤ t.Zv (ε + 2 + b₁) := by
    have hnorm : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) ≤
        normalizer (t.Zv (ε + 2 + b₁) : Set G) := by
      have hQG : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) ≤
          t.Gv ((ε + 1 + (b₁ : ℤ)) + 1) :=
        hQ1.trans (t.Qv_le_Gv hfr (ε + 1 + b₁)).2
      have hQG' : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) ≤ t.Gv (ε + 2 + (b₁ : ℤ)) := by
        rwa [show (ε + 1 + (b₁ : ℤ)) + 1 = ε + 2 + (b₁ : ℤ) by ring] at hQG
      exact hQG'.trans (t.Gv_le_normalizer_Zv (ε + 2 + b₁))
    calc ⁅t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1), t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)⁆
        = ⁅t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁), t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1)⁆ :=
          Subgroup.commutator_comm _ _
      _ ≤ ⁅t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁), t.Zv (ε + 2 + b₁)⁆ :=
          Subgroup.commutator_mono_right
            (H := t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)) hYZ
      _ ≤ t.Zv (ε + 2 + b₁) :=
          (Subgroup.le_normalizer_iff_commutator_le_right
            (H := t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)) (K := t.Zv (ε + 2 + b₁))).mp hnorm
  have hz2 : t.IsFixRadius (ε + 2 + (b₁ : ℤ)) b₁ := by
    have hsh := IsFixRadius.shift t h₁ ((m : ℤ) + 1)
    have heq : (ε + 1) + 2 * ((m : ℤ) + 1) = ε + 2 + (b₁ : ℤ) := by rw [hb1Z]; ring
    rwa [heq] at hsh
  have hZ2Gw : t.Zv (ε + 2 + (b₁ : ℤ)) ≤ t.Gw (ε + 2) (ε + 2 + 2 * (b₁ : ℤ)) := by
    have hle := hz2.le_Gw
    rwa [show (ε + 2 + (b₁ : ℤ)) - (b₁ : ℤ) = ε + 2 by ring,
      show (ε + 2 + (b₁ : ℤ)) + (b₁ : ℤ) = ε + 2 + 2 * (b₁ : ℤ) by ring] at hle
  have hXGw : ⁅t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1), t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)⁆
      ≤ t.Gw (ε + 1 - (b₁ : ℤ)) (ε + 2 + 2 * (b₁ : ℤ)) := by
    intro x hx
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i ≤ ε + 1 + (b₁ : ℤ) ∨ ε + 2 ≤ i by omega) with hle | hle
    · exact mem_win_iff.mp (h₁.le_Gw (hXZ hx)) i h1 hle
    · exact mem_win_iff.mp (hZ2Gw (hXZ2 hx)) i hle h2
  have hXp : IsPGroup 2 (⁅t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1),
      t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)⁆ : Subgroup G) :=
    (t.isPGroup_Zv (ε + 1)).to_le hXZ
  have hXpc : ⁅t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1),
      t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)⁆
      ≤ pCoreOf 2 (t.Gw (ε + 1 - (b₁ : ℤ)) (ε + 2 + 2 * (b₁ : ℤ))) :=
    t.le_pCoreOf_Gw hfr (by omega) hXp hXGw
  have hbot := h.pCoreOf_eq_bot (ε + 1 - (b₁ : ℤ)) (ε + 2 + 2 * (b₁ : ℤ))
    (by push_cast; omega)
  exact hX (le_bot_iff.mp (hXpc.trans_eq hbot))

theorem IsMaxArc.false_of_inf_Qv_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₁ : ℕ} (h : t.IsMaxArc ε (2 * (b₁ + 1)))
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₁ : Odd b₁) (hε : Even ε) (hf : f = 2 * (2 * a + 1))
    (hZ : t.Zv ε ≤ t.Zv (ε + 1))
    (hH : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) ≤ t.Qv (ε + 2 + b₁)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd_b₁Z : Odd (b₁ : ℤ) := (Int.odd_coe_nat b₁).mpr hb₁
  obtain ⟨m, hm⟩ := hb₁
  have hb1pos : 1 ≤ b₁ := IsFixRadius.one_le t hfr h₁
  have hb1Z : (b₁ : ℤ) = 2 * (m : ℤ) + 1 := by rw [hm]; push_cast; ring
  have hoddε1 : Odd (ε + 1) := hε.add_one
  have heven_e : Even (ε + 1 - (b₁ : ℤ)) :=
    (Int.even_sub' (m := ε + 1) (n := (b₁ : ℤ))).mpr (iff_of_true hoddε1 hodd_b₁Z)
  have heven_w : Even (ε + 1 + (b₁ : ℤ)) :=
    (Int.even_add' (m := ε + 1) (n := (b₁ : ℤ))).mpr (iff_of_true hoddε1 hodd_b₁Z)
  have hnot_evenε1 : ¬ Even (ε + 1) := Int.not_even_iff_odd.mpr hoddε1
  have h' : t.IsMaxArc (ε + 1 - (b₁ : ℤ)) (2 * (b₁ + 1)) := by
    have hsh := IsMaxArc.shift t h (-(m : ℤ))
    have heq : ε + 2 * (-(m : ℤ)) = ε + 1 - (b₁ : ℤ) := by rw [hb1Z]; ring
    rwa [heq] at hsh
  have hHZ : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) ≤ t.Zv (ε + 1) := inf_le_left
  have hHQ : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) ≤ t.Qv (ε + 1 + b₁) := inf_le_right
  have hH_Gw : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)
      ≤ t.Gw (ε + 1 - (b₁ : ℤ)) (ε + 3 + (b₁ : ℤ)) := by
    intro x hx
    refine mem_win_iff.mpr fun i h1 h2 => ?_
    rcases (show i ≤ ε + 1 + (b₁ : ℤ) ∨ i = ε + 2 + (b₁ : ℤ) ∨ i = ε + 3 + (b₁ : ℤ)
      by omega) with hle | heq | heq
    · exact mem_win_iff.mp (h₁.le_Gw (hHZ hx)) i h1 hle
    · rw [heq]
      have h : x ∈ t.Gv ((ε + 1 + (b₁ : ℤ)) + 1) :=
        (t.Qv_le_Gv hfr (ε + 1 + b₁)).2 (hHQ hx)
      rwa [show (ε + 1 + (b₁ : ℤ)) + 1 = ε + 2 + (b₁ : ℤ) by ring] at h
    · rw [heq]
      have h : x ∈ t.Gv ((ε + 2 + (b₁ : ℤ)) + 1) :=
        (t.Qv_le_Gv hfr (ε + 2 + b₁)).2 (hH hx)
      rwa [show (ε + 2 + (b₁ : ℤ)) + 1 = ε + 3 + (b₁ : ℤ) by ring] at h
  have hHpc : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)
      ≤ pCoreOf 2 (t.Gw (ε + 1 - (b₁ : ℤ)) (ε + 3 + (b₁ : ℤ))) :=
    t.le_pCoreOf_Gw hfr (by omega) ((t.isPGroup_Zv (ε + 1)).to_le hHZ) hH_Gw
  have hHpc' : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)
      ≤ pCoreOf 2 (t.Gw (ε + 1 - (b₁ : ℤ))
        ((ε + 1 - (b₁ : ℤ)) + ↑(2 * (b₁ + 1)))) := by
    have heq : (ε + 1 - (b₁ : ℤ)) + ↑(2 * (b₁ + 1)) = ε + 3 + (b₁ : ℤ) := by
      push_cast; ring
    rwa [heq]
  have hbot : pCoreOf 2 (t.Gw (ε + 1 - (b₁ : ℤ))
        ((ε + 1 - (b₁ : ℤ)) + ↑(2 * (b₁ + 1))))
      ⊓ t.Qv (ε + 1 - (b₁ : ℤ)) = ⊥ :=
    (IsMaxArc.inf_Qv_eq_bot t hfr h').1
  have hHinfQ : (t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)) ⊓ t.Qv (ε + 1 - (b₁ : ℤ)) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf hHpc' le_rfl).trans (le_of_eq hbot))
  have hHsq : ∀ x ∈ t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁), x ^ 2 = 1 := by
    intro x hx
    exact A4.sq_eq_one_of_mem_omegaOneCenterOf ((t.Zv_eq (ε + 1)) ▸ hHZ hx)
  have hA : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)
      ≤ pCoreOf 2 (t.Gw (ε + 1 - (b₁ : ℤ)) ((ε + 1 - (b₁ : ℤ)) + 1)) := by
    have hle : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)
        ≤ t.Gw (ε + 1 - (b₁ : ℤ)) ((ε + 1 - (b₁ : ℤ)) + 1) := by
      refine hH_Gw.trans (win_mono le_rfl ?_)
      push_cast; omega
    exact t.le_pCoreOf_Gw hfr (by omega) ((t.isPGroup_Zv (ε + 1)).to_le hHZ) hle
  have hHcard_le : Nat.card (t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) : Subgroup G) ≤ 2 ^ (2 * a + 1) := by
    have hrel_le := t.relIndex_Qv_le_of_sq_mem hfr (ε + 1 - (b₁ : ℤ)) hA
      (fun x hx => by rw [hHsq x hx]; exact (t.Qv (ε + 1 - (b₁ : ℤ))).one_mem)
    rw [if_pos heven_e] at hrel_le
    have hcard_eq : Nat.card (t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) : Subgroup G) =
        (t.Qv (ε + 1 - (b₁ : ℤ))).relIndex (t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)) := by
      have h := Subgroup.inf_relIndex_left (t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁))
        (t.Qv (ε + 1 - (b₁ : ℤ)))
      rw [hHinfQ, Subgroup.relIndex_bot_left] at h
      exact h
    rwa [hcard_eq]
  have hA2 : t.Zv (ε + 1) ≤
      pCoreOf 2 (t.Gw ((ε + 1 + b₁) - 1) (ε + 1 + b₁)) := by
    refine t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv _) ?_
    refine h₁.le_Gw.trans (win_mono ?_ le_rfl)
    push_cast; omega
  have hsqA2 : ∀ x ∈ t.Zv (ε + 1), x ^ 2 ∈ t.Qv (ε + 1 + b₁) := by
    intro x hx
    rw [A4.sq_eq_one_of_mem_omegaOneCenterOf ((t.Zv_eq (ε + 1)) ▸ hx)]
    exact (t.Qv (ε + 1 + b₁)).one_mem
  have hrel_le2 := t.relIndex_Qv_le_of_sq_mem_left hfr (ε + 1 + b₁) hA2 hsqA2
  rw [if_pos heven_w] at hrel_le2
  have hHrelZ : (t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)).relIndex (t.Zv (ε + 1))
      ≤ 2 ^ (2 * a + 1) := by
    have h := Subgroup.inf_relIndex_left (t.Zv (ε + 1)) (t.Qv (ε + 1 + b₁))
    rw [h]
    exact hrel_le2
  have hcardA : Nat.card (t.Zv (ε + 1)) ≤ (2 ^ (2 * a + 1)) ^ 2 := by
    have h := Subgroup.relIndex_mul_card (H := t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁))
      (K := t.Zv (ε + 1))
    rw [inf_eq_left.mpr hHZ] at h
    calc Nat.card (t.Zv (ε + 1))
        = (t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)).relIndex (t.Zv (ε + 1))
            * Nat.card (t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) : Subgroup G) := h.symm
      _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := Nat.mul_le_mul hHrelZ hHcard_le
      _ = (2 ^ (2 * a + 1)) ^ 2 := (pow_two _).symm
  have hpow : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_pow (by omega) (by norm_num)
  have hf2 : 2 ^ f = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [hf, show 2 * (2 * a + 1) = (2 * a + 1) * 2 by ring, pow_mul]
  have hlt : (2 ^ (2 * a + 1)) ^ 2 < (2 ^ f) ^ 2 := by
    rw [hf2]
    rw [show ((2 ^ (2 * a + 1)) ^ 2) ^ 2 = (2 ^ (2 * a + 1)) ^ 4 by ring]
    exact Nat.pow_lt_pow_right hpow (by norm_num)
  have hcard_lt : Nat.card (t.Zv (ε + 1)) < (2 ^ f) ^ 2 := lt_of_le_of_lt hcardA hlt
  have hCle : t.Lv (ε + 1) ≤ centralizer (t.Zv (ε + 1) : Set G) := by
    by_contra hC
    have hle := t.le_card_Zv_of_not_le_centralizer hfr (ε + 1) hC
    rw [if_neg hnot_evenε1] at hle
    exact absurd hle (not_le.mpr hcard_lt)
  exact false_of_Zv_le_of_le_centralizer t hfr (u := ε) (v := ε + 1) (Or.inr rfl) hZ hCle

theorem IsFixRadius.false_of_commutator_inf_eq_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₁ : ℕ}
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₁ : Odd b₁) (hε : Even ε) (hf : f = 2 * (2 * a + 1))
    (hZ : t.Zv ε ≤ t.Zv (ε + 1))
    (hH : ¬ t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) ≤ t.Qv (ε + 2 + b₁))
    (hX : ⁅t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1), t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)⁆ = ⊥) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)
  let W : Subgroup G := t.Zv (ε + 2 + b₁)
  obtain ⟨m, hm⟩ := hb₁
  have hb1pos : 1 ≤ b₁ := by omega
  have hHwin : H ≤ t.Gw ((ε + 2 + b₁) - 1) (ε + 2 + b₁) := by
    have hle : H ≤ t.Qv (ε + 1 + b₁) := by
      dsimp only [H]
      exact inf_le_right
    have hGv1 : t.Qv (ε + 1 + b₁) ≤ t.Gv ((ε + 2 + b₁) - 1) := by
      rw [show (ε + 2 + b₁) - 1 = ε + 1 + b₁ by ring]
      exact t.Qv_le_Gv_self _
    have hGv2 : t.Qv (ε + 1 + b₁) ≤ t.Gv (ε + 2 + b₁) := by
      have h := (t.Qv_le_Gv hfr (ε + 1 + b₁)).2
      rwa [show ε + 1 + b₁ + 1 = ε + 2 + b₁ by ring] at h
    have hgw : t.Gw ((ε + 2 + b₁) - 1) (ε + 2 + b₁) =
        t.Gv ((ε + 2 + b₁) - 1) ⊓ t.Gv (ε + 2 + b₁) := by
      have h := t.Gw_add_one ((ε + 2 + b₁) - 1)
      rwa [show ((ε + 2 + b₁) - 1) + 1 = ε + 2 + b₁ by ring] at h
    rw [hgw]
    exact le_inf (hle.trans hGv1) (hle.trans hGv2)
  have hH2 : H ≤ t.Zv (ε + 1) := by
    dsimp only [H]
    exact inf_le_left
  have hHpc : H ≤ pCoreOf 2 (t.Gw ((ε + 2 + b₁) - 1) (ε + 2 + b₁)) :=
    t.le_pCoreOf_Gw hfr (by omega) ((t.isPGroup_Zv (ε + 1)).to_le hH2) hHwin
  have hHK : t.K ≤ normalizer (H : Set G) :=
    (le_inf (t.K_le_normalizer_Zv (ε + 1)) (t.K_le_normalizer_Qv (ε + 1 + b₁))).trans
      (inf_normalizer_le_normalizer_inf (H := t.Zv (ε + 1))
        (K := t.Qv (ε + 1 + b₁)))
  have hshift : t.IsFixRadius (ε + 2 + b₁) b₁ := by
    have h := IsFixRadius.shift t h₁ ((m : ℤ) + 1)
    have harg : ε + 1 + 2 * ((m : ℤ) + 1) = ε + 2 + b₁ := by
      rw [hm]
      push_cast
      ring
    rwa [harg] at h
  have hW_Gw : W ≤ t.Gw (ε + 2) (ε + 2 + 2 * b₁) := by
    have h := hshift.le_Gw
    rw [show (ε + 2 + b₁) - (b₁ : ℤ) = ε + 2 by omega,
        show (ε + 2 + b₁) + (b₁ : ℤ) = ε + 2 + 2 * b₁ by omega] at h
    exact h
  have hW_le23 : W ≤ t.Gw (ε + 2) ((ε + 2) + 1) :=
    hW_Gw.trans (win_mono (le_refl _) (by omega))
  have hW_pc : W ≤ pCoreOf 2 (t.Gw (ε + 2) ((ε + 2) + 1)) :=
    t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv (ε + 2 + b₁)) hW_le23
  have hsq : ∀ x ∈ W, x ^ 2 ∈ t.Qv (ε + 2) := by
    intro x hx
    have hx2 : x ^ 2 = 1 := by
      have hx' : x ∈ t.Zv (ε + 2 + b₁) := hx
      rw [t.Zv_eq (ε + 2 + b₁)] at hx'
      exact A4.sq_eq_one_of_mem_omegaOneCenterOf hx'
    rw [hx2]
    exact one_mem _
  have hε2 : Even (ε + 2) := Even.add hε even_two
  have hrelQv : (t.Qv (ε + 2)).relIndex W ≤ 2 ^ (2 * a + 1) := by
    have h := t.relIndex_Qv_le_of_sq_mem (A := W) hfr (ε + 2) hW_pc hsq
    rwa [if_pos hε2] at h
  have hQvGv : t.Qv (ε + 2) ≤ t.Gv (ε + 1) := by
    have h := (t.Qv_le_Gv hfr (ε + 2)).1
    rwa [show ε + 2 - 1 = ε + 1 by ring] at h
  have hXcent : W ⊓ t.Gv (ε + 1) ≤ centralizer (H : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hX
  have hHbound : (W ⊓ centralizer (H : Set G)).relIndex W ≤ 2 ^ (2 * a + 1) := by
    have hWGv : W ⊓ t.Qv (ε + 2) ≤ W ⊓ t.Gv (ε + 1) :=
      le_inf inf_le_left (inf_le_right.trans hQvGv)
    have hcent : W ⊓ t.Qv (ε + 2) ≤ centralizer (H : Set G) :=
      hWGv.trans hXcent
    have hle : W ⊓ t.Qv (ε + 2) ≤ W ⊓ centralizer (H : Set G) :=
      le_inf inf_le_left hcent
    have hne : (W ⊓ t.Qv (ε + 2)).relIndex W ≠ 0 := by
      haveI : Nonempty W := ⟨⟨1, W.one_mem⟩⟩
      haveI : Finite W := inferInstance
      have hpos : 0 < Nat.card W := Nat.card_pos
      intro h
      exact (Nat.ne_of_gt hpos)
        (eq_zero_of_zero_dvd (h ▸ Subgroup.relIndex_dvd_card
          (H := W ⊓ t.Qv (ε + 2)) (K := W)))
    have h1 : (W ⊓ centralizer (H : Set G)).relIndex W ≤
        (W ⊓ t.Qv (ε + 2)).relIndex W :=
      Subgroup.relIndex_le_of_le_left hle hne
    have h2 : (W ⊓ t.Qv (ε + 2)).relIndex W = (t.Qv (ε + 2)).relIndex W := by
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right (H := t.Qv (ε + 2)) (K := W)
    rw [h2] at h1
    exact h1.trans hrelQv
  obtain ⟨y, _, hyK, hGw, hQv, hZv⟩ := t.exists_reflection (ε + 2 + b₁)
  let e : G ≃* G := MulAut.conj y
  let X' : Subgroup G := H.map e.toMonoidHom
  have hWfix : W.map e.toMonoidHom = W := by
    have h := hZv (ε + 2 + b₁)
    rwa [show 2 * (ε + 2 + b₁) - (ε + 2 + b₁) = ε + 2 + b₁ by ring] at h
  have hQfix : (t.Qv (ε + 2 + b₁)).map e.toMonoidHom = t.Qv (ε + 2 + b₁) := by
    have h := hQv (ε + 2 + b₁)
    rwa [show 2 * (ε + 2 + b₁) - (ε + 2 + b₁) = ε + 2 + b₁ by ring] at h
  have hmapGw : (t.Gw ((ε + 2 + b₁) - 1) (ε + 2 + b₁)).map e.toMonoidHom =
      t.Gw (ε + 2 + b₁) ((ε + 2 + b₁) + 1) := by
    have h := hGw ((ε + 2 + b₁) - 1) (ε + 2 + b₁)
    rw [show 2 * (ε + 2 + b₁) - (ε + 2 + b₁) = ε + 2 + b₁ by ring,
        show 2 * (ε + 2 + b₁) - ((ε + 2 + b₁) - 1) = (ε + 2 + b₁) + 1 by ring] at h
    exact h
  have hX'pc : X' ≤ pCoreOf 2 (t.Gw (ε + 2 + b₁) ((ε + 2 + b₁) + 1)) := by
    have hmono := Subgroup.map_mono (f := e.toMonoidHom) hHpc
    rw [← pCoreOf_map_mulEquiv 2 e (t.Gw ((ε + 2 + b₁) - 1) (ε + 2 + b₁)),
        hmapGw] at hmono
    exact hmono
  have hKmap : t.K.map e.toMonoidHom = t.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyK
  have hX'K : t.K ≤ normalizer (X' : Set G) := by
    have hmono := Subgroup.map_mono (f := e.toMonoidHom) hHK
    rw [hKmap, Subgroup.map_equiv_normalizer_eq] at hmono
    exact hmono
  have hX'Q : ¬ X' ≤ t.Qv (ε + 2 + b₁) := by
    intro hle
    apply hH
    have hle' : H.map e.toMonoidHom ≤ (t.Qv (ε + 2 + b₁)).map e.toMonoidHom := by
      rwa [hQfix]
    exact (Subgroup.map_le_map_iff_of_injective e.injective).mp hle'
  let A : Subgroup G := W ⊓ centralizer (H : Set G)
  have hAeq : A.map e.toMonoidHom = W ⊓ centralizer (X' : Set G) := by
    change (W ⊓ centralizer (H : Set G)).map e.toMonoidHom =
      W ⊓ centralizer (H.map e.toMonoidHom)
    rw [Subgroup.map_inf_eq W (centralizer (H : Set G)) e.toMonoidHom e.injective,
        hWfix, CFSG.Walter.map_centralizer_mulEquiv e (H : Set G), Subgroup.coe_map]
    rfl
  have hrelX' : (W ⊓ centralizer (X' : Set G)).relIndex W = A.relIndex W := by
    rw [← hAeq]
    have h := Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom)
      (W ⊓ centralizer (H : Set G)) W e.injective
    rw [hWfix] at h
    exact h
  have hX'bound : (W ⊓ centralizer (X' : Set G)).relIndex W ≤ 2 ^ (2 * a + 1) := by
    rw [hrelX']
    exact hHbound
  have hbase : (W ⊓ centralizer (X' : Set G)).relIndex W *
        (W ⊓ centralizer (H : Set G)).relIndex W ≤ (2 ^ (2 * a + 1)) ^ 2 := by
    calc (W ⊓ centralizer (X' : Set G)).relIndex W *
          (W ⊓ centralizer (H : Set G)).relIndex W
        ≤ (2 ^ (2 * a + 1)) * (2 ^ (2 * a + 1)) :=
          Nat.mul_le_mul hX'bound hHbound
      _ = (2 ^ (2 * a + 1)) ^ 2 := by rw [pow_two]
  have hltq : (2 ^ (2 * a + 1)) ^ 2 < (2 ^ (2 * a + 1)) ^ 4 := by
    have h1 : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_pow (by omega) (by norm_num)
    exact Nat.pow_lt_pow_right h1 (by norm_num)
  have hq : (2 ^ (2 * a + 1)) ^ 4 = (2 ^ f) ^ 2 := by
    rw [← pow_mul, ← pow_mul, hf]
    congr 1
    ring
  have hlt : (W ⊓ centralizer (X' : Set G)).relIndex W *
        (W ⊓ centralizer (H : Set G)).relIndex W <
      if Even (ε + 2 + b₁) then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2 := by
    split_ifs with hc
    · exact hbase.trans_lt hltq
    · rw [← hq]
      exact hbase.trans_lt hltq
  have hLc : t.Lv (ε + 2 + b₁) ≤ centralizer (W : Set G) :=
    t.Lv_le_centralizer_of_relIndex_mul_lt hfr (ε + 2 + b₁) hX'pc hHpc hX'K hHK hX'Q hH hlt
  have hcsub : Even ((ε + 2 + b₁) - (ε + 1)) := by
    rw [show (ε + 2 + b₁) - (ε + 1) = (b₁ : ℤ) + 1 by ring]
    exact ⟨(m : ℤ) + 1, by rw [hm]; push_cast; ring⟩
  have hL : t.Lv (ε + 1) ≤ centralizer (t.Zv (ε + 1) : Set G) :=
    t.Lv_le_centralizer_of_even_sub hfr hcsub hLc
  exact t.false_of_Zv_le_of_le_centralizer hfr (u := ε) (v := ε + 1)
    (Or.inr rfl) hZ hL

end Track

end CFSG.Quasithin.Stroth.Rq
