module

public import CFSG.Quasithin.Recognition.Stroth.Str83Rq412
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
public import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRoot

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem IsFixRadius.Lv_le_centralizer_and_Zv_le
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₁ : ℕ}
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₁ : Odd b₁)
    (hcomm : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ = ⊥) :
    t.Lv ε ≤ centralizer (t.Zv ε : Set G) ∧ t.Zv ε ≤ t.Zv (ε + 1) := by
  have heven : Even ((ε + 1 + b₁) - ε) := by
    rw [show (ε + 1 + b₁ : ℤ) - ε = (b₁ : ℤ) + 1 by ring]
    rw [Int.even_add_one, Int.even_coe_nat]
    exact Nat.not_even_iff_odd.mpr hb₁
  have hL : t.Lv ε ≤ centralizer (t.Zv ε : Set G) :=
    t.Lv_le_centralizer_of_even_sub hfr (u := ε + 1 + b₁) (v := ε) heven
      (IsFixRadius.Lv_add_le_centralizer t hfr h₁ hcomm)
  exact ⟨hL, t.Zv_le_of_Lv_le_centralizer hfr (u := ε) (v := ε + 1) (Or.inr rfl) hL⟩

theorem IsMaxArc.eq_of_Zv_le
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1) {ε : ℤ} {n b₀ b₁ : ℕ}
    (h : t.IsMaxArc ε n) (h₀ : t.IsFixRadius ε b₀) (h₁ : t.IsFixRadius (ε + 1) b₁)
    (hb₁ : Odd b₁) (hZ : t.Zv ε ≤ t.Zv (ε + 1)) :
    n = 2 * (b₁ + 1) ∧ b₀ = b₁ + 1 ∧
      t.Zv (ε + 1 + b₁) = omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + n))) := by
  obtain ⟨j, hj⟩ := hb₁
  have hb0le : b₁ + 1 ≤ b₀ := by
    by_contra hlt
    have hb0b1 : b₀ ≤ b₁ := by omega
    have hleGv : t.Zv ε ≤ t.Gv (ε + b₀ + 1) := by
      refine hZ.trans (h₁.le_Gw.trans ?_)
      have hwin := win_mono (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
        (x₁ := t.x₁) (x₂ := t.x₂)
        (a := ε + 1 - b₁) (b := ε + 1 + b₁)
        (a' := ε + b₀ + 1) (b' := ε + b₀ + 1)
        (by push_cast; omega) (by push_cast; omega)
      simpa using hwin.trans_eq (win_self (ε + b₀ + 1))
    exact h₀.not_le_Gv hleGv
  obtain ⟨m', hm'⟩ := even_iff_two_dvd.mp (Track.IsMaxArc.even t hfr h hrq)
  have hmax : t.IsMaxArc ε (2 * m') := by simpa [hm'] using h
  have hself := Track.IsMaxArc.fixRadius_self t hfr hmax h₀
  have hadd := Track.IsMaxArc.fixRadius_add_one t hfr hmax h₁
  have hm'eq : m' = b₁ + 1 := by
    rcases hadd with h | h
    · omega
    · omega
  have hb0eq : b₀ = b₁ + 1 := by omega
  have hn : n = 2 * (b₁ + 1) := by rw [hm', hm'eq]
  have hwrad : t.IsFixRadius (ε + 1 + b₁) (b₁ + 1) := by
    have hshift := IsFixRadius.shift t h₀ (j + 1 : ℤ)
    rw [show ε + 1 + b₁ = ε + 2 * ((j : ℤ) + 1) by rw [hj]; push_cast; ring,
      ← hb0eq]
    exact hshift
  have hwmem : t.Zv (ε + 1 + b₁) ≤ t.Gw ε (ε + n) := by
    have hle := hwrad.le_Gw
    rwa [show ε + 1 + (b₁ : ℤ) - ↑(b₁ + 1) = ε by push_cast; ring,
      show ε + 1 + (b₁ : ℤ) + ↑(b₁ + 1) = ε + n by rw [hn]; push_cast; ring] at hle
  have hZleP : t.Zv (ε + 1 + b₁) ≤ pCoreOf 2 (t.Gw ε (ε + n)) :=
    t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv _) hwmem
  refine ⟨hn, hb0eq, le_antisymm ?_ ?_⟩
  · intro x hx
    have hx' : x ∈ omegaOneCenterOf (t.Qv (ε + 1 + b₁)) := by
      rwa [← t.Zv_eq]
    have hx2 : x ^ 2 = 1 := A4.sq_eq_one_of_mem_omegaOneCenterOf hx'
    exact Track.IsMaxArc.mem_omegaOneCenterOf t hfr h (hZleP hx) hx2
  · exact Track.IsMaxArc.omegaOneCenterOf_le t hfr h hZleP
      (t.Zv_ne_bot hfr.hF _) (t.K_le_normalizer_Zv _)

theorem IsMaxArc.card_Zv_add_one_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {b₁ : ℕ} (h : t.IsMaxArc ε (2 * (b₁ + 1)))
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₁ : Odd b₁) :
    Nat.card (t.Zv (ε + 1)) ≤
      if Even ε then (2 ^ (2 * a + 1)) ^ 2 * 2 ^ f else (2 ^ f) ^ 2 * 2 ^ (2 * a + 1) := by
  obtain ⟨j, hj⟩ := hb₁
  set m : ℕ := b₁ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hmval : m = 2 * (j + 1) := by omega
  have hb1m : (b₁ : ℤ) = (m : ℤ) - 1 := by omega
  set A0 : Subgroup G := t.Zv (ε + 1) with hA0
  set A1 : Subgroup G := A0 ⊓ t.Qv (ε + (m : ℤ)) with hA1
  set A2 : Subgroup G := A1 ⊓ t.Qv (ε + 2 - (m : ℤ)) with hA2
  set A3 : Subgroup G := A2 ⊓ t.Qv (ε + (m : ℤ) + 1) with hA3def
  have hA1le : A1 ≤ A0 := by rw [hA1]; exact inf_le_left
  have hA1Q : A1 ≤ t.Qv (ε + (m : ℤ)) := by rw [hA1]; exact inf_le_right
  have hA2le : A2 ≤ A1 := by rw [hA2]; exact inf_le_left
  have hA2Q : A2 ≤ t.Qv (ε + 2 - (m : ℤ)) := by rw [hA2]; exact inf_le_right
  have hA3le : A3 ≤ A2 := by rw [hA3def]; exact inf_le_left
  have hA3Q : A3 ≤ t.Qv (ε + (m : ℤ) + 1) := by rw [hA3def]; exact inf_le_right
  have hsq0 : ∀ x ∈ A0, x ^ 2 = 1 := by
    intro x hx
    rw [hA0, t.Zv_eq] at hx
    exact A4.sq_eq_one_of_mem_omegaOneCenterOf hx
  have hsqA1 : ∀ x ∈ A1, x ^ 2 ∈ t.Qv (ε + 2 - (m : ℤ)) := by
    intro x hx
    rw [hsq0 x (hA1le hx)]
    exact (t.Qv _).one_mem
  have hsqA2 : ∀ x ∈ A2, x ^ 2 ∈ t.Qv (ε + (m : ℤ) + 1) := by
    intro x hx
    rw [hsq0 x ((hA2le.trans hA1le) hx)]
    exact (t.Qv _).one_mem
  have hA0win : A0 ≤ t.Gw (ε + 2 - (m : ℤ)) (ε + (m : ℤ)) := by
    have hle := h₁.le_Gw
    rwa [show (ε + 1) - (b₁ : ℤ) = ε + 2 - (m : ℤ) by rw [hb1m]; ring,
      show (ε + 1) + (b₁ : ℤ) = ε + (m : ℤ) by rw [hb1m]; ring] at hle
  have hA0win' : A0 ≤ t.Gw (ε + (m : ℤ) - 1) (ε + (m : ℤ)) :=
    hA0win.trans (win_mono (by omega) le_rfl)
  have hA0P : A0 ≤ pCoreOf 2 (t.Gw (ε + (m : ℤ) - 1) (ε + (m : ℤ))) :=
    t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv (ε + 1)) hA0win'
  have hrel0 : (t.Qv (ε + (m : ℤ))).relIndex A0 ≤
      if Even (ε + (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f :=
    t.relIndex_Qv_le_of_sq_mem_left hfr (ε + (m : ℤ)) hA0P
      (fun x hx => by rw [hsq0 x hx]; exact (t.Qv _).one_mem)
  have hwin1 : t.Gw (ε + 2 - (m : ℤ)) (ε + (m : ℤ) + 1) =
      t.Gw (ε + 2 - (m : ℤ)) (ε + (m : ℤ)) ⊓ t.Gv (ε + (m : ℤ) + 1) := by
    have hw := win_add_one_right (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      (x₁ := t.x₁) (x₂ := t.x₂) (a := ε + 2 - (m : ℤ)) (b := ε + (m : ℤ))
      (by omega)
    simpa [Track.Gw, Track.Gv] using hw
  have hA1win : A1 ≤ t.Gw (ε + 2 - (m : ℤ)) (ε + (m : ℤ) + 1) := by
    rw [hwin1]
    exact le_inf (hA1le.trans hA0win)
      (hA1Q.trans (t.Qv_le_Gv hfr (ε + (m : ℤ))).2)
  have hA1win' : A1 ≤ t.Gw (ε + 2 - (m : ℤ)) (ε + 3 - (m : ℤ)) :=
    hA1win.trans (win_mono le_rfl (by omega))
  have hA1P : A1 ≤ pCoreOf 2 (t.Gw (ε + 2 - (m : ℤ)) (ε + 3 - (m : ℤ))) :=
    t.le_pCoreOf_Gw hfr (by omega)
      ((t.isPGroup_Zv (ε + 1)).to_le hA1le) hA1win'
  have hA1P' : A1 ≤ pCoreOf 2 (t.Gw (ε + 2 - (m : ℤ))
      ((ε + 2 - (m : ℤ)) + 1)) := by
    rwa [show ε + 2 - (m : ℤ) + 1 = ε + 3 - (m : ℤ) by ring]
  have hrel1 : (t.Qv (ε + 2 - (m : ℤ))).relIndex A1 ≤
      if Even (ε + 2 - (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f :=
    t.relIndex_Qv_le_of_sq_mem hfr (ε + 2 - (m : ℤ)) hA1P' hsqA1
  have hwin2 : t.Gw (ε + 1 - (m : ℤ)) (ε + (m : ℤ) + 1) =
      t.Gv (ε + 1 - (m : ℤ)) ⊓
        t.Gw (ε + 2 - (m : ℤ)) (ε + (m : ℤ) + 1) := by
    have hw := win_sub_one_left (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      (x₁ := t.x₁) (x₂ := t.x₂) (a := ε + 2 - (m : ℤ)) (b := ε + (m : ℤ) + 1)
      (by omega)
    rw [show ε + 2 - (m : ℤ) - 1 = ε + 1 - (m : ℤ) by ring] at hw
    simpa [Track.Gw, Track.Gv] using hw
  have hQvGv2 : t.Qv (ε + 2 - (m : ℤ)) ≤ t.Gv (ε + 1 - (m : ℤ)) := by
    simpa [show ε + 2 - (m : ℤ) - 1 = ε + 1 - (m : ℤ) by ring] using
      (t.Qv_le_Gv hfr (ε + 2 - (m : ℤ))).1
  have hA2win : A2 ≤ t.Gw (ε + 1 - (m : ℤ)) (ε + (m : ℤ) + 1) := by
    rw [hwin2]
    exact le_inf (hA2Q.trans hQvGv2) (hA2le.trans hA1win)
  have hA2win' : A2 ≤ t.Gw (ε + (m : ℤ)) (ε + (m : ℤ) + 1) :=
    hA2win.trans (win_mono (by omega) le_rfl)
  have hA2P : A2 ≤ pCoreOf 2 (t.Gw (ε + (m : ℤ)) (ε + (m : ℤ) + 1)) :=
    t.le_pCoreOf_Gw hfr (by omega)
      ((t.isPGroup_Zv (ε + 1)).to_le (hA2le.trans hA1le)) hA2win'
  have hA2P' : A2 ≤ pCoreOf 2 (t.Gw ((ε + (m : ℤ) + 1) - 1) (ε + (m : ℤ) + 1)) := by
    rwa [show (ε + (m : ℤ) + 1) - 1 = ε + (m : ℤ) by ring]
  have hrel2 : (t.Qv (ε + (m : ℤ) + 1)).relIndex A2 ≤
      if Even (ε + (m : ℤ) + 1) then 2 ^ (2 * a + 1) else 2 ^ f :=
    t.relIndex_Qv_le_of_sq_mem_left hfr (ε + (m : ℤ) + 1) hA2P' hsqA2
  have hwin3 : t.Gw (ε + 1 - (m : ℤ)) (ε + (m : ℤ) + 2) =
      t.Gw (ε + 1 - (m : ℤ)) (ε + (m : ℤ) + 1) ⊓
        t.Gv (ε + (m : ℤ) + 2) := by
    have hw := win_add_one_right (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      (x₁ := t.x₁) (x₂ := t.x₂) (a := ε + 1 - (m : ℤ)) (b := ε + (m : ℤ) + 1)
      (by omega)
    rw [show ε + (m : ℤ) + 1 + 1 = ε + (m : ℤ) + 2 by ring] at hw
    simpa [Track.Gw, Track.Gv] using hw
  have hQvGv3 : t.Qv (ε + (m : ℤ) + 1) ≤ t.Gv (ε + (m : ℤ) + 2) := by
    simpa [show ε + (m : ℤ) + 1 + 1 = ε + (m : ℤ) + 2 by ring] using
      (t.Qv_le_Gv hfr (ε + (m : ℤ) + 1)).2
  have hA3win : A3 ≤ t.Gw (ε + 1 - (m : ℤ)) (ε + (m : ℤ) + 2) := by
    rw [hwin3]
    exact le_inf (hA3le.trans hA2win) (hA3Q.trans hQvGv3)
  have hA3bot : A3 = ⊥ := by
    have hlen : ((2 * m : ℕ) : ℤ) <
        (ε + (m : ℤ) + 2) - (ε + 1 - (m : ℤ)) := by
      push_cast
      omega
    have hPb := h.pCoreOf_eq_bot (ε + 1 - (m : ℤ)) (ε + (m : ℤ) + 2) hlen
    have hA3P : A3 ≤ pCoreOf 2 (t.Gw (ε + 1 - (m : ℤ)) (ε + (m : ℤ) + 2)) :=
      t.le_pCoreOf_Gw hfr (by omega)
        ((t.isPGroup_Zv (ε + 1)).to_le (hA3le.trans (hA2le.trans hA1le))) hA3win
    rw [hPb] at hA3P
    exact le_bot_iff.mp hA3P
  have hcard0 : Nat.card A0 = Nat.card A1 * A1.relIndex A0 :=
    C5.card_eq_card_mul_relIndex hA1le
  have hcard1 : Nat.card A1 = Nat.card A2 * A2.relIndex A1 :=
    C5.card_eq_card_mul_relIndex hA2le
  have hcard2 : Nat.card A2 = Nat.card A3 * A3.relIndex A2 :=
    C5.card_eq_card_mul_relIndex hA3le
  have hcardA3 : Nat.card A3 = 1 := by rw [hA3bot, Subgroup.card_bot]
  have hrelA1 : A1.relIndex A0 = (t.Qv (ε + (m : ℤ))).relIndex A0 := by
    rw [hA1]
    exact Subgroup.inf_relIndex_left A0 _
  have hrelA2 : A2.relIndex A1 = (t.Qv (ε + 2 - (m : ℤ))).relIndex A1 := by
    rw [hA2]
    exact Subgroup.inf_relIndex_left A1 _
  have hrelA3 : A3.relIndex A2 = (t.Qv (ε + (m : ℤ) + 1)).relIndex A2 := by
    rw [hA3def]
    exact Subgroup.inf_relIndex_left A2 _
  have hrelA1' : A1.relIndex A0 ≤
      if Even (ε + (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f := by
    rw [hrelA1]
    exact hrel0
  have hrelA2' : A2.relIndex A1 ≤
      if Even (ε + 2 - (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f := by
    rw [hrelA2]
    exact hrel1
  have hrelA3' : A3.relIndex A2 ≤
      if Even (ε + (m : ℤ) + 1) then 2 ^ (2 * a + 1) else 2 ^ f := by
    rw [hrelA3]
    exact hrel2
  have hcardA0 : Nat.card A0 =
      Nat.card A3 * (A3.relIndex A2 * (A2.relIndex A1 * A1.relIndex A0)) := by
    rw [hcard0, hcard1, hcard2]
    ring
  have hbound : A3.relIndex A2 * (A2.relIndex A1 * A1.relIndex A0) ≤
      (if Even (ε + (m : ℤ) + 1) then 2 ^ (2 * a + 1) else 2 ^ f) *
        ((if Even (ε + 2 - (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f) *
          (if Even (ε + (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f)) :=
    Nat.mul_le_mul hrelA3' (Nat.mul_le_mul hrelA2' hrelA1')
  have hmain : Nat.card A0 ≤
      (if Even (ε + (m : ℤ) + 1) then 2 ^ (2 * a + 1) else 2 ^ f) *
        ((if Even (ε + 2 - (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f) *
          (if Even (ε + (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f)) := by
    rw [hcardA0, hcardA3, one_mul]
    exact hbound
  have hmEven : Even (m : ℤ) := by
    rw [show (m : ℤ) = 2 * ((j : ℤ) + 1) by rw [hmval]; push_cast; ring]
    exact even_two_mul _
  by_cases hε : Even ε
  · have hparA : Even (ε + (m : ℤ)) := hε.add hmEven
    have hparB : Even (ε + 2 - (m : ℤ)) := by
      rw [show ε + 2 - (m : ℤ) = ε + 2 * (-(j : ℤ)) by
        rw [hmval]; push_cast; ring]
      exact hε.add (even_two_mul _)
    have hparC : ¬ Even (ε + (m : ℤ) + 1) := by
      exact Int.not_even_iff_odd.mpr hparA.add_one
    have hval : (if Even (ε + (m : ℤ) + 1) then 2 ^ (2 * a + 1) else 2 ^ f) *
        ((if Even (ε + 2 - (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f) *
          (if Even (ε + (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f)) =
        (2 ^ (2 * a + 1)) ^ 2 * 2 ^ f := by
      rw [if_neg hparC, if_pos hparB, if_pos hparA]
      ring
    rw [if_pos hε]
    exact hmain.trans_eq hval
  · have hoddε : Odd ε := Int.not_even_iff_odd.mp hε
    have hoddA : Odd (ε + (m : ℤ)) := hoddε.add_even hmEven
    have hparA : ¬ Even (ε + (m : ℤ)) := Int.not_even_iff_odd.mpr hoddA
    have hparB : ¬ Even (ε + 2 - (m : ℤ)) := by
      refine Int.not_even_iff_odd.mpr ?_
      rw [show ε + 2 - (m : ℤ) = ε + 2 * (-(j : ℤ)) by
        rw [hmval]; push_cast; ring]
      exact hoddε.add_even (even_two_mul _)
    have hparC : Even (ε + (m : ℤ) + 1) := hoddA.add_one
    have hval : (if Even (ε + (m : ℤ) + 1) then 2 ^ (2 * a + 1) else 2 ^ f) *
        ((if Even (ε + 2 - (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f) *
          (if Even (ε + (m : ℤ)) then 2 ^ (2 * a + 1) else 2 ^ f)) =
        (2 ^ f) ^ 2 * 2 ^ (2 * a + 1) := by
      rw [if_pos hparC, if_neg hparB, if_neg hparA]
      ring
    rw [if_neg hε]
    exact hmain.trans_eq hval

end Track

end CFSG.Quasithin.Stroth.Rq
