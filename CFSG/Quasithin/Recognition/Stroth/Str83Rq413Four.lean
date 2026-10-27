module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackModule
public import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRoot
import CFSG.Quasithin.Recognition.Stroth.Str83RqModBridge
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Core
import CFSG.Quasithin.Recognition.Stroth.Str83RqT6
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeSeries

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem r8four_Gw_left {a b : ℤ} {X : Subgroup G}
    (hX : X ≤ t.Gw a b) (hY : X ≤ t.Gv (a - 1)) : X ≤ t.Gw (a - 1) b := by
  intro x hx
  refine mem_win_iff.mpr fun i hi1 hi2 => ?_
  by_cases hia : i = a - 1
  · subst i; exact hY hx
  · exact mem_win_iff.mp (hX hx) i (by omega) hi2

private theorem r8four_Gw_right {a b : ℤ} {X : Subgroup G}
    (hX : X ≤ t.Gw a b) (hY : X ≤ t.Gv (b + 1)) : X ≤ t.Gw a (b + 1) := by
  intro x hx
  refine mem_win_iff.mpr fun i hi1 hi2 => ?_
  by_cases hib : i = b + 1
  · subst i; exact hY hx
  · exact mem_win_iff.mp (hX hx) i hi1 (by omega)

private theorem r8four_card_Zv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} (h : t.IsMaxArc ε 4) (hε : Even ε)
    (hZ : t.Zv ε ≤ t.Zv (ε + 1)) :
    Nat.card (t.Zv ε) = 2 ^ (2 * a + 1) := by
  have hZH : t.Zv ε ≤ t.Gw ε (ε + 2) := by
    intro x hx
    refine mem_win_iff.mpr fun i hi1 hi2 => ?_
    rcases (show i = ε ∨ i = ε + 1 ∨ i = ε + 2 by omega) with h | h | h
    · rw [h]; exact t.Qv_le_Gv_self ε (t.Zv_le_Qv ε hx)
    · rw [h]; exact (t.Qv_le_Gv hfr ε).2 (t.Zv_le_Qv ε hx)
    · rw [h]
      simpa only [show (ε : ℤ) + 1 + 1 = ε + 2 by ring] using
        (t.Qv_le_Gv hfr (ε + 1)).2 (t.Zv_le_Qv (ε + 1) (hZ hx))
  obtain ⟨y, -, -, hGw, -, hZy⟩ := Track.exists_reflection t ε
  have hGw' : (t.Gw ε (ε + 2)).map (MulAut.conj y).toMonoidHom = t.Gw (ε - 2) ε := by
    have hh := hGw ε (ε + 2)
    rw [show 2 * ε - (ε + 2) = ε - 2 by ring, show 2 * ε - ε = ε by ring] at hh
    exact hh
  have hZmap : (t.Zv ε).map (MulAut.conj y).toMonoidHom = t.Zv ε := by
    have hh := hZy ε
    rwa [show 2 * ε - ε = ε by ring] at hh
  have hZGw_left : t.Zv ε ≤ t.Gw (ε - 2) ε := by
    have hmaple : (t.Zv ε).map (MulAut.conj y).toMonoidHom ≤ t.Gw (ε - 2) ε := by
      rw [← hGw']; exact Subgroup.map_mono hZH
    rwa [hZmap] at hmaple
  have hZarc : t.Zv ε ≤ t.Gw (ε - 2) (ε + 2) := by
    intro x hx
    refine mem_win_iff.mpr fun i hi1 hi2 => ?_
    rcases le_total i ε with hle | hle
    · exact mem_win_iff.mp (hZGw_left hx) i hi1 hle
    · exact mem_win_iff.mp (hZH hx) i hle hi2
  have hshift : t.IsMaxArc (ε - 2) 4 := by
    have hh := h.shift t (-1 : ℤ)
    rwa [show ε + 2 * (-1 : ℤ) = ε - 2 by ring] at hh
  have hZP : t.Zv ε ≤ pCoreOf 2 (t.Gw (ε - 2) ((ε - 2) + ((4 : ℕ) : ℤ))) := by
    simpa only [show (ε : ℤ) - 2 + ((4 : ℕ) : ℤ) = ε + 2 by push_cast; ring] using
      (t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Zv ε) hZarc)
  have hKZ : t.K ≤ normalizer (t.Zv ε : Set G) :=
    (t.K_le_Gv ε).trans (t.Gv_le_normalizer_Zv ε)
  have hWle : omegaOneCenterOf (pCoreOf 2 (t.Gw (ε - 2) ((ε - 2) + ((4 : ℕ) : ℤ)))) ≤
      t.Zv ε :=
    hshift.omegaOneCenterOf_le t hfr hZP (t.Zv_ne_bot hfr.hF ε) hKZ
  have hZleW : t.Zv ε ≤
      omegaOneCenterOf (pCoreOf 2 (t.Gw (ε - 2) ((ε - 2) + ((4 : ℕ) : ℤ)))) := by
    intro x hx
    refine hshift.mem_omegaOneCenterOf t hfr (hZP hx) ?_
    have hx' : x ∈ omegaOneCenterOf (t.Qv ε) := by rwa [t.Zv_eq ε] at hx
    exact A4.sq_eq_one_of_mem_omegaOneCenterOf hx'
  have hWeq :
      omegaOneCenterOf (pCoreOf 2 (t.Gw (ε - 2) ((ε - 2) + ((4 : ℕ) : ℤ)))) = t.Zv ε :=
    le_antisymm hWle hZleW
  have hcardW := hshift.card_omegaOneCenterOf t hfr (e := ε + 2) (Or.inr (by ring))
  simpa only [hWeq, if_pos (hε.add (by norm_num : Even (2 : ℤ)))] using hcardW

private theorem r8four_card_pCoreOf_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} (h : t.IsMaxArc ε 4) (hε : Even ε) :
    Nat.card (pCoreOf 2 (t.Gw ε (ε + 1))) ≤
      (2 ^ (2 * a + 1)) ^ 4 * (2 ^ f) ^ 2 := by
  set X0 : Subgroup G := pCoreOf 2 (t.Gw ε (ε + 1)) with hX0
  set X1 : Subgroup G := X0 ⊓ t.Gv (ε - 1) with hX1
  set X2 : Subgroup G := X1 ⊓ t.Gv (ε - 2) with hX2
  set X3 : Subgroup G := X2 ⊓ t.Gv (ε + 2) with hX3
  set X4 : Subgroup G := X3 ⊓ t.Gv (ε + 3) with hX4
  have hX0p : IsPGroup 2 X0 := by rw [hX0]; exact pCoreOf_isPGroup 2 _
  have hX0w : X0 ≤ t.Gw ε (ε + 1) := by rw [hX0]; exact pCoreOf_le 2 _
  have hX1p : IsPGroup 2 X1 := hX0p.to_le inf_le_left
  have hX1w : X1 ≤ t.Gw (ε - 1) (ε + 1) :=
    r8four_Gw_left t (inf_le_left.trans hX0w) inf_le_right
  have c1 := t.card_le_mul_card_inf_Gv_sub_one hfr ε hX0p hX0w
  rw [if_pos hε, ← hX1] at c1
  have hX2p : IsPGroup 2 X2 := hX1p.to_le inf_le_left
  have hX1wε : X1 ≤ t.Gw (ε - 1) ((ε - 1) + 1) := by
    have h' : X1 ≤ t.Gw (ε - 1) ε := hX1w.trans (win_mono le_rfl (by omega))
    simpa only [show (ε : ℤ) - 1 + 1 = ε by ring] using h'
  have c2 := t.card_le_mul_card_inf_Gv_sub_one hfr (ε - 1) hX1p hX1wε
  have hodd1 : ¬ Even (ε - 1) := by rw [Int.even_sub_one]; exact not_not.mpr hε
  rw [if_neg hodd1, show (ε : ℤ) - 1 - 1 = ε - 2 by ring, ← hX2] at c2
  have hX2w : X2 ≤ t.Gw (ε - 2) (ε + 1) := by
    simpa only [show (ε : ℤ) - 1 - 1 = ε - 2 by ring] using
      r8four_Gw_left t (inf_le_left.trans hX1w) inf_le_right
  have hX2w' : X2 ≤ t.Gw ((ε + 1) - 1) (ε + 1) := by
    simpa only [show (ε : ℤ) + 1 - 1 = ε by ring] using hX2w.trans (win_mono (by omega) le_rfl)
  have c3 := t.card_le_mul_card_inf_Gv_add_one hfr (ε + 1) hX2p hX2w'
  have hodd2 : ¬ Even (ε + 1) := by rw [Int.even_add_one]; exact not_not.mpr hε
  rw [if_neg hodd2, show (ε : ℤ) + 1 + 1 = ε + 2 by ring, ← hX3] at c3
  have hX3p : IsPGroup 2 X3 := hX2p.to_le inf_le_left
  have hX3w : X3 ≤ t.Gw (ε - 2) (ε + 2) := by
    have hY : X3 ≤ t.Gv ((ε + 1) + 1) := by
      simpa only [show (ε : ℤ) + 1 + 1 = ε + 2 by ring] using
        (inf_le_right : X3 ≤ t.Gv (ε + 2))
    simpa only [show (ε : ℤ) + 1 + 1 = ε + 2 by ring] using
      r8four_Gw_right t (inf_le_left.trans hX2w) hY
  have hX3w' : X3 ≤ t.Gw ((ε + 2) - 1) (ε + 2) := by
    simpa only [show (ε : ℤ) + 2 - 1 = ε + 1 by ring] using hX3w.trans (win_mono (by omega) le_rfl)
  have c4 := t.card_le_mul_card_inf_Gv_add_one hfr (ε + 2) hX3p hX3w'
  have heven2 : Even (ε + 2) := hε.add (by norm_num : Even (2 : ℤ))
  rw [if_pos heven2, show (ε : ℤ) + 2 + 1 = ε + 3 by ring, ← hX4] at c4
  have hX4p : IsPGroup 2 X4 := hX3p.to_le inf_le_left
  have hX4w : X4 ≤ t.Gw (ε - 2) (ε + 3) := by
    have hY : X4 ≤ t.Gv ((ε + 2) + 1) := by
      simpa only [show (ε : ℤ) + 2 + 1 = ε + 3 by ring] using
        (inf_le_right : X4 ≤ t.Gv (ε + 3))
    simpa only [show (ε : ℤ) + 2 + 1 = ε + 3 by ring] using
      r8four_Gw_right t (inf_le_left.trans hX3w) hY
  have hX4P : X4 ≤ pCoreOf 2 (t.Gw (ε - 2) (ε + 3)) :=
    t.le_pCoreOf_Gw hfr (by omega) hX4p hX4w
  have hbot : pCoreOf 2 (t.Gw (ε - 2) (ε + 3)) = ⊥ :=
    h.pCoreOf_eq_bot (ε - 2) (ε + 3) (by omega)
  rw [hbot] at hX4P
  have hcardX4 : Nat.card X4 = 1 := by rw [le_bot_iff.mp hX4P, Subgroup.card_bot]
  change Nat.card X0 ≤ (2 ^ (2 * a + 1)) ^ 4 * (2 ^ f) ^ 2
  calc Nat.card X0 ≤ (2 ^ (2 * a + 1)) ^ 2 * Nat.card X1 := c1
    _ ≤ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ f * Nat.card X2) :=
        Nat.mul_le_mul_left _ c2
    _ ≤ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ f * (2 ^ f * Nat.card X3)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ c3)
    _ ≤ (2 ^ (2 * a + 1)) ^ 2 *
          (2 ^ f * (2 ^ f * ((2 ^ (2 * a + 1)) ^ 2 * Nat.card X4))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ c4))
    _ = (2 ^ (2 * a + 1)) ^ 4 * (2 ^ f) ^ 2 := by rw [hcardX4]; ring_nf

private theorem r8four_relIndex_Zv_Qv_add_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} (hε : Even ε) (hf : f = 2 * (2 * a + 1))
    (hcard : Nat.card (t.Zv (ε + 1)) = (2 ^ f) ^ 2)
    (hPle : Nat.card (pCoreOf 2 (t.Gw ε (ε + 1))) ≤
      (2 ^ (2 * a + 1)) ^ 4 * (2 ^ f) ^ 2) :
    (t.Zv (ε + 1)).relIndex (t.Qv (ε + 1)) < (2 ^ f) ^ 2 := by
  set P : Subgroup G := pCoreOf 2 (t.Gw ε (ε + 1)) with hP
  set Q : Subgroup G := t.Qv (ε + 1) with hQ
  set Z : Subgroup G := t.Zv (ε + 1) with hZ
  have hodd : ¬ Even (ε + 1) := by rw [Int.even_add_one]; exact not_not.mpr hε
  have hQP : Q ≤ P := by
    rw [hQ, hP]
    refine t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Qv (ε + 1)) ?_
    intro x hx
    refine mem_win_iff.mpr fun i hi1 hi2 => ?_
    rcases (show i = ε ∨ i = ε + 1 by omega) with h | h
    · rw [h]
      simpa only [show (ε : ℤ) + 1 - 1 = ε by ring] using
        (t.Qv_le_Gv hfr (ε + 1)).1 hx
    · rw [h]; exact t.Qv_le_Gv_self (ε + 1) hx
  have hrelQ : Q.relIndex P = 2 ^ f := by
    rw [hQ, hP]
    have h := (t.relIndex_Qv_pCoreOf hfr (ε + 1)).1
    rw [show (ε : ℤ) + 1 - 1 = ε by ring, if_neg hodd] at h
    exact h
  have hcardP : Nat.card P = 2 ^ f * Nat.card Q := by
    have h := Subgroup.relIndex_mul_card Q P
    rw [inf_eq_left.mpr hQP, hrelQ] at h
    exact h.symm
  have hcardQ : Nat.card Q ≤ (2 ^ (2 * a + 1)) ^ 4 * 2 ^ f := by
    have hle : 2 ^ f * Nat.card Q ≤ 2 ^ f * ((2 ^ (2 * a + 1)) ^ 4 * 2 ^ f) := by
      calc 2 ^ f * Nat.card Q = Nat.card P := hcardP.symm
        _ ≤ (2 ^ (2 * a + 1)) ^ 4 * (2 ^ f) ^ 2 := by
            rw [hP]; exact hPle
        _ = 2 ^ f * ((2 ^ (2 * a + 1)) ^ 4 * 2 ^ f) := by ring
    exact Nat.le_of_mul_le_mul_left hle (by positivity)
  have hZQ : Z ≤ Q := by rw [hZ, hQ]; exact t.Zv_le_Qv (ε + 1)
  have hcardZQ : Z.relIndex Q * Nat.card Z = Nat.card Q := by
    have h := Subgroup.relIndex_mul_card Z Q
    rwa [inf_eq_left.mpr hZQ] at h
  have hrq : 2 ^ f = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [hf]
    calc 2 ^ (2 * (2 * a + 1)) = 2 ^ ((2 * a + 1) * 2) :=
          congrArg (fun e => 2 ^ e) (by ring)
      _ = (2 ^ (2 * a + 1)) ^ 2 := pow_mul 2 (2 * a + 1) 2
  have hRle : Z.relIndex Q ≤ 2 ^ f := by
    have hbound : (2 ^ f) ^ 2 * Z.relIndex Q ≤ (2 ^ f) ^ 2 * 2 ^ f := by
      calc (2 ^ f) ^ 2 * Z.relIndex Q = Z.relIndex Q * (2 ^ f) ^ 2 := by ring
        _ = Z.relIndex Q * Nat.card Z := by rw [hcard]
        _ = Nat.card Q := hcardZQ
        _ ≤ (2 ^ (2 * a + 1)) ^ 4 * 2 ^ f := hcardQ
        _ = (2 ^ f) ^ 2 * 2 ^ f := by rw [hrq]; ring
    exact Nat.le_of_mul_le_mul_left hbound (by positivity)
  have hr4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  have hr1 : 1 < 2 ^ f := by omega
  have hlt : 2 ^ f < (2 ^ f) ^ 2 := by
    rw [pow_two]
    nlinarith [hr1]
  exact lt_of_le_of_lt hRle hlt

private theorem r8four_exists_fixedPointFree {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} (h : t.IsMaxArc ε 4) (hε : Even ε)
    (hf : f = 2 * (2 * a + 1)) (hC : t.Lv ε ≤ centralizer (t.Zv ε : Set G))
    (hZ : t.Zv ε ≤ t.Zv (ε + 1)) (hcard : Nat.card (t.Zv (ε + 1)) = (2 ^ f) ^ 2) :
    ∃ w ∈ t.Lv (ε + 1), Odd (orderOf w) ∧
      t.Zv (ε + 1) ⊓ centralizer ({w} : Set G) = ⊥ := by
  have hodd : ¬ Even (ε + 1) := by rw [Int.even_add_one]; exact not_not.mpr hε
  have hCnext : ¬ t.Lv (ε + 1) ≤ centralizer (t.Zv (ε + 1) : Set G) := by
    intro hC'
    exact t.false_of_Zv_le_of_le_centralizer hfr (Or.inr rfl) hZ hC'
  have hcard' : Nat.card (t.Zv (ε + 1)) =
      if Even (ε + 1) then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2 := by
    rw [if_neg hodd, hcard]
  have hirr : ∀ U : Subgroup G, U ≤ t.Zv (ε + 1) →
      t.Lv (ε + 1) ≤ normalizer (U : Set G) → U = ⊥ ∨ U = t.Zv (ε + 1) :=
    fun U hU hUL => t.eq_bot_or_eq_of_card_Zv hfr (ε + 1) hcard' hCnext hU hUL
  have hLZ : t.Lv (ε + 1) ≤ normalizer (t.Zv (ε + 1) : Set G) :=
    (t.Lv_le_Gv (ε + 1)).trans (t.Gv_le_normalizer_Zv (ε + 1))
  have hZc : ∀ x ∈ t.Zv (ε + 1), ∀ y ∈ t.Zv (ε + 1), x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer (ε + 1) hx) y
      (t.Zv_le_Qv (ε + 1) hy)).symm
  have hZ2 : ∀ x ∈ t.Zv (ε + 1), x ^ 2 = 1 := by
    intro x hx
    have hx' : x ∈ omegaOneCenterOf (t.Qv (ε + 1)) := by rwa [t.Zv_eq (ε + 1)] at hx
    exact A4.sq_eq_one_of_mem_omegaOneCenterOf hx'
  exact exists_odd_inf_centralizer_eq_bot_of_isL2Quot hfr.hf
    (t.isL2Quot_Lv hfr (Int.not_even_iff_odd.mp hodd)) hLZ hZc hZ2 hcard hirr

private theorem r8four_commutator_mem_Qv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ)
    (hlt : (t.Zv v).relIndex (t.Qv v) <
      if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2)
    {g : G} (hg : g ∈ t.Lv v) (hodd : Odd (orderOf g)) :
    ∀ x ∈ t.Qv v, ⁅g, x⁆ ∈ t.Zv v :=
  t.commutator_mem_of_odd_of_relIndex_lt hfr v (t.Zv_le_Qv v) le_rfl
    ((t.Lv_le_Gv v).trans (t.Gv_le_normalizer_Qv v))
    ((t.Lv_le_Gv v).trans (t.Gv_le_normalizer_Zv v)) hlt hg hodd

private theorem r8four_Qv_add_one_eq_Zv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {w : G} (hwL : w ∈ t.Lv (ε + 1))
    (hodd : Odd (orderOf w))
    (hcomm : ∀ x ∈ t.Qv (ε + 1), ⁅w, x⁆ ∈ t.Zv (ε + 1))
    (hfix : t.Zv (ε + 1) ⊓ centralizer ({w} : Set G) = ⊥) :
    t.Qv (ε + 1) = t.Zv (ε + 1) := by
  refine CFSG.Quasithin.Stroth.eq_of_commutator_le_of_fixedPointFree
    (Q := t.Qv (ε + 1)) (Z := t.Zv (ε + 1)) (ω := w)
    (t.isPGroup_Qv (ε + 1)) (t.Zv_le_Qv (ε + 1)) (t.Zv_le_centralizer (ε + 1)) ?_ ?_ ?_
  · intro z hzQ hzC hz2
    rw [t.Zv_eq (ε + 1)]
    exact Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hzQ, hzC⟩, hz2⟩
  · intro x hx
    have h := hcomm x hx
    have : ⁅x, w⁆ = (⁅w, x⁆)⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [this]
    exact (t.Zv (ε + 1)).inv_mem h
  · intro z hz hzw
    have hzC : z ∈ centralizer ({w} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hzw)
    have hmem : z ∈ t.Zv (ε + 1) ⊓ centralizer ({w} : Set G) := ⟨hz, hzC⟩
    rw [hfix] at hmem
    exact Subgroup.mem_bot.mp hmem

private theorem r8four_card_Qv_eps {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} (hε : Even ε) (hf : f = 2 * (2 * a + 1))
    (hcard : Nat.card (t.Zv (ε + 1)) = (2 ^ f) ^ 2)
    (hPle : Nat.card (pCoreOf 2 (t.Gw ε (ε + 1))) ≤
      (2 ^ (2 * a + 1)) ^ 4 * (2 ^ f) ^ 2)
    (hQeqZ : t.Qv (ε + 1) = t.Zv (ε + 1)) :
    Nat.card (t.Qv ε) = (2 ^ (2 * a + 1)) ^ 4 := by
  set P : Subgroup G := pCoreOf 2 (t.Gw ε (ε + 1)) with hP
  have hodd : ¬ Even (ε + 1) := by rw [Int.even_add_one]; exact not_not.mpr hε
  have hQPadd : t.Qv (ε + 1) ≤ P := by
    rw [hP]
    refine t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Qv (ε + 1)) ?_
    intro x hx
    refine mem_win_iff.mpr fun i hi1 hi2 => ?_
    rcases (show i = ε ∨ i = ε + 1 by omega) with h | h
    · rw [h]
      simpa only [show (ε : ℤ) + 1 - 1 = ε by ring] using
        (t.Qv_le_Gv hfr (ε + 1)).1 hx
    · rw [h]; exact t.Qv_le_Gv_self (ε + 1) hx
  have hrelAdd : (t.Qv (ε + 1)).relIndex P = 2 ^ f := by
    rw [hP]
    have h := (t.relIndex_Qv_pCoreOf hfr (ε + 1)).1
    rw [show (ε : ℤ) + 1 - 1 = ε by ring, if_neg hodd] at h
    exact h
  have hcardPadd : Nat.card P = 2 ^ f * Nat.card (t.Qv (ε + 1)) := by
    have h := Subgroup.relIndex_mul_card (t.Qv (ε + 1)) P
    rw [inf_eq_left.mpr hQPadd, hrelAdd] at h
    exact h.symm
  have hQPε : t.Qv ε ≤ P := by
    rw [hP]
    refine t.le_pCoreOf_Gw hfr (by omega) (t.isPGroup_Qv ε) ?_
    intro x hx
    refine mem_win_iff.mpr fun i hi1 hi2 => ?_
    rcases (show i = ε ∨ i = ε + 1 by omega) with h | h
    · rw [h]; exact t.Qv_le_Gv_self ε hx
    · rw [h]; exact (t.Qv_le_Gv hfr ε).2 hx
  have hrelε : (t.Qv ε).relIndex P = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [hP]
    have h := (t.relIndex_Qv_pCoreOf hfr ε).2
    rwa [if_pos hε] at h
  have hcardPε : Nat.card P = (2 ^ (2 * a + 1)) ^ 2 * Nat.card (t.Qv ε) := by
    have h := Subgroup.relIndex_mul_card (t.Qv ε) P
    rw [inf_eq_left.mpr hQPε, hrelε] at h
    exact h.symm
  have hcardP : Nat.card P = 2 ^ f * (2 ^ f) ^ 2 := by
    rw [hcardPadd, hQeqZ, hcard]
  have hrq : 2 ^ f = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [hf]
    calc 2 ^ (2 * (2 * a + 1)) = 2 ^ ((2 * a + 1) * 2) :=
          congrArg (fun e => 2 ^ e) (by ring)
      _ = (2 ^ (2 * a + 1)) ^ 2 := pow_mul 2 (2 * a + 1) 2
  have heq : (2 ^ (2 * a + 1)) ^ 2 * Nat.card (t.Qv ε) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1)) ^ 4 := by
    rw [← hcardPε, hcardP, hrq]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) heq

private theorem r8four_false_of_odd_elt {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} (hC : t.Lv ε ≤ centralizer (t.Zv ε : Set G))
    {d : G} (hdK : d ∈ t.K) (hdL : d ∈ t.Lv ε) (hd1 : d ≠ 1)
    (hodd : Odd (orderOf d))
    (hcomm : ∀ x ∈ t.Qv ε, ⁅d, x⁆ ∈ t.Zv ε) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : (orderOf d).Coprime 2 := hodd.coprime_two_right
  have hcent : d ∈ centralizer (t.Qv ε : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hmem : d * x * d⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) :=
      CFSG.GroupTheory.CoprimeActionSupport.commutator_mem_of_coprime_of_commutator_mem
        (p := 2) (P := t.Qv ε) (W := t.Zv ε) (Z := ⊥)
        (t.isPGroup_Zv ε)
        (fun w _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top w)
        hcop (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top d)
        (fun x hx => by simpa [commutatorElement_def] using hcomm x hx)
        (fun w hw => by
          rw [Subgroup.mem_bot]
          change ⁅d, w⁆ = 1
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (Subgroup.mem_centralizer_iff.mp (hC hdL) w hw).symm) x hx
    have h1 : ⁅d, x⁆ = 1 := by simpa [commutatorElement_def] using Subgroup.mem_bot.mp hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hdQ : d ∈ t.Qv ε :=
    t.Gv_inf_centralizer_le_Qv hfr ε ⟨(t.K_le_Gv ε) hdK, hcent⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp (t.isPGroup_Qv ε) ⟨d, hdQ⟩
  have hdvd : orderOf d ∣ 2 ^ n := by
    rw [Subgroup.orderOf_mk d hdQ] at hn
    exact orderOf_dvd_of_pow_eq_one (by rw [← hn]; exact pow_orderOf_eq_one d)
  have hcopn : (orderOf d).Coprime (2 ^ n) := hcop.pow_right n
  have hone : orderOf d = 1 := Nat.eq_one_of_dvd_coprimes hcopn dvd_rfl hdvd
  exact hd1 (orderOf_eq_one_iff.mp hone)

theorem IsMaxArc.false_of_four
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} (h : t.IsMaxArc ε 4) (hε : Even ε)
    (hf : f = 2 * (2 * a + 1)) (hC : t.Lv ε ≤ centralizer (t.Zv ε : Set G))
    (hZ : t.Zv ε ≤ t.Zv (ε + 1)) (hcard : Nat.card (t.Zv (ε + 1)) = (2 ^ f) ^ 2) : False := by
  have hcardZv : Nat.card (t.Zv ε) = 2 ^ (2 * a + 1) :=
    r8four_card_Zv t hfr h hε hZ
  have hPle : Nat.card (pCoreOf 2 (t.Gw ε (ε + 1))) ≤
      (2 ^ (2 * a + 1)) ^ 4 * (2 ^ f) ^ 2 := r8four_card_pCoreOf_le t hfr h hε
  have hltAddOne := r8four_relIndex_Zv_Qv_add_one t hfr hε hf hcard hPle
  obtain ⟨w, hwL, hwodd, hwfix⟩ := r8four_exists_fixedPointFree t hfr h hε hf hC hZ hcard
  have hodd : ¬ Even (ε + 1) := by rw [Int.even_add_one]; exact not_not.mpr hε
  have hcommW : ∀ x ∈ t.Qv (ε + 1), ⁅w, x⁆ ∈ t.Zv (ε + 1) :=
    r8four_commutator_mem_Qv t hfr (ε + 1) (by rw [if_neg hodd]; exact hltAddOne) hwL hwodd
  have hQeqZ : t.Qv (ε + 1) = t.Zv (ε + 1) :=
    r8four_Qv_add_one_eq_Zv t hfr hwL hwodd hcommW hwfix
  have hQvE := r8four_card_Qv_eps t hfr hε hf hcard hPle hQeqZ
  have hrelZeq : (t.Zv ε).relIndex (t.Qv ε) * 2 ^ (2 * a + 1) = (2 ^ (2 * a + 1)) ^ 4 := by
    have h := Subgroup.relIndex_mul_card (t.Zv ε) (t.Qv ε)
    rw [inf_eq_left.mpr (t.Zv_le_Qv ε), hcardZv, hQvE] at h
    exact h
  have hrelZ : (t.Zv ε).relIndex (t.Qv ε) = (2 ^ (2 * a + 1)) ^ 3 := by
    have hmul : 2 ^ (2 * a + 1) * (t.Zv ε).relIndex (t.Qv ε) =
        2 ^ (2 * a + 1) * (2 ^ (2 * a + 1)) ^ 3 := by
      rw [mul_comm (2 ^ (2 * a + 1)) ((t.Zv ε).relIndex (t.Qv ε)), hrelZeq]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (2 * a + 1)) hmul
  have hltε : (t.Zv ε).relIndex (t.Qv ε) <
      if Even ε then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2 := by
    rw [if_pos hε, hrelZ]
    have hq1 : 1 < 2 ^ (2 * a + 1) := by
      have ha1 : 1 ≤ a := hfr.ha
      have h1 : 1 < 2 * a + 1 := by omega
      have := Nat.pow_lt_pow_right (show 1 < (2 : ℕ) by norm_num) h1
      simpa using this
    exact Nat.pow_lt_pow_right hq1 (by norm_num)
  obtain ⟨⟨d, hdmem⟩, hd1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (t.K_inf_Lv_ne_bot hfr ε)
  have hdK : d ∈ t.K := hdmem.1
  have hdL : d ∈ t.Lv ε := hdmem.2
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hodd_d : Odd (orderOf d) :=
    Odd.of_dvd_nat t.hHall.2.1 (t.K.orderOf_dvd_natCard hdK)
  have hcommd : ∀ x ∈ t.Qv ε, ⁅d, x⁆ ∈ t.Zv ε :=
    r8four_commutator_mem_Qv t hfr ε hltε hdL hodd_d
  exact r8four_false_of_odd_elt t hfr hC hdK hdL hd1' hodd_d hcommd

end Track

end CFSG.Quasithin.Stroth.Rq
