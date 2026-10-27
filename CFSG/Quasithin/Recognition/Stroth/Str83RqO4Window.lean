module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Goldschmidt

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Frame
import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
import CFSG.Quasithin.Recognition.Stroth.Str83RqRoot

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem GT_map_tau_pow_le (k : ℤ) :
    (t.GT).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom ≤ t.GT := by
  rintro y ⟨x, hx, rfl⟩
  change (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom x ∈ ⨅ j : ℤ, t.Gv j
  rw [Subgroup.mem_iInf]
  intro j
  have h := Subgroup.mem_map_of_mem (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom
    (t.GT_le_Gv (j - 2 * k) hx)
  rw [show t.Gv (j - 2 * k) =
      win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (j - 2 * k) (j - 2 * k) from
    (win_self (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) (x₁ := t.x₁) (x₂ := t.x₂)
      (j - 2 * k)).symm] at h
  rw [map_win_tau_pow] at h
  simpa [win_self, sub_add_cancel] using h

private theorem exists_sym_window :
    ∃ N : ℕ, t.Gw (-(N : ℤ)) (N : ℤ) = t.GT := by
  classical
  let H : ℕ → Subgroup G := fun n => t.Gw (-(n : ℤ)) (n : ℤ)
  let c : ℕ → ℕ := fun n => Nat.card (H n)
  have hP : ∃ k : ℕ, ∃ n : ℕ, c n = k := ⟨c 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hP
  refine ⟨N, le_antisymm ?_ (t.GT_le_Gw _ _)⟩
  by_contra hnot
  have hnotall : ¬ ∀ i : ℤ, H N ≤ t.Gv i := fun h => hnot (le_iInf h)
  push Not at hnotall
  obtain ⟨i, hi⟩ := hnotall
  let n : ℕ := max N i.natAbs
  have hHN : H n ≤ H N := by
    show win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (-(n : ℤ)) (n : ℤ) ≤
      win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (-(N : ℤ)) (N : ℤ)
    refine win_mono ?_ ?_ <;> simp only [n] <;> omega
  have hHnGv : H n ≤ t.Gv i := by
    have hnge : (i.natAbs : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast Nat.le_max_right N i.natAbs
    have hneg : -(n : ℤ) ≤ i := by
      have h1 : -(n : ℤ) ≤ -(i.natAbs : ℤ) := by omega
      have h2 : -i ≤ (i.natAbs : ℤ) := by
        have h := (Int.le_natAbs (a := -i))
        rwa [Int.natAbs_neg] at h
      omega
    have hpos : i ≤ (n : ℤ) := (Int.le_natAbs (a := i)).trans hnge
    exact win_le_qv hneg hpos
  have hcard : Nat.card (H N) ≤ Nat.card (H n) := by
    have hm : Nat.find hP ≤ c n := Nat.find_min' hP ⟨n, rfl⟩
    exact hN.le.trans hm
  have heq : H n = H N := Subgroup.eq_of_le_of_card_ge hHN hcard
  rw [heq] at hHnGv
  exact hi hHnGv

private theorem Gw_zero_one_ne_GT {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Gw 0 1 ≠ t.GT := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : S = t.QT :=
    (t.pCoreOf_Gw_zero_one hfr).symm.trans (by rw [h])
  have hB : bigB L1 L2 S = t.Gv 0 ⊓ t.Gv 1 := by
    rw [← t.Gw_zero_one hfr.hF]
    simpa using t.Gw_add_one 0
  have hleB : t.Qv 1 ≤ bigB L1 L2 S := by
    rw [hB]
    exact le_inf (by simpa using (t.Qv_le_Gv hfr 1).1) (t.Qv_le_Gv_self 1)
  have hnormB : bigB L1 L2 S ≤ normalizer (t.Qv 1 : Set G) :=
    (hB.le.trans inf_le_right).trans (t.Gv_le_normalizer_Qv 1)
  have hBcore : pCoreOf 2 (bigB L1 L2 S) = S := by
    rw [← t.Gw_zero_one hfr.hF]
    exact t.pCoreOf_Gw_zero_one hfr
  have hQv1S : t.Qv 1 ≤ S :=
    (le_pCoreOf_of_le_normalizer 2 hleB hnormB (t.isPGroup_Qv 1)).trans hBcore.le
  have hSle : S ≤ t.Qv 0 := hS.le.trans (t.pCoreOf_GT_le_Qv hfr 0)
  exact t.Qv_one_not_le_Qv_zero hfr (hQv1S.trans hSle)

private theorem exists_window {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    ∃ n : ℕ, 2 ≤ n ∧ t.Gw 0 (n : ℤ) = t.GT ∧
      t.Gw 0 ((n : ℤ) - 1) ≠ t.GT := by
  classical
  obtain ⟨N, hN⟩ := exists_sym_window t
  have hshift : t.Gw ((N : ℤ) + 2) (3 * (N : ℤ) + 2) = t.GT := by
    have hmap := map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      (x₁ := t.x₁) (x₂ := t.x₂) (-(N : ℤ)) (N : ℤ) ((N : ℤ) + 1)
    change (t.Gw (-(N : ℤ)) (N : ℤ)).map
      (MulAut.conj ((t.x₂ * t.x₁) ^ ((N : ℤ) + 1))).toMonoidHom = _ at hmap
    rw [hN] at hmap
    rw [show -(N : ℤ) + 2 * ((N : ℤ) + 1) = (N : ℤ) + 2 by ring,
      show (N : ℤ) + 2 * ((N : ℤ) + 1) = 3 * (N : ℤ) + 2 by ring] at hmap
    change win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ ((N : ℤ) + 2) (3 * (N : ℤ) + 2) = t.GT
    have hle := GT_map_tau_pow_le t ((N : ℤ) + 1)
    have hcard : Nat.card (t.GT.map (MulAut.conj ((t.x₂ * t.x₁) ^ ((N : ℤ) + 1))).toMonoidHom)
        = Nat.card t.GT :=
      Subgroup.card_map_of_injective (MulAut.conj _).injective
    have heq : t.GT.map (MulAut.conj ((t.x₂ * t.x₁) ^ ((N : ℤ) + 1))).toMonoidHom = t.GT :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    rw [heq] at hmap
    exact hmap.symm
  have hGw : t.Gw 0 ((3 * N + 2 : ℕ) : ℤ) = t.GT := by
    have hle : t.Gw 0 ((3 * N + 2 : ℕ) : ℤ) ≤ t.Gw ((N : ℤ) + 2) (3 * (N : ℤ) + 2) := by
      refine win_mono ?_ ?_ <;> push_cast <;> omega
    exact le_antisymm (hle.trans hshift.le) (t.GT_le_Gw _ _)
  let P : ℕ → Prop := fun n => 2 ≤ n ∧ t.Gw 0 (n : ℤ) = t.GT
  have hPex : ∃ n, P n := ⟨3 * N + 2, by omega, hGw⟩
  have hnP : P (Nat.find hPex) := Nat.find_spec hPex
  refine ⟨Nat.find hPex, hnP.1, hnP.2, ?_⟩
  intro hW
  rcases (show Nat.find hPex = 2 ∨ 3 ≤ Nat.find hPex by omega) with h2 | h3
  · rw [h2] at hW
    norm_num at hW
    exact Gw_zero_one_ne_GT t hfr hW
  · have hcast : (((Nat.find hPex - 1 : ℕ) : ℤ)) = (Nat.find hPex : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Nat.find hPex)]
      norm_num
    have hP' : P (Nat.find hPex - 1) := ⟨by omega, by rwa [hcast]⟩
    exact Nat.find_min hPex (by omega) hP'

private theorem map_Gv_tau_pow (i k : ℤ) :
    (t.Gv i).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = t.Gv (i + 2 * k) := by
  have h := map_win_tau_pow (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
    (x₁ := t.x₁) (x₂ := t.x₂) i i k
  simpa [win_self] using h

private theorem window_GT_eq_inf_sup_K {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : 0 < v) :
    t.GT = (pCoreOf 2 (t.Gw 0 v) ⊓ t.GT) ⊔ t.K := by
  have hW : t.Gw 0 v = pCoreOf 2 (t.Gw 0 v) ⊔ t.K := t.Gw_eq_sup hfr hv
  have hKP : t.K ≤ normalizer (pCoreOf 2 (t.Gw 0 v) : Set G) :=
    (t.K_le_Gw 0 v).trans (le_normalizer_pCoreOf 2 _)
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_right (t.K_le_GT))
  have hxW : x ∈ t.Gw 0 v := (t.GT_le_Gw 0 v) hx
  rw [hW] at hxW
  obtain ⟨p, hp, k, hk, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hKP).mp hxW
  have hpGT : p ∈ t.GT := by
    have h := t.GT.mul_mem hx (t.GT.inv_mem (t.K_le_GT hk))
    simpa using h
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hp, hpGT⟩) hk

private theorem window_core_inf_GT {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : 0 < v) :
    pCoreOf 2 (t.Gw 0 v) ⊓ t.GT = t.QT := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := t.window_GT_eq_inf_sup_K hfr hv
  have hle : pCoreOf 2 (t.Gw 0 v) ⊓ t.GT ≤ t.QT := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
    · intro g hg
      refine Subgroup.inf_normalizer_le_normalizer_inf
        (H := pCoreOf 2 (t.Gw 0 v)) (K := t.GT) ⟨?_, Subgroup.le_normalizer hg⟩
      exact (t.GT_le_Gw 0 v).trans (le_normalizer_pCoreOf 2 (t.Gw 0 v)) hg
    · exact (pCoreOf_isPGroup 2 (t.Gw 0 v)).to_le inf_le_left
  refine le_antisymm hle ?_
  intro q hq
  have hqGT : q ∈ t.GT := pCoreOf_le 2 t.GT hq
  rw [hD] at hqGT
  have hKP : t.K ≤ normalizer ((pCoreOf 2 (t.Gw 0 v) ⊓ t.GT : Subgroup G) : Set G) := by
    intro k hk
    refine Subgroup.inf_normalizer_le_normalizer_inf
      (H := pCoreOf 2 (t.Gw 0 v)) (K := t.GT) ⟨?_, ?_⟩
    · exact (t.K_le_Gw 0 v).trans (le_normalizer_pCoreOf 2 (t.Gw 0 v)) hk
    · exact Subgroup.le_normalizer (t.K_le_GT hk)
  obtain ⟨p, hp, k, hk, hqpk⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hKP).mp hqGT
  have hpQ : p ∈ t.QT := hle hp
  have hkQ : k ∈ t.QT := by
    have hkeq : k = p⁻¹ * q := by rw [hqpk]; group
    rw [hkeq]
    exact t.QT.mul_mem (t.QT.inv_mem hpQ) hq
  have hk1 : k = 1 := by
    have hmem : k ∈ t.QT ⊓ t.K := ⟨hkQ, hk⟩
    rw [t.pCoreOf_GT_inf_K] at hmem
    simpa using hmem
  rw [hqpk, hk1, mul_one]
  exact hp

private theorem window_core_inf_Qv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : 1 ≤ v)
    (hGT : t.Gw 0 (v + 1) = t.GT) :
    pCoreOf 2 (t.Gw 0 v) ⊓ t.Qv v = t.QT := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 (pCoreOf 2 (t.Gw 0 v)) := pCoreOf_isPGroup 2 _
  have hPGw : pCoreOf 2 (t.Gw 0 v) ≤ t.Gw (v - 1) v := by
    refine (pCoreOf_le 2 (t.Gw 0 v)).trans (win_mono ?_ le_rfl)
    omega
  have h1 := (t.inf_Gv_eq_inf_Qv hfr v hP2).1 hPGw
  have hPGv : pCoreOf 2 (t.Gw 0 v) ⊓ t.Gv (v + 1) = t.QT := by
    calc pCoreOf 2 (t.Gw 0 v) ⊓ t.Gv (v + 1)
        = (pCoreOf 2 (t.Gw 0 v) ⊓ t.Gw 0 v) ⊓ t.Gv (v + 1) := by
          rw [inf_eq_left.mpr (pCoreOf_le 2 (t.Gw 0 v))]
      _ = pCoreOf 2 (t.Gw 0 v) ⊓ (t.Gw 0 v ⊓ t.Gv (v + 1)) := by rw [inf_assoc]
      _ = pCoreOf 2 (t.Gw 0 v) ⊓ t.Gw 0 (v + 1) := by
          rw [← win_add_one_right (a := 0) (b := v) (by omega)]
      _ = pCoreOf 2 (t.Gw 0 v) ⊓ t.GT := by rw [hGT]
      _ = t.QT := t.window_core_inf_GT hfr hv
  calc pCoreOf 2 (t.Gw 0 v) ⊓ t.Qv v
      = pCoreOf 2 (t.Gw 0 v) ⊓ t.Gv (v + 1) := h1.symm
    _ = t.QT := hPGv

private theorem window_core_normal {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : 0 < v)
    (hGT : t.Gw 0 (v + 1) = t.GT) :
    t.Gw 0 v ≤ normalizer (t.QT : Set G) := by
  have hQ := t.window_core_inf_Qv hfr (by omega) hGT
  intro w hw
  have h1 : w ∈ normalizer (pCoreOf 2 (t.Gw 0 v) : Set G) :=
    le_normalizer_pCoreOf 2 (t.Gw 0 v) hw
  have h2 : w ∈ normalizer (t.Qv v : Set G) :=
    (win_le_qv (by omega : (0 : ℤ) ≤ v) le_rfl hw :
      w ∈ t.Gv v) |> fun h => t.Gv_le_normalizer_Qv v h
  have h3 := Subgroup.inf_normalizer_le_normalizer_inf
    (H := pCoreOf 2 (t.Gw 0 v)) (K := t.Qv v) ⟨h1, h2⟩
  rwa [hQ] at h3

private theorem window_core_ne {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : 0 < v)
    (hWne : t.Gw 0 v ≠ t.GT) :
    pCoreOf 2 (t.Gw 0 v) ≠ t.QT := by
  intro h
  apply hWne
  rw [t.Gw_eq_sup hfr hv, h, ← t.GT_eq_pCoreOf_sup_K hfr]

private theorem K_le_normalizer_map_conj {P : Subgroup G} {y : G}
    (hKP : t.K ≤ normalizer (P : Set G)) (hyK : y ∈ normalizer (t.K : Set G)) :
    t.K ≤ normalizer ((P.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
  intro k hk
  have hyK' : y⁻¹ ∈ normalizer (t.K : Set G) :=
    Subgroup.inv_mem (H := normalizer (t.K : Set G)) hyK
  have hk' : y⁻¹ * k * y ∈ t.K := by
    have h := (Subgroup.mem_normalizer_iff.mp hyK' k).mp hk
    simpa using h
  have hk'inv : y⁻¹ * k⁻¹ * y ∈ t.K := by
    have h := (Subgroup.mem_normalizer_iff.mp hyK' k⁻¹).mp (t.K.inv_mem hk)
    simpa using h
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
    have h1 : y⁻¹ * k * y * q * (y⁻¹ * k * y)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hKP hk') q).mp hq
    refine Subgroup.mem_map.mpr ⟨y⁻¹ * k * y * q * (y⁻¹ * k * y)⁻¹, h1, ?_⟩
    show y * (y⁻¹ * k * y * q * (y⁻¹ * k * y)⁻¹) * y⁻¹ =
      k * (y * q * y⁻¹) * k⁻¹
    group
  · rintro ⟨q, hq, rfl⟩
    have hq' : y⁻¹ * k⁻¹ * y * q * (y⁻¹ * k⁻¹ * y)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hKP hk'inv) q).mp hq
    refine Subgroup.mem_map.mpr ⟨k⁻¹ * (y * q * y⁻¹) * k, ?_, ?_⟩
    · refine Subgroup.mem_map.mpr
        ⟨y⁻¹ * k⁻¹ * y * q * (y⁻¹ * k⁻¹ * y)⁻¹, hq', ?_⟩
      show y * (y⁻¹ * k⁻¹ * y * q * (y⁻¹ * k⁻¹ * y)⁻¹) * y⁻¹ =
        k⁻¹ * (y * q * y⁻¹) * k
      group
    · show k * (k⁻¹ * (y * q * y⁻¹) * k) * k⁻¹ = y * q * y⁻¹
      group

private theorem mem_normalizer_GT_of_reflection {v : ℤ} {y : G}
    (hyGv : ∀ i : ℤ, (t.Gv i).map (MulAut.conj y).toMonoidHom = t.Gv (2 * v - i)) :
    y ∈ normalizer (t.GT : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (t.GT).map (MulAut.conj y).toMonoidHom = t.GT
  have hmap : (t.GT).map (MulAut.conj y).toMonoidHom =
      ⨅ i : ℤ, (t.Gv i).map (MulAut.conj y).toMonoidHom :=
    Subgroup.map_iInf (MulAut.conj y).toMonoidHom (MulAut.conj y).injective (fun i => t.Gv i)
  rw [hmap]
  simp only [hyGv]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun j => ?_
    simpa [show 2 * v - (2 * v - j) = j by ring] using
      (iInf_le (fun i : ℤ => t.Gv (2 * v - i)) (2 * v - j))
  · refine le_iInf fun i => t.GT_le_Gv (2 * v - i)

private theorem map_Gv_of_win_reflection {v : ℤ} {y : G}
    (hwin : ∀ u w : ℤ,
      (t.Gw u w).map (MulAut.conj y).toMonoidHom = t.Gw (2 * v - w) (2 * v - u)) :
    ∀ i : ℤ, (t.Gv i).map (MulAut.conj y).toMonoidHom = t.Gv (2 * v - i) := by
  intro i
  have h := hwin i i
  simpa [win_self] using h

private theorem reflection_mem_normalizer_QT {v : ℤ} {y : G}
    (hyGv : ∀ i : ℤ, (t.Gv i).map (MulAut.conj y).toMonoidHom = t.Gv (2 * v - i)) :
    y ∈ normalizer (t.QT : Set G) :=
  normalizer_le_normalizer_pCoreOf 2 t.GT (t.mem_normalizer_GT_of_reflection hyGv)

private theorem reflection_mem_normalizer_Qv {v : ℤ} {y : G}
    (hQv : (t.Qv v).map (MulAut.conj y).toMonoidHom = t.Qv v) :
    y ∈ normalizer (t.Qv v : Set G) :=
  (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hQv

private theorem map_le_Gv_of_reflection {v : ℤ} {y : G} {P : Subgroup G}
    (hP : P ≤ t.Gv v) (hyGv : (t.Gv v).map (MulAut.conj y).toMonoidHom = t.Gv v) :
    P.map (MulAut.conj y).toMonoidHom ≤ t.Gv v := by
  have h := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hP
  rwa [hyGv] at h

private theorem map_le_Gw_of_reflection {v : ℤ} {y : G} {P : Subgroup G}
    (hP : P ≤ t.Gw 0 v)
    (hwin : (t.Gw 0 v).map (MulAut.conj y).toMonoidHom = t.Gw v (2 * v)) :
    P.map (MulAut.conj y).toMonoidHom ≤ t.Gw v (2 * v) := by
  have h := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hP
  rwa [hwin] at h

private theorem map_le_pCoreOf_of_reflection {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : 1 ≤ v) {y : G} {P Py : Subgroup G}
    (hP2 : IsPGroup 2 P) (hPy : Py = P.map (MulAut.conj y).toMonoidHom)
    (hPyW : Py ≤ t.Gw v (2 * v)) :
    Py ≤ pCoreOf 2 (t.Gw v (v + 1)) := by
  refine t.le_pCoreOf_Gw hfr (show v < v + 1 by omega) ?_ ?_
  · rw [hPy]
    exact hP2.map (MulAut.conj y).toMonoidHom
  · exact hPyW.trans (win_mono le_rfl (by omega))

private theorem not_le_Qv_of_reflection {v : ℤ} {y : G} {P Py : Subgroup G}
    (hPne : P ≠ t.QT) (hPQ : P ⊓ t.Qv v = t.QT)
    (hyQv : y ∈ normalizer (t.Qv v : Set G))
    (hPy : Py = P.map (MulAut.conj y).toMonoidHom) :
    ¬ Py ≤ t.Qv v := by
  intro hle
  apply hPne
  have hPle : P ≤ t.Qv v := by
    intro p hp
    have hmem : y * p * y⁻¹ ∈ Py := by
      rw [hPy]
      exact Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
    have h1 : y * p * y⁻¹ ∈ t.Qv v := hle hmem
    have hyQv' : y⁻¹ ∈ normalizer (t.Qv v : Set G) :=
      Subgroup.inv_mem (H := normalizer (t.Qv v : Set G)) hyQv
    have h2 := (Subgroup.mem_normalizer_iff.mp hyQv' (y * p * y⁻¹)).mp h1
    simpa [mul_assoc] using h2
  rw [← hPQ, inf_eq_left.mpr hPle]

private theorem map_le_MX_of_reflection {v : ℤ} {y : G} {P Py : Subgroup G}
    (hyQ : y ∈ normalizer (t.QT : Set G))
    (hPM : P ≤ normalizer (t.QT : Set G))
    (hPyGv : Py ≤ t.Gv v)
    (hPy : Py = P.map (MulAut.conj y).toMonoidHom) :
    Py ≤ t.MX t.QT v := by
  refine le_inf ?_ hPyGv
  intro z hz
  rw [hPy] at hz
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hz
  exact Subgroup.mul_mem (H := normalizer (t.QT : Set G))
    (Subgroup.mul_mem (H := normalizer (t.QT : Set G)) hyQ (hPM hp))
    (Subgroup.inv_mem (H := normalizer (t.QT : Set G)) hyQ)

private theorem root_hyp_right {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} {Py : Subgroup G}
    (hPyR : Py ≤ pCoreOf 2 (t.Gw v (v + 1)))
    (hKPy : t.K ≤ normalizer (Py : Set G)) (hPyne : ¬ Py ≤ t.Qv v)
    (hPyMX : Py ≤ t.MX t.QT v) :
    ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), x ^ 2 ∈ t.Qv v →
      x ∈ t.MX t.QT v ⊔ t.Qv v := by
  intro x hxR hxQ
  have hx := t.rootOmega_le_sup hfr v hPyR hKPy hPyne
    ((t.mem_rootOmega_iff hfr v).mpr ⟨hxR, hxQ⟩)
  exact (sup_le (hPyMX.trans le_sup_left) le_sup_right) hx

private theorem root_hyp_left {v : ℤ} {y : G}
    (hyv : y ∈ t.Gv v) (hyQ : y ∈ normalizer (t.QT : Set G))
    (hyQv : y ∈ normalizer (t.Qv v : Set G))
    (hwin : ∀ u w : ℤ,
      (t.Gw u w).map (MulAut.conj y).toMonoidHom = t.Gw (2 * v - w) (2 * v - u))
    (hroot1 : ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), x ^ 2 ∈ t.Qv v →
      x ∈ t.MX t.QT v ⊔ t.Qv v) :
    ∀ x ∈ pCoreOf 2 (t.Gw (v - 1) v), x ^ 2 ∈ t.Qv v →
      x ∈ t.MX t.QT v ⊔ t.Qv v := by
  intro x hxR hxQ
  have hmapR : (pCoreOf 2 (t.Gw v (v + 1))).map (MulAut.conj y).toMonoidHom
      = pCoreOf 2 (t.Gw (v - 1) v) := by
    have h := hwin v (v + 1)
    rw [show 2 * v - (v + 1) = v - 1 by ring,
      show 2 * v - v = v by ring] at h
    rw [← h, pCoreOf_map_mulEquiv]
  obtain ⟨r, hrR, hxr⟩ := Subgroup.mem_map.mp (hmapR.symm ▸ hxR)
  have hrQ : r ^ 2 ∈ t.Qv v := by
    have hxq : y * r ^ 2 * y⁻¹ ∈ t.Qv v := by
      have hEq : (y * r * y⁻¹) ^ 2 = y * r ^ 2 * y⁻¹ := by
        rw [pow_two, pow_two]
        group
      have hx2 : (y * r * y⁻¹) ^ 2 ∈ t.Qv v := by
        rw [show y * r * y⁻¹ = x from hxr]
        exact hxQ
      rwa [hEq] at hx2
    exact (Subgroup.mem_normalizer_iff.mp hyQv (r ^ 2)).mpr hxq
  have hrH : r ∈ t.MX t.QT v ⊔ t.Qv v := hroot1 r hrR hrQ
  have hyNX : y ∈ normalizer (t.MX t.QT v : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      (H := normalizer (t.QT : Set G)) (K := t.Gv v)
      ⟨Subgroup.le_normalizer hyQ, Subgroup.le_normalizer hyv⟩
  have hyX : y ∈ normalizer ((t.MX t.QT v ⊔ t.Qv v : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup
      (H := t.MX t.QT v) (K := t.Qv v) ⟨hyNX, hyQv⟩
  have hmem := (Subgroup.mem_normalizer_iff.mp hyX r).mp hrH
  simpa [← hxr] using hmem

private theorem cosetTrans_MX_of_roots
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (v : ℤ)
    (hroot1 : ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), x ^ 2 ∈ t.Qv v →
      x ∈ t.MX t.QT v ⊔ t.Qv v)
    (hroot2 : ∀ x ∈ pCoreOf 2 (t.Gw (v - 1) v), x ^ 2 ∈ t.Qv v →
      x ∈ t.MX t.QT v ⊔ t.Qv v) :
    CosetTrans (t.MX t.QT v) (t.Gv v) (t.Gv (v + 1)) := by
  intro g hg
  have hXv : t.MX t.QT v ≤ t.Gv v := inf_le_right
  obtain ⟨m, hm, s, hs, hgs⟩ := t.exists_mul_of_mem_Gv hfr v hXv hroot1 hroot2 hg
  refine ⟨m, Subgroup.mem_inf.mpr ⟨hm, hXv hm⟩, ?_⟩
  have hmul : m⁻¹ * (m * s) = s := by group
  rw [hgs, hmul]
  exact win_le_qv (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
    (x₁ := t.x₁) (x₂ := t.x₂) (a := v) (b := v + 1) (i := v + 1)
    (by omega) le_rfl hs

private theorem exists_transitive_edge
    {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    ∃ n : ℕ, 2 ≤ n ∧
      CosetTrans (normalizer (t.QT : Set G)) (t.Gv ((n : ℤ) - 1)) (t.Gv (n : ℤ)) := by
  classical
  obtain ⟨n, hn2, hGT, hWne⟩ := t.exists_window hfr
  let v : ℤ := (n : ℤ) - 1
  have hv1 : 1 ≤ v := by omega
  have hGTv : t.Gw 0 (v + 1) = t.GT := by
    have h : v + 1 = (n : ℤ) := by omega
    rwa [h]
  have hPQ : pCoreOf 2 (t.Gw 0 v) ⊓ t.Qv v = t.QT :=
    t.window_core_inf_Qv hfr hv1 hGTv
  have hWnorm : t.Gw 0 v ≤ normalizer (t.QT : Set G) :=
    t.window_core_normal hfr (by omega) hGTv
  have hPne : pCoreOf 2 (t.Gw 0 v) ≠ t.QT :=
    t.window_core_ne hfr (by omega) (by simpa [v] using hWne)
  obtain ⟨y, hyv, hyK, hwin, hQvmap, -⟩ := t.exists_reflection v
  have hyGv := t.map_Gv_of_win_reflection hwin
  have hyQ := t.reflection_mem_normalizer_QT hyGv
  have hyQv : y ∈ normalizer (t.Qv v : Set G) :=
    t.reflection_mem_normalizer_Qv (by
      have h := hQvmap v
      simpa [show 2 * v - v = v by ring] using h)
  let P := pCoreOf 2 (t.Gw 0 v)
  let Py := P.map (MulAut.conj y).toMonoidHom
  have hPyGv : Py ≤ t.Gv v :=
    t.map_le_Gv_of_reflection
      ((pCoreOf_le 2 (t.Gw 0 v)).trans (win_le_qv (by omega) le_rfl))
      (by simpa [show 2 * v - v = v by ring] using hyGv v)
  have hPyW : Py ≤ t.Gw v (2 * v) :=
    t.map_le_Gw_of_reflection (pCoreOf_le 2 (t.Gw 0 v))
      (by
        simpa [show 2 * v - v = v by ring, show 2 * v - 0 = 2 * v by ring]
          using hwin 0 v)
  have hPyR : Py ≤ pCoreOf 2 (t.Gw v (v + 1)) :=
    t.map_le_pCoreOf_of_reflection hfr hv1 (pCoreOf_isPGroup 2 (t.Gw 0 v)) rfl hPyW
  have hKP : t.K ≤ normalizer (P : Set G) :=
    (t.K_le_Gw 0 v).trans (le_normalizer_pCoreOf 2 (t.Gw 0 v))
  have hKPy : t.K ≤ normalizer (Py : Set G) := t.K_le_normalizer_map_conj hKP hyK
  have hPyne : ¬ Py ≤ t.Qv v := t.not_le_Qv_of_reflection hPne hPQ hyQv rfl
  have hPyMX : Py ≤ t.MX t.QT v :=
    t.map_le_MX_of_reflection hyQ ((pCoreOf_le 2 (t.Gw 0 v)).trans hWnorm) hPyGv rfl
  have hroot1 := t.root_hyp_right hfr hPyR hKPy hPyne hPyMX
  have hroot2 := t.root_hyp_left hyv hyQ hyQv hwin hroot1
  have htransX := t.cosetTrans_MX_of_roots hfr v hroot1 hroot2
  refine ⟨n, hn2, ?_⟩
  have htrans : CosetTrans (normalizer (t.QT : Set G)) (t.Gv v) (t.Gv (v + 1)) :=
    CosetTrans.mono htransX (inf_le_left : t.MX t.QT v ≤ normalizer (t.QT : Set G))
  simpa [v] using htrans

private theorem cosetTrans_map_conj_normalizer {A B : Subgroup G} {g : G}
    (hg : g ∈ normalizer (t.QT : Set G))
    (h : CosetTrans (normalizer (t.QT : Set G)) A B) :
    CosetTrans (normalizer (t.QT : Set G))
      (A.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom) := by
  have hM : (normalizer (t.QT : Set G)).map (MulAut.conj g).toMonoidHom =
      normalizer (t.QT : Set G) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer hg)
  have h' := h.map_conj g
  rwa [hM] at h'

private theorem cosetTrans_shift_tau {v k : ℤ}
    (h : CosetTrans (normalizer (t.QT : Set G)) (t.Gv v) (t.Gv (v + 1))) :
    CosetTrans (normalizer (t.QT : Set G)) (t.Gv (v + 2 * k)) (t.Gv (v + 1 + 2 * k)) := by
  have hτ : (t.x₂ * t.x₁) ^ k ∈ normalizer (t.QT : Set G) :=
    zpow_mem (Subgroup.mul_mem (H := normalizer (t.QT : Set G))
      t.x₂_mem_normalizer_pCoreOf_GT t.x₁_mem_normalizer_pCoreOf_GT) k
  have h' := cosetTrans_map_conj_normalizer t hτ h
  rw [map_Gv_tau_pow t v k, map_Gv_tau_pow t (v + 1) k] at h'
  exact h'

private theorem arcL_of_trans (hQ : t.QT ≠ ⊥)
    (htr₀ : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 1) (t.Gv 0))
    (htr₂ : CosetTrans (normalizer (t.QT : Set G)) (t.Gv (-1)) (t.Gv 0))
    (hpair : ∀ g ∈ t.MX t.QT 0,
      g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨ t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) :
    t.ArcL t.QT := by
  have hQleGT : t.QT ≤ t.GT := pCoreOf_le 2 t.GT
  refine ⟨hQ, ?_, t.K_le_normalizer_pCoreOf_GT, htr₀, htr₂, hpair, ?_⟩
  · exact le_inf (le_inf (hQleGT.trans (t.GT_le_Gv 1)) (hQleGT.trans (t.GT_le_Gv 0)))
      (hQleGT.trans (t.GT_le_Gv (-1)))
  · exact ⟨t.x₁, Subgroup.mem_inf.mpr
      ⟨t.x₁_mem_normalizer_pCoreOf_GT, t.x₁_mem_Gv_zero⟩, by
        show t.x₁⁻¹ * t.x₁ ∈ t.Gv 1 ⊓ t.Gv (-1)
        rw [inv_mul_cancel]
        exact Subgroup.one_mem _⟩

private theorem arcSz_of_trans (hQ : t.QT ≠ ⊥)
    (htr₀ : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 0) (t.Gv 1))
    (htr₂ : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 2) (t.Gv 1))
    (hpair : ∀ g ∈ t.MX t.QT 1,
      g ∈ t.Gv 0 ⊓ t.Gv 2 ∨ t.x₂⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 2) :
    t.ArcSz t.QT := by
  have hQleGT : t.QT ≤ t.GT := pCoreOf_le 2 t.GT
  refine ⟨hQ, ?_, t.K_le_normalizer_pCoreOf_GT, htr₀, htr₂, hpair, ?_⟩
  · exact le_inf (le_inf (hQleGT.trans (t.GT_le_Gv 0)) (hQleGT.trans (t.GT_le_Gv 1)))
      (hQleGT.trans (t.GT_le_Gv 2))
  · exact ⟨t.x₂, Subgroup.mem_inf.mpr
      ⟨t.x₂_mem_normalizer_pCoreOf_GT, t.x₂_mem_Gv_one⟩, by
        show t.x₂⁻¹ * t.x₂ ∈ t.Gv 0 ⊓ t.Gv 2
        rw [inv_mul_cancel]
        exact Subgroup.one_mem _⟩

private theorem arcSz_of_even_trans
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hQ : t.QT ≠ ⊥)
    (hL : (∀ g ∈ t.MX t.QT 1, g ∈ t.Gv 0 ⊓ t.Gv 2 ∨
      t.x₂⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 2) ∨ L2 ≤ t.MX t.QT 1 ⊔ t.Qv 1)
    (htr0 : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 0) (t.Gv 1)) :
    t.ArcSz t.QT := by
  have hQle01 : t.QT ≤ t.Gv 0 ⊓ t.Gv 1 :=
    le_inf ((pCoreOf_le 2 t.GT).trans (t.GT_le_Gv 0))
      ((pCoreOf_le 2 t.GT).trans (t.GT_le_Gv 1))
  rcases hL with hpair | hcover
  · have htr2 : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 2) (t.Gv 1) := by
      have h := cosetTrans_map_conj_normalizer t t.x₂_mem_normalizer_pCoreOf_GT htr0
      rw [t.map_Gv_x₂ 0, t.map_Gv_x₂ 1] at h
      simpa using h
    exact arcSz_of_trans (t := t) (hQ := hQ) (htr₀ := htr0) (htr₂ := htr2) (hpair := hpair)
  · exfalso
    have htr1 : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 1) (t.Gv 0) :=
      CosetTrans.mono (t.cosetTrans_one_of_le_sup hfr (H := t.MX t.QT 1) inf_le_right hcover)
        (inf_le_left : t.MX t.QT 1 ≤ normalizer (t.QT : Set G))
    exact hQ (t.eq_bot_of_cosetTrans hfr hQle01 htr0 htr1)

private theorem arcL_of_odd_trans
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hQ : t.QT ≠ ⊥)
    (hSz : (∀ g ∈ t.MX t.QT 0, g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
      t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨ L1 ≤ t.MX t.QT 0 ⊔ t.Qv 0)
    (htr1 : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 1) (t.Gv 2)) :
    t.ArcL t.QT := by
  have hQle01 : t.QT ≤ t.Gv 0 ⊓ t.Gv 1 :=
    le_inf ((pCoreOf_le 2 t.GT).trans (t.GT_le_Gv 0))
      ((pCoreOf_le 2 t.GT).trans (t.GT_le_Gv 1))
  have htr0 : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 1) (t.Gv 0) := by
    have h := cosetTrans_map_conj_normalizer t t.x₂_mem_normalizer_pCoreOf_GT htr1
    rw [t.map_Gv_x₂ 1, t.map_Gv_x₂ 2] at h
    simpa using h
  have htr2 : CosetTrans (normalizer (t.QT : Set G)) (t.Gv (-1)) (t.Gv 0) := by
    have h := cosetTrans_map_conj_normalizer t t.x₁_mem_normalizer_pCoreOf_GT htr0
    rw [t.map_Gv_x₁ 1, t.map_Gv_x₁ 0] at h
    simpa using h
  rcases hSz with hpair | hcover
  · exact arcL_of_trans (t := t) (hQ := hQ) (htr₀ := htr0) (htr₂ := htr2) (hpair := hpair)
  · exfalso
    have htr01 : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 0) (t.Gv 1) :=
      CosetTrans.mono (t.cosetTrans_zero_of_le_sup hfr (H := t.MX t.QT 0) inf_le_right hcover)
        (inf_le_left : t.MX t.QT 0 ≤ normalizer (t.QT : Set G))
    exact hQ (t.eq_bot_of_cosetTrans hfr hQle01 htr01 htr0)

theorem arcL_or_arcSz_QT {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.QT ≠ ⊥)
    (hSz : (∀ g ∈ t.MX t.QT 0, g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨ t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨
      L1 ≤ t.MX t.QT 0 ⊔ t.Qv 0)
    (hL : (∀ g ∈ t.MX t.QT 1, g ∈ t.Gv 0 ⊓ t.Gv 2 ∨ t.x₂⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 2) ∨
      L2 ≤ t.MX t.QT 1 ⊔ t.Qv 1) :
    t.ArcL t.QT ∨ t.ArcSz t.QT := by
  classical
  obtain ⟨n, hn2, htr⟩ := t.exists_transitive_edge hfr
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' ((n : ℤ) - 1)
  · have hnk : (n : ℤ) = 2 * k + 1 := by omega
    rw [hk, hnk] at htr
    have htr0 : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 0) (t.Gv 1) := by
      have h := cosetTrans_shift_tau t (v := 2 * k) (k := -k) htr
      rw [show 2 * k + 2 * (-k) = 0 by ring,
        show 2 * k + 1 + 2 * (-k) = 1 by ring] at h
      exact h
    exact Or.inr (arcSz_of_even_trans (t := t) hfr hQ hL htr0)
  · have hnk : (n : ℤ) = 2 * k + 2 := by omega
    rw [hk, hnk] at htr
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring] at htr
    have htr1 : CosetTrans (normalizer (t.QT : Set G)) (t.Gv 1) (t.Gv 2) := by
      have h := cosetTrans_shift_tau t (v := 2 * k + 1) (k := -k) htr
      rw [show 2 * k + 1 + 2 * (-k) = 1 by ring,
        show 2 * k + 1 + 1 + 2 * (-k) = 2 by ring] at h
      exact h
    exact Or.inl (arcL_of_odd_trans (t := t) hfr hQ hSz htr1)

end Track

end CFSG.Quasithin.Stroth.Rq

end
