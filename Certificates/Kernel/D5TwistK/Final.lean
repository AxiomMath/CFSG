module

public import CFSG.Certificates.Kernel.D5TwistKSound
import CFSG.Certificates.Kernel.D5TwistFSound
import Certificates.Kernel.D5TwistK.ChecksF
import Certificates.Kernel.D5TwistK.BF0
import Certificates.Kernel.D5TwistK.BF1
import Certificates.Kernel.D5TwistK.BF2

public section

namespace Certificates.D5TwistK

open Certificates.D5Twist

theorem lfacts_wj : LFacts ∧
    ∀ b ∈ [0, 2, 3], wjGens b = (wjGensK b).map (decN 25) ∧ ∀ x ∈ wjGensK b, x < 4 ^ 25 := by
  have h := ch712503L_ok
  unfold ch712503L at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, h6⟩, h7⟩, _⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨⟨h1, h2, fun x hx => by simpa using h3 x hx, h4, by decide, h6, h7, by decide, h9, h10,
    fun z hz => (h11 z hz).1.1, fun z hz => (h11 z hz).1.2,
    fun z hz v hv => by simpa using (h11 z hz).2 v hv⟩, fun b hb => ⟨(h12 b hb).1, ?_⟩⟩
  intro x hx
  simpa using (h12 b hb).2 x hx

theorem pairs_b : ∀ b r, (b, r) ∈ pairsK → b ∈ [0, 2, 3] := by
  have h : ∀ p ∈ pairsK, p.1 ∈ [0, 2, 3] := by decide
  exact fun b r hp => h (b, r) hp

theorem pairs_ok : ∀ b r, (b, r) ∈ pairsK → BK b r = true := by
  have keyF : ∀ i, i < 12 → ch712503BF i = true := by
    intro i hi
    match i, hi with
    | 0, _ => exact ch712503BF0
    | 1, _ => exact ch712503BF1
    | 2, _ => exact ch712503BF2
    | 3, _ => exact ch712503BF3
    | 4, _ => exact ch712503BF4
    | 5, _ => exact ch712503BF5
    | 6, _ => exact ch712503BF6
    | 7, _ => exact ch712503BF7
    | 8, _ => exact ch712503BF8
    | 9, _ => exact ch712503BF9
    | 10, _ => exact ch712503BF10
    | 11, _ => exact ch712503BF11
    | n + 12, h => exact absurd h (by omega)
  have key : ∀ i, i < 12 → ch712503B i = true := fun i hi => by
    rw [← ch712503BF_eq]
    exact keyF i hi
  intro b r hp
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hp
  have hl : pairsK.length = 12 := rfl
  have h := key i (by omega)
  unfold ch712503B at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he] at h
  exact h

theorem check_true : check () = true := by
  have hS : ch712503S () = true := by
    rw [← ch712503SF_eq]
    exact ch712503SF_ok
  have hA : ch712503A () = true := by
    rw [← ch712503AF_eq]
    exact ch712503AF_ok
  exact check_of_twin lfacts_wj.1 hS hA lfacts_wj.2 pairs_b pairs_ok

end Certificates.D5TwistK

end
