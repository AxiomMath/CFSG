module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoBase
public import Mathlib.Algebra.Group.Action.Basic

public section

namespace CFSG.Quasithin.Fan86.Tutte.Geo

open CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.Tutte.Red

variable {W : Type} {Γ : SimpleGraph W} {H : Type} [Group H] [MulAction H W] {s : ℕ}

namespace RegData

variable (R : RegData Γ H s)

include R

theorem trans_le {n : ℕ} (hn : n ≤ s) (P Q : Arc Γ n) :
    ∃ h : H, ∀ i, i ≤ n → h • P.vert i = Q.vert i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨P', hP'⟩ := exists_extend R.card3 P d
  obtain ⟨Q', hQ'⟩ := exists_extend R.card3 Q d
  obtain ⟨h, hh⟩ := R.trans P' Q'
  exact ⟨h, fun i hi => by rw [← hP' i hi, ← hQ' i hi]; exact hh i (by omega)⟩

theorem ext_trans {n : ℕ} (hn : n < s) (P : Arc Γ n) {w₁ w₂ : W} (h₁ : w₁ ∈ extSet P)
    (h₂ : w₂ ∈ extSet P) :
    ∃ h : H, (∀ i, i ≤ n → h • P.vert i = P.vert i) ∧ h • w₁ = w₂ := by
  obtain ⟨h, hh⟩ := R.trans_le (n := n + 1) (by omega) (snocArc P w₁ h₁.1 h₁.2)
    (snocArc P w₂ h₂.1 h₂.2)
  refine ⟨h, fun i hi => ?_, ?_⟩
  · have := hh i (by omega)
    rwa [snocArc_vert_le _ _ _ _ hi, snocArc_vert_le _ _ _ _ hi] at this
  · have := hh (n + 1) le_rfl
    rwa [snocArc_vert_last, snocArc_vert_last] at this

theorem smul_mem_extSet {n : ℕ} (P : Arc Γ n) {h : H} (hfix : ∀ i, i ≤ n → h • P.vert i = P.vert i)
    {w : W} (hw : w ∈ extSet P) : h • w ∈ extSet P := by
  refine ⟨?_, fun hn1 hcontra => ?_⟩
  · have := (R.adj h _ _).2 hw.1
    rwa [hfix n le_rfl] at this
  · apply hw.2 hn1
    apply MulAction.injective h
    show h • w = h • P.vert (n - 1)
    rw [hcontra, hfix (n - 1) (by omega)]

end RegData

theorem extSet_ncard_zero (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3) (P : Arc Γ 0) :
    (extSet P).ncard = 3 := by
  have : extSet P = Γ.neighborSet (P.vert 0) := by
    ext w
    simp [extSet, SimpleGraph.mem_neighborSet]
  rw [this, ← Nat.card_coe_set_eq, hcard]

theorem extSet_ncard_succ (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3) {n : ℕ}
    (P : Arc Γ (n + 1)) : (extSet P).ncard = 2 := by
  have hmem : P.vert n ∈ Γ.neighborSet (P.vert (n + 1)) := by
    exact (P.adj n (by omega)).symm
  have : extSet P = Γ.neighborSet (P.vert (n + 1)) \ {P.vert n} := by
    ext w
    simp [extSet, SimpleGraph.mem_neighborSet]
  have hn : (Γ.neighborSet (P.vert (n + 1))).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard _
  rw [this, Set.ncard_sdiff_singleton_of_mem hmem, hn]

theorem extSet_ncard (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3) {n : ℕ} (P : Arc Γ n) :
    (extSet P).ncard = if n = 0 then 3 else 2 := by
  cases n with
  | zero => simpa using extSet_ncard_zero hcard P
  | succ n => simpa using extSet_ncard_succ hcard P

end CFSG.Quasithin.Fan86.Tutte.Geo
