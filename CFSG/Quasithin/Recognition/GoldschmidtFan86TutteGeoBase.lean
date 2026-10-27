module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteRedWalk
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteRedArc

public section

namespace CFSG.Quasithin.Fan86.Tutte.Geo

open CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.Tutte.Red

variable {W : Type} {Γ : SimpleGraph W}

structure RegData (Γ : SimpleGraph W) (H : Type) [Group H] [MulAction H W] (s : ℕ) : Prop where
  one_le : 1 ≤ s
  card3 : ∀ w, Nat.card (Γ.neighborSet w) = 3
  adj : ∀ (h : H) (u v : W), Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v
  trans : ∀ P Q : Arc Γ s, ∃ h : H, ∀ i, i ≤ s → h • P.vert i = Q.vert i
  faith : ∀ (P : Arc Γ s) (h : H), (∀ i, i ≤ s → h • P.vert i = P.vert i) → h = 1

@[expose] def truncTo {s : ℕ} (a : Arc Γ s) (m : ℕ) (hm : m ≤ s) : Arc Γ m where
  vert := a.vert
  adj i hi := a.adj i (by omega)
  nb i hi := a.nb i (by omega)

@[simp] theorem truncTo_vert {s : ℕ} (a : Arc Γ s) (m : ℕ) (hm : m ≤ s) :
    (truncTo a m hm).vert = a.vert := rfl

@[expose] def extSet {n : ℕ} (P : Arc Γ n) : Set W :=
  {w | Γ.Adj (P.vert n) w ∧ (1 ≤ n → w ≠ P.vert (n - 1))}

theorem exists_mem_extSet (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3) {n : ℕ} (P : Arc Γ n) :
    ∃ w, w ∈ extSet P := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : Nat.card (Γ.neighborSet (P.vert 0)) ≠ 0 := by rw [hcard]; omega
    obtain ⟨⟨⟨w, hw⟩⟩, -⟩ := Nat.card_ne_zero.mp h0
    exact ⟨w, hw, fun h => by omega⟩
  · have hadj : Γ.Adj (P.vert n) (P.vert (n - 1)) := by
      have := (P.adj (n - 1) (by omega)).symm
      rwa [show n - 1 + 1 = n by omega] at this
    obtain ⟨w, hw, hwne⟩ := exists_other (hcard _) hadj
    exact ⟨w, hw, fun _ => hwne⟩

theorem exists_extend (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3) {m : ℕ} (P : Arc Γ m) :
    ∀ d : ℕ, ∃ Q : Arc Γ (m + d), ∀ i, i ≤ m → Q.vert i = P.vert i
  | 0 => ⟨P, fun _ _ => rfl⟩
  | d + 1 => by
    obtain ⟨Q, hQ⟩ := exists_extend hcard P d
    obtain ⟨w, hw1, hw2⟩ := exists_mem_extSet hcard Q
    refine ⟨snocArc Q w hw1 hw2, fun i hi => ?_⟩
    have h1 : i ≤ m + d := by omega
    exact (snocArc_vert_le Q w hw1 hw2 h1).trans (hQ i hi)

end CFSG.Quasithin.Fan86.Tutte.Geo
