module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86OrbitTreeDef

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type*} {Γ : SimpleGraph V} {A : Set V}

noncomputable def commonNbr (Γ : SimpleGraph V) (A : Set V) (a b : ↥A) : V :=
  @Classical.epsilon V ⟨a.1⟩ (fun w => Γ.Adj a.1 w ∧ Γ.Adj b.1 w)

theorem commonNbr_spec {a b : ↥A} (h : (orbitGraph Γ A).Adj a b) :
    Γ.Adj a.1 (commonNbr Γ A a b) ∧ Γ.Adj b.1 (commonNbr Γ A a b) :=
  Classical.epsilon_spec (p := fun w => Γ.Adj a.1 w ∧ Γ.Adj b.1 w) h.2

noncomputable def liftVert (Γ : SimpleGraph V) (A : Set V) (Q : ℕ → ↥A) (j : ℕ) : V :=
  if j % 2 = 0 then (Q (j / 2)).1 else commonNbr Γ A (Q (j / 2)) (Q (j / 2 + 1))

theorem liftVert_even (Q : ℕ → ↥A) (i : ℕ) : liftVert Γ A Q (2 * i) = (Q i).1 := by
  have h1 : (2 * i) % 2 = 0 := by omega
  have h2 : (2 * i) / 2 = i := by omega
  simp [liftVert, h1, h2]

theorem liftVert_odd (Q : ℕ → ↥A) (i : ℕ) :
    liftVert Γ A Q (2 * i + 1) = commonNbr Γ A (Q i) (Q (i + 1)) := by
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [liftVert, h2]

noncomputable def OrbitPartner.liftArc (hP : OrbitPartner Γ A) {n : ℕ}
    (Q : Arc (orbitGraph Γ A) n) : Arc Γ (2 * n) where
  vert := liftVert Γ A Q.vert
  adj j hj := by
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [liftVert_even, liftVert_odd]
      exact (commonNbr_spec (Q.adj i (by omega))).1
    · rw [liftVert_odd, show 2 * i + 1 + 1 = 2 * (i + 1) by omega, liftVert_even]
      exact (commonNbr_spec (Q.adj i (by omega))).2.symm
  nb j hj := by
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [show 2 * i + 2 = 2 * (i + 1) by omega, liftVert_even, liftVert_even]
      exact (Q.adj i (by omega)).1
    · rw [show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by omega, liftVert_odd, liftVert_odd]
      intro e
      have h1 := commonNbr_spec (Q.adj i (by omega))
      have h2 := commonNbr_spec (Q.adj (i + 1) (by omega))
      have e1 : (Q.vert i).1 ∈ A ∧ (Q.vert i).1 ≠ (Q.vert (i + 1)).1 ∧
          Γ.Adj (Q.vert i).1 (commonNbr Γ A (Q.vert i) (Q.vert (i + 1))) :=
        ⟨(Q.vert i).2, (Q.adj i (by omega)).1, h1.1⟩
      have e2 : (Q.vert (i + 1 + 1)).1 ∈ A ∧ (Q.vert (i + 1 + 1)).1 ≠ (Q.vert (i + 1)).1 ∧
          Γ.Adj (Q.vert (i + 1 + 1)).1 (commonNbr Γ A (Q.vert i) (Q.vert (i + 1))) :=
        ⟨(Q.vert (i + 1 + 1)).2, (Q.adj (i + 1) (by omega)).1.symm, by rw [e]; exact h2.2⟩
      have hu := hP (Q.vert (i + 1)).1 (Q.vert (i + 1)).2 _ h1.2
      exact Q.nb i (by omega) (Subtype.ext (hu.unique e1 e2))

theorem OrbitPartner.liftArc_vert_even (hP : OrbitPartner Γ A) {n : ℕ} (Q : Arc (orbitGraph Γ A) n)
    (i : ℕ) : (hP.liftArc Q).vert (2 * i) = (Q.vert i).1 :=
  liftVert_even Q.vert i

def Arc.toOrbit (hT : Γ.IsTree) {k : ℕ} (P : Arc Γ (2 * k))
    (hmem : ∀ i, i ≤ k → P.vert (2 * i) ∈ A) : Arc (orbitGraph Γ A) k where
  vert i := ⟨P.vert (2 * min i k), hmem _ (min_le_right i k)⟩
  adj i hi := by
    have e0 : min i k = i := Nat.min_eq_left (by omega)
    have e1 : min (i + 1) k = i + 1 := Nat.min_eq_left (by omega)
    refine ⟨?_, P.vert (2 * i + 1), ?_, ?_⟩
    · show P.vert (2 * min i k) ≠ P.vert (2 * min (i + 1) k)
      rw [e0, e1, show 2 * (i + 1) = 2 * i + 2 by omega]
      exact P.nb (2 * i) (by omega)
    · show Γ.Adj (P.vert (2 * min i k)) (P.vert (2 * i + 1))
      rw [e0]
      exact P.adj (2 * i) (by omega)
    · show Γ.Adj (P.vert (2 * min (i + 1) k)) (P.vert (2 * i + 1))
      rw [e1, show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
      exact (P.adj (2 * i + 1) (by omega)).symm
  nb i hi e := by
    have e0 : min i k = i := Nat.min_eq_left (by omega)
    have e1 : min (i + 2) k = i + 2 := Nat.min_eq_left (by omega)
    have h : P.vert (2 * min i k) = P.vert (2 * min (i + 2) k) := congrArg Subtype.val e
    rw [e0, e1] at h
    have := Arc.vert_injOn hT P (by omega) (by omega) h
    omega

theorem Arc.toOrbit_vert (hT : Γ.IsTree) {k : ℕ} (P : Arc Γ (2 * k))
    (hmem : ∀ i, i ≤ k → P.vert (2 * i) ∈ A) {i : ℕ} (hi : i ≤ k) :
    ((Arc.toOrbit hT P hmem).vert i).1 = P.vert (2 * i) := by
  show P.vert (2 * min i k) = _
  rw [Nat.min_eq_left hi]

end CFSG.Quasithin.Fan86
