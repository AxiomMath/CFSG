module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.X1512

namespace Delta

abbrev Dsub (n : ℕ) : Type := {x : G6.PermMod n // ∑ i, Multiplicative.toAdd x i = 0}

private theorem perm_fix_three : ∀ σ : Equiv.Perm (Fin 3),
    (∀ u : Dsub 3, G6.permAct 3 σ u.1 = u.1) → σ = 1 := by
  decide +kernel

private theorem perm_fix_five : ∀ σ : Equiv.Perm (Fin 5),
    (∀ u : Dsub 5, G6.permAct 5 σ u.1 = u.1) → σ = 1 := by
  decide +kernel

private theorem allOnes_sq (n : ℕ) : G6.allOnes n * G6.allOnes n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  show (1 : ZMod 2) + 1 = 0
  decide +kernel

private theorem allOnes_notMem {n : ℕ} (h : n = 3 ∨ n = 5) : G6.allOnes n ∉ G6.coreMod n := by
  intro hmem
  have h' : ∑ i : Fin n, Multiplicative.toAdd (G6.allOnes n) i = 0 := hmem
  rcases h with rfl | rfl
  · revert h'; decide +kernel
  · revert h'; decide +kernel

private def wt {n : ℕ} (x : G6.PermMod n) : ℕ :=
  (Finset.univ.filter (fun i => Multiplicative.toAdd x i ≠ 0)).card

private theorem irr_aux {n : ℕ} (P : G6.PermMod n → Prop)
    (hc1 : ∀ u : G6.PermMod n, ∑ i, Multiplicative.toAdd u i = 0 → u ≠ 1 →
      P u ∨ ∃ σ, P (u * G6.permAct n σ u))
    (hc2 : ∀ p q, P p → P q → ∃ σ, G6.permAct n σ p = q)
    (hc3 : ∀ v : G6.PermMod n, ∑ i, Multiplicative.toAdd v i = 0 →
      v = 1 ∨ P v ∨ ∃ p q, P p ∧ P q ∧ p * q = v)
    (Y : Subgroup (G6.PermMod n)) (hinv : ∀ σ, ∀ x ∈ Y, G6.permAct n σ x ∈ Y)
    (hex : ∃ u ∈ Y, ∑ i, Multiplicative.toAdd u i = 0 ∧ u ≠ 1) :
    ∀ v : G6.PermMod n, ∑ i, Multiplicative.toAdd v i = 0 → v ∈ Y := by
  obtain ⟨u, hu, hs, h1⟩ := hex
  obtain ⟨p, hpY, hp⟩ : ∃ p ∈ Y, P p := by
    rcases hc1 u hs h1 with h | ⟨σ, hσ⟩
    · exact ⟨u, hu, h⟩
    · exact ⟨_, Y.mul_mem hu (hinv σ u hu), hσ⟩
  have hq : ∀ q, P q → q ∈ Y := fun q hq => by
    obtain ⟨σ, rfl⟩ := hc2 p q hp hq
    exact hinv σ p hpY
  intro v hv
  rcases hc3 v hv with rfl | h | ⟨a, b, ha, hb, rfl⟩
  · exact Y.one_mem
  · exact hq _ h
  · exact Y.mul_mem (hq a ha) (hq b hb)

private theorem cert_irr_three_1 :
    ∀ u : G6.PermMod 3, ∑ i, Multiplicative.toAdd u i = 0 → u ≠ 1 →
      wt u = 2 ∨ ∃ σ : Equiv.Perm (Fin 3), wt (u * G6.permAct 3 σ u) = 2 := by
  decide +kernel

private theorem cert_irr_three_2 :
    ∀ p q : G6.PermMod 3, wt p = 2 → wt q = 2 →
      ∃ σ : Equiv.Perm (Fin 3), G6.permAct 3 σ p = q := by
  decide +kernel

private theorem cert_irr_three_3 :
    ∀ v : G6.PermMod 3, ∑ i, Multiplicative.toAdd v i = 0 →
      v = 1 ∨ wt v = 2 ∨ ∃ p q : G6.PermMod 3, wt p = 2 ∧ wt q = 2 ∧ p * q = v := by
  decide +kernel

private theorem cert_irr_five_1 :
    ∀ u : G6.PermMod 5, ∑ i, Multiplicative.toAdd u i = 0 → u ≠ 1 →
      wt u = 2 ∨ ∃ σ : Equiv.Perm (Fin 5), wt (u * G6.permAct 5 σ u) = 2 := by
  decide +kernel

private theorem cert_irr_five_2 :
    ∀ p q : G6.PermMod 5, wt p = 2 → wt q = 2 →
      ∃ σ : Equiv.Perm (Fin 5), G6.permAct 5 σ p = q := by
  decide +kernel

private theorem cert_irr_five_3 :
    ∀ v : G6.PermMod 5, ∑ i, Multiplicative.toAdd v i = 0 →
      v = 1 ∨ wt v = 2 ∨ ∃ p q : G6.PermMod 5, wt p = 2 ∧ wt q = 2 ∧ p * q = v := by
  decide +kernel

end Delta

theorem card_coreMod {n : ℕ} (h : n = 3 ∨ n = 5) : Nat.card (G6.coreMod n) = 2 ^ (n - 1) := by
  rcases h with rfl | rfl
  · show Nat.card (Delta.Dsub 3) = 2 ^ 2
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  · show Nat.card (Delta.Dsub 5) = 2 ^ 4
    rw [Nat.card_eq_fintype_card]
    decide +kernel

theorem coreAct_injective {n : ℕ} (h : n = 3 ∨ n = 5) : Function.Injective (G6.coreAct n) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix : ∀ u : Delta.Dsub n, G6.permAct n σ u.1 = u.1 := fun u => by
    have := congrArg Subtype.val (DFunLike.congr_fun hσ (⟨u.1, u.2⟩ : G6.coreMod n))
    exact this
  rcases h with rfl | rfl
  · exact Delta.perm_fix_three σ hfix
  · exact Delta.perm_fix_five σ hfix

theorem natKer_eq_bot {n : ℕ} (h : n = 3 ∨ n = 5) : G6.natKer n = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  have hnot := Delta.allOnes_notMem h
  have hsq := Delta.allOnes_sq n
  have key : ∀ x ∈ Subgroup.zpowers (G6.allOnes n), x = 1 ∨ x = G6.allOnes n := by
    intro x hx
    rw [Subgroup.zpowers_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Or.inr hx
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [hsq]
    | inv x _ hx =>
      rcases hx with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (inv_eq_of_mul_eq_one_right hsq)
  rcases key _ hu with h1 | h1
  · exact Subtype.ext h1
  · exact absurd (h1 ▸ u.2) hnot

theorem coreMod_irreducible {n : ℕ} (h : n = 3 ∨ n = 5) (Y : Subgroup ↥(G6.coreMod n))
    (hY : ∀ σ : Equiv.Perm (Fin n), ∀ u ∈ Y, G6.coreAct n σ u ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  by_cases hbot : ∀ u ∈ Y, u = 1
  · exact Or.inl ((Subgroup.eq_bot_iff_forall Y).mpr hbot)
  · right
    push Not at hbot
    obtain ⟨u, huY, hu1⟩ := hbot
    have hinv : ∀ σ, ∀ x ∈ Y.map (G6.coreMod n).subtype, G6.permAct n σ x ∈
        Y.map (G6.coreMod n).subtype := by
      rintro σ x ⟨y, hy, rfl⟩
      exact ⟨G6.coreAct n σ y, hY σ y hy, rfl⟩
    have hex : ∃ x ∈ Y.map (G6.coreMod n).subtype, ∑ i, Multiplicative.toAdd x i = 0 ∧ x ≠ 1 :=
      ⟨u.1, ⟨u, huY, rfl⟩, u.2, fun h => hu1 (Subtype.ext h)⟩
    have hall : ∀ v : G6.PermMod n, ∑ i, Multiplicative.toAdd v i = 0 →
        v ∈ Y.map (G6.coreMod n).subtype := by
      rcases h with rfl | rfl
      · exact Delta.irr_aux (fun x => Delta.wt x = 2) Delta.cert_irr_three_1
          Delta.cert_irr_three_2 Delta.cert_irr_three_3 _ hinv hex
      · exact Delta.irr_aux (fun x => Delta.wt x = 2) Delta.cert_irr_five_1
          Delta.cert_irr_five_2 Delta.cert_irr_five_3 _ hinv hex
    rw [eq_top_iff]
    intro v _
    obtain ⟨y, hy, hyv⟩ := hall v.1 v.2
    have : y = v := Subtype.ext hyv
    exact this ▸ hy

end CFSG.Quasithin.X1512
