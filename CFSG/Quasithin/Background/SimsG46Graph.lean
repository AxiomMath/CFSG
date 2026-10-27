module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Quasithin.SimsG4

section Aux

variable {Γ : Type*} [Group Γ]

private theorem exists_mem_closure_conj_of_odd_orderOf {D : Set Γ} {s t : Γ} (hs : s ∈ D)
    (ht : t ∈ D) (hs2 : s * s = 1) (ht2 : t * t = 1) (hodd : Odd (orderOf (s * t))) :
    ∃ x ∈ Subgroup.closure D, x * t * x⁻¹ = s := by
  obtain ⟨k, hk⟩ := hodd
  have hwk : (s * t) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hinv : (s * t)⁻¹ = t * s := by rw [mul_inv_rev, hs', ht']
  have hinvt : t * (s * t) * t⁻¹ = (s * t)⁻¹ := by
    rw [hinv, ht']
    calc t * (s * t) * t = t * s * (t * t) := by simp only [mul_assoc]
      _ = t * s := by rw [ht2, mul_one]
  have hpow : t * (s * t) ^ k = ((s * t) ^ k)⁻¹ * t := by
    have h := conj_pow (a := t) (b := s * t) (i := k)
    rw [hinvt, inv_pow] at h
    exact mul_inv_eq_iff_eq_mul.mp h.symm
  have hw2 : (s * t) ^ (k + k) = (s * t)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show k + k + 1 = 2 * k + 1 by omega, hwk]
  refine ⟨((s * t) ^ k)⁻¹, ?_, ?_⟩
  · exact inv_mem (Subgroup.pow_mem _
      (mul_mem (Subgroup.subset_closure hs) (Subgroup.subset_closure ht)) k)
  · rw [inv_inv, ← hpow, mul_assoc, ← pow_add, hw2, hinv, ← mul_assoc, ht2, one_mul]

end Aux

theorem connected_iff_transitive {Γ : Type*} [Group Γ] (D : Set Γ) (hD : D.Nonempty)
    (hinv : ∀ d ∈ D, d * d = 1)
    (hconj : ∀ g ∈ Subgroup.closure D, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hodd : ∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) = 2 ∨ Odd (orderOf (a * b))) :
    (SimpleGraph.fromRel fun a b : ↥D => (a : Γ) * b ≠ b * a).Connected ↔
      ∀ a ∈ D, ∀ b ∈ D, ∃ g ∈ Subgroup.closure D, g * a * g⁻¹ = b := by
  set Gr : SimpleGraph ↥D := SimpleGraph.fromRel fun a b : ↥D => (a : Γ) * b ≠ b * a with hGr
  have hinv' : ∀ d ∈ D, d⁻¹ = d := fun d hd => inv_eq_of_mul_eq_one_right (hinv d hd)
  have hadj : ∀ a b : ↥D, Gr.Adj a b ↔ (a : Γ) * b ≠ b * a := by
    intro a b
    rw [hGr, SimpleGraph.fromRel_adj]
    refine ⟨?_, fun h => ⟨fun hab => h (by rw [hab]), Or.inl h⟩⟩
    rintro ⟨-, h | h⟩
    · exact h
    · exact Ne.symm h
  constructor
  · intro hc a ha b hb
    have hstep : ∀ b c : ↥D, Gr.Adj b c → ∃ h ∈ Subgroup.closure D, h * (b : Γ) * h⁻¹ = c := by
      intro b c hbc
      have hne := (hadj b c).mp hbc
      have hodd' : Odd (orderOf ((c : Γ) * b)) := by
        rcases hodd c c.2 b b.2 with h2 | h
        · exfalso
          apply hne
          have hsq := pow_orderOf_eq_one ((c : Γ) * b)
          rw [h2, pow_two] at hsq
          calc (b : Γ) * c = ((c : Γ) * b)⁻¹ := by rw [mul_inv_rev, hinv' b b.2, hinv' c c.2]
            _ = c * b := inv_eq_of_mul_eq_one_right hsq
        · exact h
      exact exists_mem_closure_conj_of_odd_orderOf c.2 b.2 (hinv c c.2) (hinv b b.2) hodd'
    have key : ∀ x y : ↥D, Gr.Reachable x y →
        ∃ g ∈ Subgroup.closure D, g * (x : Γ) * g⁻¹ = y := by
      intro x y hxy
      rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
      induction hxy with
      | refl => exact ⟨1, one_mem _, by simp⟩
      | tail _ hbc ih =>
        obtain ⟨g, hg, hgx⟩ := ih
        obtain ⟨h, hh, hhb⟩ := hstep _ _ hbc
        exact ⟨h * g, mul_mem hh hg, by rw [← hhb, ← hgx]; simp [mul_assoc]⟩
    exact key ⟨a, ha⟩ ⟨b, hb⟩ (hc.preconnected _ _)
  · intro htrans
    have hstep : ∀ d ∈ D, ∀ x y : ↥D, (y : Γ) = d * x * d⁻¹ → Gr.Reachable x y := by
      intro d hd x y hy
      by_cases hcomm : (x : Γ) * d = d * x
      · have hyx : y = x := Subtype.ext (by rw [hy, ← hcomm, mul_inv_cancel_right])
        rw [hyx]
      · have e1 : d * (y : Γ) = x * d := by
          rw [hy, hinv' d hd]
          simp only [← mul_assoc, hinv d hd, one_mul]
        have e2 : (y : Γ) * d = d * x := by rw [hy, inv_mul_cancel_right]
        have hxd : Gr.Adj x ⟨d, hd⟩ := (hadj _ _).mpr hcomm
        have hdy : Gr.Adj ⟨d, hd⟩ y := by
          refine (hadj _ _).mpr fun h => hcomm ?_
          have h' : d * (y : Γ) = y * d := h
          rwa [e1, e2] at h'
        exact hxd.reachable.trans hdy.reachable
    have hmain : ∀ g ∈ Subgroup.closure D, ∀ x y : ↥D, (y : Γ) = g * x * g⁻¹ →
        Gr.Reachable x y := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem d hd => exact hstep d hd
      | one =>
        intro x y hy
        have hyx : y = x := Subtype.ext (by simpa using hy)
        rw [hyx]
      | mul g h hg hh ihg ihh =>
        intro x y hy
        have hz : h * (x : Γ) * h⁻¹ ∈ D := hconj h hh x x.2
        exact (ihh x ⟨_, hz⟩ rfl).trans (ihg ⟨_, hz⟩ y (by rw [hy]; simp [mul_assoc]))
      | inv g hg ih =>
        intro x y hy
        exact (ih y x (by rw [hy]; simp [mul_assoc])).symm
    haveI : Nonempty ↥D := hD.to_subtype
    refine ⟨fun u v => ?_⟩
    obtain ⟨g, hg, hgu⟩ := htrans u u.2 v v.2
    exact hmain g hg u v hgu.symm

end CFSG.Quasithin.SimsG4
