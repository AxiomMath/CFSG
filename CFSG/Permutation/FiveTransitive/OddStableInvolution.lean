module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.OddStableInvolution

open MulAction

theorem exists_fixed
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (b : G) (hb : b * b = 1) (F : Set X) (hodd : Odd F.ncard)
    (hstable : ∀ x ∈ F, b • x ∈ F) : ∃ u ∈ F, b • u = u := by
  classical
  let _ : Fintype F := Fintype.ofFinite _
  have hbb (x : X) : b • (b • x) = x := by rw [← mul_smul, hb, one_smul]
  let σ : Equiv.Perm F :=
    { toFun := fun x => ⟨b • x, hstable x x.property⟩
      invFun := fun x => ⟨b • x, hstable x x.property⟩
      left_inv := fun x => Subtype.ext (hbb x)
      right_inv := fun x => Subtype.ext (hbb x) }
  have hσ : σ ^ 2 = 1 := by
    ext x
    exact hbb x
  have heven := Equiv.Perm.two_dvd_card_support hσ
  by_contra hnone
  have hsupp : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    rw [Equiv.Perm.mem_support]
    intro h
    exact hnone ⟨x, x.property, congrArg Subtype.val h⟩
  rw [hsupp, Finset.card_univ] at heven
  have hcard : Fintype.card F = F.ncard := by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hcard] at heven
  exact hodd.not_two_dvd_nat heven

theorem enumerate_five
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (b : G) (hb : b * b = 1) (F : Set X) (hF : F.ncard = 5)
    (hstable : ∀ x ∈ F, b • x ∈ F) (u : X) (hu : u ∈ F) (hbu : b • u = u)
    (hunique : ∀ x ∈ F, b • x = x → x = u) :
    ∃ e : Fin 5 ↪ X, Set.range e = F ∧ e 0 = u ∧
      b • e 0 = e 0 ∧ b • e 1 = e 2 ∧ b • e 2 = e 1 ∧
      b • e 3 = e 4 ∧ b • e 4 = e 3 := by
  classical
  have hbb (x : X) : b • (b • x) = x := by rw [← mul_smul, hb, one_smul]
  obtain ⟨v, hv, hvu⟩ := Set.exists_ne_of_one_lt_ncard (s := F) (by omega) u
  have hbvv : b • v ≠ v := fun h => hvu (hunique v hv h)
  have hbvu : b • v ≠ u := by
    intro h
    exact hvu ((MulAction.injective b) (h.trans hbu.symm))
  obtain ⟨w, hw, hwu, hwv, hwbv⟩ : ∃ w ∈ F, w ≠ u ∧ w ≠ v ∧ w ≠ b • v := by
    by_contra hnone
    push Not at hnone
    have hsub : F ⊆ {u, v, b • v} := by
      intro w hw
      by_cases hwu : w = u
      · simp [hwu]
      by_cases hwv : w = v
      · simp [hwv]
      exact Or.inr (Or.inr (hnone w hw hwu hwv))
    have hle := Set.ncard_le_ncard hsub
    have hthree : ({u, v, b • v} : Set X).ncard = 3 := by
      simp [hvu.symm, hbvu.symm, hbvv.symm]
    omega
  have hbww : b • w ≠ w := fun h => hwu (hunique w hw h)
  have hbwu : b • w ≠ u := by
    intro h
    exact hwu ((MulAction.injective b) (h.trans hbu.symm))
  have hbwv : b • w ≠ v := by
    intro h
    have hh := congrArg (fun x : X => b • x) h
    exact hwbv (by simpa only [hbb] using hh)
  have hbw_bv : b • w ≠ b • v := fun h => hwv ((MulAction.injective b) h)
  let e : Fin 5 ↪ X :=
    ⟨![u, v, b • v, w, b • w], by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [hvu, hvu.symm, hbvu, hbvu.symm, hbvv, hbvv.symm,
          hwu, hwu.symm, hwv, hwv.symm, hwbv, hwbv.symm,
          hbww, hbww.symm, hbwu, hbwu.symm, hbwv, hbwv.symm, hbw_bv, hbw_bv.symm]⟩
  have herange : Set.range e = F := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hu
      · exact hv
      · exact hstable v hv
      · exact hw
      · exact hstable w hw
    · rw [Set.ncard_range_of_injective e.injective, Nat.card_fin, hF]
    · exact Set.toFinite F
  exact ⟨e, herange, rfl, hbu, rfl, hbb v, rfl, hbb w⟩

end FiveTransitive.OddStableInvolution

end CFSG
