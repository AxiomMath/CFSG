module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinWeylRank

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CoxeterSystem CFSG.LieType.Universal.Symplectic

theorem card_coxeterB_le (n : ℕ) : Nat.card (CoxeterMatrix.B n).Group ≤ 2 ^ n * n.factorial := by
  rw [← coxeterMatrix_cartanC_eq_B n]
  classical
  let sgn : (Fin n → ℤ) → (Fin n → Bool) := fun s a => decide (s a = 1)
  have key : ∀ w : (coxeterMatrix (isFiniteType_cartanC n)).Group,
      ∃ q : Equiv.Perm (Fin n) × (Fin n → ℤ), SpIsSign q.2 ∧ SpRealizes n w q.1 q.2 := by
    intro w
    obtain ⟨π, s, hs, h⟩ := exists_spRealizes w
    exact ⟨(π, s), hs, h⟩
  choose q hq using key
  let f : (coxeterMatrix (isFiniteType_cartanC n)).Group →
      Equiv.Perm (Fin n) × (Fin n → Bool) := fun w => ((q w).1, sgn (q w).2)
  have hsgn : ∀ {s s' : Fin n → ℤ}, SpIsSign s → SpIsSign s' → sgn s = sgn s' → s = s' := by
    intro s s' hs hs' h
    funext a
    have ha := congrFun h a
    simp only [sgn, decide_eq_decide] at ha
    rcases hs a with h1 | h1 <;> rcases hs' a with h2 | h2
    · rw [h1, h2]
    · exfalso
      have := ha.mp h1
      rw [h2] at this
      norm_num at this
    · exfalso
      have := ha.mpr h2
      rw [h1] at this
      norm_num at this
    · rw [h1, h2]
  have hf : Function.Injective f := by
    intro w w' hww'
    have h1 : (q w).1 = (q w').1 := (Prod.ext_iff.mp hww').1
    have h2 : sgn (q w).2 = sgn (q w').2 := (Prod.ext_iff.mp hww').2
    have h3 : (q w).2 = (q w').2 := hsgn (hq w).1 (hq w').1 h2
    exact SpRealizes.inj (hq w).2 ((hq w').2.congr h1.symm h3.symm)
  calc Nat.card (coxeterMatrix (isFiniteType_cartanC n)).Group
      ≤ Nat.card (Equiv.Perm (Fin n) × (Fin n → Bool)) := Nat.card_le_card_of_injective f hf
    _ = 2 ^ n * n.factorial := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          Fintype.card_perm, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
        ring

end CFSG.StandardType
