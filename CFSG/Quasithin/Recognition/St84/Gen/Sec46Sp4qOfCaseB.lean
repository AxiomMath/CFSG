module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec46Sp4qLocal
public import CFSG.Quasithin.Recognition.St84.Sec46Cases


public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.Quasithin.F112R.St84
open scoped commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

theorem CaseB.card_S (B : X.CaseB) : Nat.card X.S = 2 ^ (2 * X.n 0 + 2 * X.n 1) := by
  have H := B.hyp
  have hpGT : pCoreOf 2 X.GT = ⊥ := by
    have h := inf_eq_bot_of_odd_of_isPGroup (A := X.GT) (B := pCoreOf 2 X.GT) H.odd_GT
      (pCoreOf_isPGroup' X.GT)
    have hle : pCoreOf 2 X.GT ≤ X.GT ⊓ pCoreOf 2 X.GT :=
      le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X.GT) le_rfl
    rw [h] at hle
    exact le_bot_iff.mp hle
  have harc : X.arcStab 0 (5 : ℕ) = X.GT := by
    simpa using H.longReg.2 0 5 (by norm_num)
  have h := X.card_S_eq_prod H.sing
  rw [harc, hpGT, Subgroup.card_bot, mul_one] at h
  rw [h]
  have h2 : X.n (2 : ℤ) = X.n 0 := by simpa using X.n_add 1 0
  have h3 : X.n (3 : ℤ) = X.n 1 := by simpa using X.n_add 1 1
  have h4 : X.n (4 : ℤ) = X.n 0 := by simpa using X.n_add 2 0
  rw [show Finset.Icc 1 (5 - 1) = ({1, 2, 3, 4} : Finset ℕ) by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  push_cast
  rw [h2, h3, h4, ← pow_add, ← pow_add, ← pow_add]
  ring_nf

theorem CaseB.inf_bot (B : X.CaseB) : X.Q (-1) ⊓ X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2 = ⊥ := by
  have H := B.hyp
  set U := X.Q (-1) ⊓ X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2 with hU
  have hU2 : IsPGroup 2 ↥U :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have harc : X.arcStab (-2) 3 = X.GT := by
    have h := H.longReg.2 (-2) 5 (by norm_num)
    norm_num at h
    exact h
  have hfix : ∀ j : ℤ, -2 ≤ j → j ≤ 3 → U ≤ X.Gi j := by
    intro j hj1 hj2
    have hm1 : U ≤ X.Q (-1) := inf_le_left.trans (inf_le_left.trans inf_le_left)
    have h0 : U ≤ X.Q 0 := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have h1 : U ≤ X.Q 1 := inf_le_left.trans inf_le_right
    have h2 : U ≤ X.Q 2 := inf_le_right
    interval_cases j
    · exact hm1.trans ((X.Q_le_Gi_adj (-1)).trans inf_le_left)
    · exact hm1.trans (X.Q_le_Gi (-1))
    · exact h0.trans (X.Q_le_Gi 0)
    · exact h1.trans (X.Q_le_Gi 1)
    · exact h2.trans (X.Q_le_Gi 2)
    · exact h2.trans ((X.Q_le_Gi_adj 2).trans inf_le_right)
  have hle : U ≤ X.GT := by
    rw [← harc]
    refine X.le_arcStab_of_fixSet fun j hj u hu => ?_
    obtain ⟨hj1, hj2⟩ := Set.mem_Icc.mp hj
    exact MulAction.mem_stabilizer_iff.mp (hfix j hj1 hj2 hu)
  have h := inf_eq_bot_of_odd_of_isPGroup (A := X.GT) (B := U) H.odd_GT hU2
  rwa [inf_eq_right.mpr hle] at h

theorem CaseB.toGen (B : X.CaseB) : X.CaseBGen where
  char := B.hyp.char
  two_le_n := B.hyp.two_le_n
  b₀ := B.b₀
  b₁ := B.b₁
  R_le := B.R_le
  R_ne := B.R_ne
  card_S := B.card_S
  inf_bot := B.inf_bot

theorem caseB_sp4q_of_caseB (X : Setup Γ G) (B : X.CaseB) :
    X.n 1 = X.n 0 ∧ Sp4qLocalData (X.L 0) (X.L 1) X.S (X.n 0) :=
  X.caseB_sp4q B.toGen

end Setup

end CFSG.Quasithin.St84

end
