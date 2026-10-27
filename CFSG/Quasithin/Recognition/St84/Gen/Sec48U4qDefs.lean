module

public import CFSG.Quasithin.Recognition.St84.Sec48A
public import CFSG.Quasithin.Recognition.St84.Sec4QuotA

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

structure U4qBase (X : Setup Γ G) : Prop where
  gen : X.Comm48 5 4 1
  hasB0 : X.HasB 0 2
  hasB2 : X.HasB 2 2
  Z0_eq : X.Z 0 = centerOf (X.L 0)
  Z0_le_Z1 : X.Z 0 ≤ X.Z 1
  card_S : Nat.card X.S = 2 ^ (2 * X.n 0 + 2 * X.n 1)
  card_Q0 : Nat.card (X.Q 0) = 2 ^ (X.n 0 + 2 * X.n 1)
  card_Q1 : Nat.card (X.Q 1) = 2 ^ (2 * X.n 0 + X.n 1)
  Z2_eq : X.Z 2 = X.Qg 4
  Z0_eq_pCore : X.Z 0 = pCoreOf 2 (X.arcStab (-2) 2)
  card_Z0 : Nat.card (X.Z 0) = 2 ^ X.n 0
  card_Z2 : Nat.card (X.Z 2) = 2 ^ X.n 0
  elem_Z0 : IsElemAbelian 2 (X.Z 0)
  elem_Z2 : IsElemAbelian 2 (X.Z 2)
  Z0_inf_Q2 : X.Z 0 ⊓ X.Q 2 = ⊥
  Z0_inf_Qm2 : X.Z 0 ⊓ X.Q (-2) = ⊥
  Z2_inf_Q0 : X.Z 2 ⊓ X.Q 0 = ⊥
  Z2_inf_Q4 : X.Z 2 ⊓ X.Q 4 = ⊥
  Z0_inf_Z2 : X.Z 0 ⊓ X.Z 2 = ⊥
  sup_S : X.Z 2 ⊔ X.Q 0 = X.S
  Q1_eq : X.Q 1 = X.Z 0 ⊔ X.Z 2 ⊔ (X.Q 0 ⊓ X.Q 2)
  Q1_inf_Q0 : X.Q 1 ⊓ X.Q 0 = X.Z 0 ⊔ (X.Q 0 ⊓ X.Q 2)
  card_A : Nat.card ↥(X.Q 0 ⊓ X.Q 2) = 2 ^ X.n 1
  card_Q0_inf_Q1 : Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ (X.n 0 + X.n 1)
  Q1_inf_Qm1 : X.Q 1 ⊓ X.Q (-1) = X.Z 0
  elem_A : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2)
  elem_Q1 : IsElemAbelian 2 (X.Q 1)
  quad : ⁅⁅X.Q 0, X.S⁆, X.S⁆ ≤ X.Z 0

namespace U4qBase

variable {X : Setup Γ G}

theorem Q0_eq_sup (B : X.U4qBase) : X.Q 0 = (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) := by
  simpa using
    (X.Q_quot B.gen.hyp.char B.gen.hyp.sing (Nat.le_of_succ_le B.gen.hyp.five_le) 0).2.2.2.2.2

theorem isElemSec_Q0 (B : X.U4qBase) : IsElemSec (X.Z 0) (X.Q 0) := by
  obtain ⟨-, hsq, hcomm, -⟩ :=
    X.Q_quot B.gen.hyp.char B.gen.hyp.sing (Nat.le_of_succ_le B.gen.hyp.five_le) 0
  have hA : X.Q (0 - 1) ⊓ X.Q (0 + 1) = X.Z 0 := by
    simpa [inf_comm] using B.Q1_inf_Qm1
  rw [hA] at hsq hcomm
  exact ⟨X.Z_le_Q 0, hcomm, hsq⟩

end U4qBase

end Setup

end CFSG.Quasithin.St84

end
