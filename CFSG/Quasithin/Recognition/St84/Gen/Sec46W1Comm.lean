module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec46W1
public import CFSG.Quasithin.Recognition.St84.Gen.NatSecPre

import CFSG.Quasithin.Recognition.St84.Gen.NatSecSumBil
import CFSG.Quasithin.Recognition.St84.Sec4Local

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

theorem CaseAW1Hyp.comm_le (W : X.CaseAW1Hyp) {P Z : Subgroup G} [Finite ↥P]
    (hV : NatPre P (X.L 1) (X.Q 0 ⊓ X.Q 2) Z (X.n 1))
    (hVZ : NatQuot (X.L 1) (X.Q 0 ⊓ X.Q 2) Z (X.n 1))
    (hcent : ⁅X.Q 1, X.Q 0 ⊓ X.Q 2⁆ ≤ Z) : ⁅X.Q 1, X.Q 1⁆ ≤ Z :=
  comm_le_of_quadratic (P := P) (L := X.L 1) (E := X.Q 1) (V := X.Q 0 ⊓ X.Q 2)
    (Z := Z) (T := X.edgeSylow 1) W.two_le_n1 (X.Q_le_L 1) W.sec
    ((X.L_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)))
    (fun _ hx _ he => W.core hx he) W.relCent_L (X.isSylowTwoOf_edgeSylow_L 1)
    (fun _ ht _ ht' _ he => W.quad ht ht' he) (fun _ _ h1 h2 h3 => W.gen h1 h2 h3)
    hV hVZ hcent

end Setup

end CFSG.Quasithin.St84

end
