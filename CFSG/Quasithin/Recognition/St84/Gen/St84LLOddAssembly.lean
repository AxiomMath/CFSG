module

public import CFSG.Quasithin.Recognition.St84.Gen.St84LLOdd
public import CFSG.Quasithin.Recognition.St84.Gen.TransportG2qTree

import CFSG.Quasithin.Recognition.St84.Gen.Sec46AGen
import CFSG.Quasithin.Recognition.St84.Sec48E
import CFSG.Quasithin.Recognition.St84.Sec4HypExists
public import CFSG.Quasithin.Recognition.St84.Gen.St84LLSplit

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
open SimpleGraph CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.Stroth


theorem st84LLOdd_of_inputs
    (hex : ∀ {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ},
      CharTwoStab (V := V) (G := G) → ∀ X : Setup Γ G, (∀ v, 2 ≤ nOf Γ v) →
      IsSingularity Γ G s → Odd s → 5 ≤ s →
      ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s → Odd (Nat.card X.GT) →
      ∃ m : ℕ, X.Sec4Hyp s (2 * m))
    (hA : ∀ {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} (Y : Setup Γ G),
      Y.CaseA → Y.CaseAGen) :
    St84LLOdd := by
  intro H _ _ L1 L2 S m n s hF hm hn hmn h1 h2 hs hodd h5 hGT
  exact f112ll_odd_of_sec4 hF hm hn h1 h2 hs hodd
    (fun X hX => hex (f112ll_charTwoStab hF hm hn h1 h2) X (two_le_nOf_f112 hF hm hn h1 h2) hs
      hodd h5 hX (hGT X))
    (fun X r H => X.sec4Row_of H (fun Y A => hA Y A)
      (fun Y r d H hd hR => Setup.sec4Row_of_comm_eq_bot
        (fun Z r d C => CFSG.Quasithin.St84.Setup.comm48_u4q Z C) Y H hd hR))
    (fun X hX0 hX1 f hd => f112ll_g2qLocalData_of_tree hF hm hn hmn h1 h2 hX0 hX1 hd)
    (fun X hX0 hX1 f hd =>
      f112ll_g2qLocalData_of_tree_swap hF hm hn hmn h1 h2 hX0 hX1 hd)

theorem st84LLOdd_holds : St84LLOdd :=
  st84LLOdd_of_inputs (fun hc X hn hs hodd h5 hX hGT => X.exists_sec4Hyp hc hn hs hodd h5 hX hGT)
    (fun _ A => A.toGen)

end CFSG.Quasithin.F112R.St84

end
