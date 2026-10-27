module

public import CFSG.GH74.GLS.C3.Layer2.L5C2c
public import CFSG.GH74.GLS.C3.Layer2.L5C2a

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

@[expose] def greedyStep {n : Nat} (R : List (Idx n)) (Ls : List (List (Idx n))) (st : Nat × Bool)
    (s : Idx n) : Nat × Bool :=
  if (Ls.getD st.1 []).contains s then st else (st.1 + 1, st.2 && decide (R[st.1]? = some s))

@[expose] def greedySim {n : Nat} (S R : List (Idx n)) (Ls : List (List (Idx n))) : Bool :=
  let st := S.foldl (greedyStep R Ls) (0, true)
  st.2 && decide (st.1 = R.length)

@[expose] def subChk {n : Nat} [Group (Idx n)] (gs : List (Idx n)) (W : List (Idx n × List Nat)) :
    Bool :=
  (W.map Prod.fst).contains 1 &&
    W.all (fun p => gs.all fun g => (W.map Prod.fst).contains (p.1 * g)) &&
    W.all (fun p => decide (evW gs p.2 = p.1))

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
