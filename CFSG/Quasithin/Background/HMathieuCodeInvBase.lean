
module

public import CFSG.Quasithin.Background.HMathieuCodeMask
public import CFSG.Quasithin.Background.HMathieuSyl22
public import CFSG.Quasithin.Background.HMathieuSyl23
public import CFSG.Quasithin.Background.HMathieuSyl24
public import CFSG.Quasithin.Background.HMathieuFacts24Base
public meta import CFSG.Quasithin.Background.HMathieuCodeMask
public meta import CFSG.Quasithin.Background.HMathieuSyl22
public meta import CFSG.Quasithin.Background.HMathieuSyl23
public meta import CFSG.Quasithin.Background.HMathieuSyl24
public meta import CFSG.Quasithin.Background.HMathieuFacts24Base
public meta import CFSG.Monster.Code.Basis
public import CFSG.Quasithin.Background.HMathieuCodeInvInputs
public import CFSG.Quasithin.Background.HMathieuSyl22Inputs
public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Quasithin.Background.HMathieuSyl23Inputs
public import CFSG.Quasithin.Background.HMathieuSyl24Inputs
public import CFSG.Quasithin.Background.HMathieuAvoid
public import CFSG.Quasithin.Background.HMathieuEnumAll

@[expose] public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

theorem actM_matsC10 (T : PT 24) [Fact (T.check = true)] {mats : Array (List ℕ)}
    (hm : mats = matsOfC10 T) (p : T.Elem) {m : ℕ} (hm2 : m < 2 ^ 10) :
    actM (mats[p.idx]!) m = actC10 (T.arr p) m := by
  have hlt : p.idx < T.elems.size := by rw [T.size_elems]; exact p.lt
  rw [hm, matsOfC10, getElem!_pos _ p.idx (by simpa using hlt), Array.getElem_map, PT.arr,
    getElem!_pos _ p.idx hlt, actM_matOf (xorLin_actC10 _) 10 m hm2]

theorem actM_matsC11 (T : PT 24) [Fact (T.check = true)] {mats : Array (List ℕ)}
    (hm : mats = matsOfC11 T) (p : T.Elem) {m : ℕ} (hm2 : m < 2 ^ 11) :
    actM (mats[p.idx]!) m = actC11 (T.arr p) m := by
  have hlt : p.idx < T.elems.size := by rw [T.size_elems]; exact p.lt
  rw [hm, matsOfC11, getElem!_pos _ p.idx (by simpa using hlt), Array.getElem_map, PT.arr,
    getElem!_pos _ p.idx hlt, actM_matOf (xorLin_actC11 _) 11 m hm2]

end CFSG.Quasithin.H.Mathieu
