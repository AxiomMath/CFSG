module

public import Certificates.Kernel.DELK.D
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option Elab.async false

public section

namespace CFSG.KD.DELK

open Certificates.TwoDepSmallLow Certificates.DELK

theorem cover : kCover O T = true := by decide +kernel

theorem groupsCover : kGroupsCover P S C = true := by decide +kernel

theorem lenO : O.length = 3 := by decide +kernel

theorem lenT : T.length = 6 := by decide +kernel

theorem lenS : S.length = 2 := by decide +kernel

theorem lenC : C.length = 2 := by decide +kernel

theorem neg_cl : (!kSubOK ((P.getD 0 []).map (ggTWLMatOfPair 3 6))
    (let s := (S.getD 0 (0, [], [])).2.1.getD 2 ([], [], [], [], [])
     (s.1, s.2.1, s.2.2.1, s.2.2.2.1.map (·.map (· + 1)), s.2.2.2.2))) = true := by
  decide +kernel

theorem neg_ord : (!kSubOK ((P.getD 0 []).map (ggTWLMatOfPair 3 6))
    (let s := (S.getD 0 (0, [], [])).2.1.getD 2 ([], [], [], [], [])
     (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.reverse))) = true := by
  decide +kernel

theorem neg_tree : (!kSubOK ((P.getD 0 []).map (ggTWLMatOfPair 3 6))
    (let s := (S.getD 0 (0, [], [])).2.1.getD 2 ([], [], [], [], [])
     (s.1, s.2.1, s.2.2.1.dropLast, s.2.2.2.1, s.2.2.2.2))) = true := by
  decide +kernel

theorem neg_base : (!kSubOK ((P.getD 0 []).map (ggTWLMatOfPair 3 6))
    (let s := (S.getD 0 (0, [], [])).2.1.getD 2 ([], [], [], [], [])
     (s.1, s.2.1.map (·.dropLast), s.2.2.1, s.2.2.2.1, s.2.2.2.2))) = true := by
  decide +kernel

theorem neg_cen : (!(let Om := (P.getD 0 []).map (ggTWLMatOfPair 3 6)
    kCen Om (ggTWLWordMat 3 6 Om (S.getD 0 (0, [], [])).2.2.tail))) = true := by
  decide +kernel

theorem neg_conj : (!kConjAt P S (C.map fun c => (c.1, c.2.1, c.2.2.2, c.2.2.1)) 0) = true := by
  decide +kernel

theorem neg_groups : (!kGroupsCover P S C.tail) = true := by decide +kernel

theorem neg_grp : (!(let e := ((T.getD 0 ((0, 0), [], [])).2.2.getD 0 (([], [], [], []), (0, 0)))
    let news := [(e.1.1, e.1.2.1), (e.1.2.2.1, e.1.2.2.2)]
    let z := Z.getD e.2.2 kZ0
    kPZRef P news (Certificates.DepED4Low.ggDepELY0 news) (z.1, z.2 + 1))) = true := by
  decide +kernel

theorem neg_hk : (!kPat1At (H.map fun h => ((h.1.1 + 100, h.1.2), h.2)) Z P O 0) = true := by
  decide +kernel

theorem neg_hkset : (!kPat1At (H.map fun h => (h.1, h.2.tail)) Z P O 0) = true := by
  decide +kernel

theorem neg_kind : (!kPat2At H Z P
    (T.map fun e => (e.1, e.2.1, e.2.2.map fun c => (c.1, if c.2.1 = 2 then 1 else c.2.1,
      c.2.2))) 0) = true := by
  decide +kernel

theorem neg_cover : (!kCover O T.tail) = true := by decide +kernel

end CFSG.KD.DELK

#kc_each CFSG.KD.DELK ch709539c (Certificates.DELK.kConjAt CFSG.KD.DELK.P CFSG.KD.DELK.S
  CFSG.KD.DELK.C) 0 2

#kc_each CFSG.KD.DELK ch709539g (Certificates.DELK.kBaseAt CFSG.KD.DELK.P CFSG.KD.DELK.S) 0 2

#kc_each CFSG.KD.DELK ch709539o (Certificates.DELK.kPat1At CFSG.KD.DELK.H CFSG.KD.DELK.Z
  CFSG.KD.DELK.P CFSG.KD.DELK.O) 0 3

#kc_each CFSG.KD.DELK ch709539t (Certificates.DELK.kPat2At CFSG.KD.DELK.H CFSG.KD.DELK.Z
  CFSG.KD.DELK.P CFSG.KD.DELK.T) 0 6

end
