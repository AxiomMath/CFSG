module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import Certificates.Kernel.Bounds.Suz.T1vData
public import Certificates.Kernel.Bounds.Suz.T2vData
public import Certificates.Kernel.Bounds.Suz.T3vData
public import Certificates.Kernel.Bounds.Suz.T4vData
import CFSG.Certificates.Kernel.Bounds.Load

open CFSG.Certificates

public section

namespace CFSG.KBRoute.Suz

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)], [(3, true), (3, true)], [(4, true), (4, true)], [(5, true), (5, true)], [(6, true), (6, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)], [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)], [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)], [(1, true), (5, true), (1, true), (5, true), (1, true), (5, true)], [(5, true), (6, true), (5, true), (6, true), (5, true), (6, true), (5, true), (6, true)], [(6, true), (1, true), (6, true), (1, true), (6, true), (1, true)], [(0, true), (2, true), (0, true), (2, true)], [(0, true), (3, true), (0, true), (3, true)], [(0, true), (4, true), (0, true), (4, true)], [(0, true), (5, true), (0, true), (5, true)], [(0, true), (6, true), (0, true), (6, true)], [(1, true), (3, true), (1, true), (3, true)], [(1, true), (4, true), (1, true), (4, true)], [(2, true), (4, true), (2, true), (4, true)], [(2, true), (5, true), (2, true), (5, true)], [(2, true), (6, true), (2, true), (6, true)], [(3, true), (5, true), (3, true), (5, true)], [(3, true), (6, true), (3, true), (6, true)], [(4, true), (5, true), (4, true), (5, true)], [(4, true), (6, true), (4, true), (6, true)], [(0, false), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true)], [(0, false), (5, true), (6, true), (5, true), (6, true)], [(0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true), (0, true), (1, true), (2, true), (5, true)], [(1, true), (5, true), (6, true), (1, true), (5, true), (6, true), (1, true), (5, true), (6, true), (1, true), (5, true), (6, true), (1, true), (5, true), (6, true)], [(1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (4, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (4, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (1, true), (2, true), (3, true), (2, true), (3, true), (4, true)], [(0, true), (1, true), (2, true), (6, true), (0, true), (1, true), (2, true), (6, true), (0, true), (1, true), (2, true), (6, true), (0, true), (1, true), (2, true), (6, true), (0, true), (1, true), (2, true), (6, true)]]

#kb_table CFSG.KBRoute.Suz T1 Suz_T1v include_bytes "data/Suz_T1v.meta" 3149 9308309354496609925 1976943448883713 CFSG.KBRoute.Suz.rels "1 2 3 4 5 6"

#kb_table CFSG.KBRoute.Suz T2 Suz_T2v include_bytes "data/Suz_T2v.meta" 729 17567991394435746506 6618611909121 CFSG.KBRoute.Suz.rels "1 2 3 4 5"

#kb_table CFSG.KBRoute.Suz T3 Suz_T3v include_bytes "data/Suz_T3v.meta" 431 2536992008051246648 21542142465 CFSG.KBRoute.Suz.rels "1 2 3 4"

#kb_table CFSG.KBRoute.Suz T4 Suz_T4v include_bytes "data/Suz_T4v.meta" 5057 4390005806162259891 67305985 CFSG.KBRoute.Suz.rels ""

theorem top : KB.topOk T1.amap (nat_lit 7) = true := by quickRfl

theorem top_T2 : KB.topOk T2.amap (nat_lit 6) = true := by quickRfl

theorem top_T3 : KB.topOk T3.amap (nat_lit 5) = true := by quickRfl

theorem top_T4 : KB.topOk T4.amap (nat_lit 4) = true := by quickRfl

theorem link_T1 : KB.linkOk T2.amap T1.words = true := by quickRfl

theorem link_T2 : KB.linkOk T3.amap T2.words = true := by quickRfl

theorem link_T3 : KB.linkOk T4.amap T3.words = true := by quickRfl

theorem order : Nat.beq (Nat.mul (Nat.mul (Nat.mul T1.N T2.N) T3.N) T4.N) (nat_lit 448345497600) = true := by quickRfl

end CFSG.KBRoute.Suz

end
