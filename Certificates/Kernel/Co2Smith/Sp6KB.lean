module

public import Certificates.Data.CFSGNative.Co2Smith.Sp6Pres
public import Certificates.Data.Kernel.Bounds.TableFact
public import CFSG.Certificates.Kernel.Bounds.Checks
public import Certificates.Kernel.Bounds.Assemble
public import CFSG.Certificates.CosetTablePresented
import CFSG.Certificates.Kernel.Bounds.Load
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

open CFSG.Sporadic.Co2Smith.Native CFSG.CosetTable

public section

set_option maxRecDepth 100000

namespace CFSG.KBRoute.K10084a

@[expose] def rels : List (List (Nat × Bool)) :=
  (sp6Rels ()).map fun w => w.map fun l => (l.1.val, l.2)

end CFSG.KBRoute.K10084a

namespace CFSG.KBRoute.K10084b

@[expose] def rels : List (List (Nat × Bool)) :=
  (restrictWords [(6 : Fin 8), 7] (sp6Rels ())).map fun w => w.map fun l => (l.1.val, l.2)

end CFSG.KBRoute.K10084b

namespace CFSG.KBRoute.K10084c

@[expose] def rels : List (List (Nat × Bool)) :=
  (sp6CoverR ()).map fun w => w.map fun l => (l.1.val, l.2)

end CFSG.KBRoute.K10084c

namespace CFSG.KBRoute.K10084d

@[expose] def rels : List (List (Nat × Bool)) :=
  (restrictWords [(6 : Fin 8), 7] (sp6CoverR ())).map fun w => w.map fun l => (l.1.val, l.2)

end CFSG.KBRoute.K10084d

#kc_repo #kc_blocked_root CFSG.KBData.K10084a.F "Certificates/Kernel/Co2Smith/data/K10084a.F.bin" 12 6 18446744073709551615 16496 16344384238057308295
#kc_repo #kc_blocked_root CFSG.KBData.K10084a.D "Certificates/Kernel/Co2Smith/data/K10084a.D.bin" 12 4 65535 538 10074502817808444183
#kc_repo #kc_items_root CFSG.KBData.K10084a.Wd "Certificates/Kernel/Co2Smith/data/K10084a.Wd.items" 1279 146612079865013507
#kc_repo #kc_items_root CFSG.KBData.K10084a.Wd2 "Certificates/Kernel/Co2Smith/data/K10084a.Wd2.items" 1904 16580799235191217314
#kc_repo #kc_items_root CFSG.KBData.K10084a.R "Certificates/Kernel/Co2Smith/data/K10084a.R.items" 342 18220505260529694719
#kc_repo #kc_items_root CFSG.KBData.K10084a.S "Certificates/Kernel/Co2Smith/data/K10084a.S.items" 16 11195056550565907830
#kc_repo #kc_list_root CFSG.KBData.K10084a.wl0 "Certificates/Kernel/Co2Smith/data/K10084a.wl0.items" 1 23844 6497784592549246469
#kc_repo #kc_list_root CFSG.KBData.K10084a.cv0 "Certificates/Kernel/Co2Smith/data/K10084a.cv0.items" 1 6315 2511493397823045385

#kb_table CFSG.KBRoute.K10084a T1 K10084a include_bytes "data/K10084a.meta" 458 13399827935545566570 578437695752307201 CFSG.KBRoute.K10084a.rels "7 8"

theorem CFSG.KBRoute.K10084a.top :
    CFSG.Certificates.KB.topOk CFSG.KBRoute.K10084a.T1.amap (nat_lit 8) = true := by
  quickRfl

#kb_checks K10084a include_bytes "data/K10084a.meta" 458 13399827935545566570 0

#kb_cert CFSG.KBRoute.K10084a T1 K10084a include_bytes "data/K10084a.meta" 458 13399827935545566570 CFSG.KBRoute.K10084a.rels

theorem CFSG.KBRoute.K10084a.t1 : CFSG.KBRoute.K10084a.T1.ok = true := by kb_assemble K10084a

theorem CFSG.KBFact.K10084a :
    CFSG.Certificates.KB.TableFact 8 CFSG.KBRoute.K10084a.rels CFSG.KBRoute.K10084a.T1.words 240 :=
  CFSG.Certificates.KB.TableFact.intro CFSG.KBRoute.K10084a.t1 CFSG.KBRoute.K10084a.top

#kc_repo #kc_blocked_root CFSG.KBData.K10084b.F "Certificates/Kernel/Co2Smith/data/K10084b.F.bin" 12 6 18446744073709551615 98048 7599222153405006697
#kc_repo #kc_blocked_root CFSG.KBData.K10084b.D "Certificates/Kernel/Co2Smith/data/K10084b.D.bin" 12 4 65535 12226 13582347426839599312
#kc_repo #kc_items_root CFSG.KBData.K10084b.Wd "Certificates/Kernel/Co2Smith/data/K10084b.Wd.items" 843 9965573644085890114
#kc_repo #kc_items_root CFSG.KBData.K10084b.Wd2 "Certificates/Kernel/Co2Smith/data/K10084b.Wd2.items" 1390 6377338884927589093
#kc_repo #kc_items_root CFSG.KBData.K10084b.R "Certificates/Kernel/Co2Smith/data/K10084b.R.items" 88 10605911157911472605
#kc_repo #kc_items_root CFSG.KBData.K10084b.S "Certificates/Kernel/Co2Smith/data/K10084b.S.items" 4 14007230941556241898
#kc_repo #kc_list_root CFSG.KBData.K10084b.wl0 "Certificates/Kernel/Co2Smith/data/K10084b.wl0.items" 1 119768 16986829181318738583
#kc_repo #kc_list_root CFSG.KBData.K10084b.cv0 "Certificates/Kernel/Co2Smith/data/K10084b.cv0.items" 1 47248 5553232110882372034

#kb_table CFSG.KBRoute.K10084b T1 K10084b include_bytes "data/K10084b.meta" 2069 15788974455626622437 513 CFSG.KBRoute.K10084b.rels ""

theorem CFSG.KBRoute.K10084b.top :
    CFSG.Certificates.KB.topOk CFSG.KBRoute.K10084b.T1.amap (nat_lit 2) = true := by
  quickRfl

#kb_checks K10084b include_bytes "data/K10084b.meta" 2069 15788974455626622437 0

#kb_cert CFSG.KBRoute.K10084b T1 K10084b include_bytes "data/K10084b.meta" 2069 15788974455626622437 CFSG.KBRoute.K10084b.rels

theorem CFSG.KBRoute.K10084b.t1 : CFSG.KBRoute.K10084b.T1.ok = true := by kb_assemble K10084b

theorem CFSG.KBFact.K10084b :
    CFSG.Certificates.KB.TableFact 2 CFSG.KBRoute.K10084b.rels CFSG.KBRoute.K10084b.T1.words 6048 :=
  CFSG.Certificates.KB.TableFact.intro CFSG.KBRoute.K10084b.t1 CFSG.KBRoute.K10084b.top

#kc_repo #kc_blocked_root CFSG.KBData.K10084c.F "Certificates/Kernel/Co2Smith/data/K10084c.F.bin" 12 6 18446744073709551615 761664 6365965502928192294
#kc_repo #kc_blocked_root CFSG.KBData.K10084c.D "Certificates/Kernel/Co2Smith/data/K10084c.D.bin" 12 4 65535 50320 12993819944473258263
#kc_repo #kc_items_root CFSG.KBData.K10084c.Wd "Certificates/Kernel/Co2Smith/data/K10084c.Wd.items" 68502 18038928933385658272
#kc_repo #kc_items_root CFSG.KBData.K10084c.Wd2 "Certificates/Kernel/Co2Smith/data/K10084c.Wd2.items" 110266 7644818884879144947
#kc_repo #kc_items_root CFSG.KBData.K10084c.R "Certificates/Kernel/Co2Smith/data/K10084c.R.items" 4616 8673485228574965019
#kc_repo #kc_items_root CFSG.KBData.K10084c.S "Certificates/Kernel/Co2Smith/data/K10084c.S.items" 16 11195056550565907830
#kc_repo #kc_list_root CFSG.KBData.K10084c.wl0 "Certificates/Kernel/Co2Smith/data/K10084c.wl0.items" 1 1316031 9097483295556726123
#kc_repo #kc_list_root CFSG.KBData.K10084c.cv0 "Certificates/Kernel/Co2Smith/data/K10084c.cv0.items" 1 17426 4422913293571274500

#kb_table CFSG.KBRoute.K10084c T1 K10084c include_bytes "data/K10084c.meta" 9049 17618135647787881860 578437695752307201 CFSG.KBRoute.K10084c.rels "7 8"

theorem CFSG.KBRoute.K10084c.top :
    CFSG.Certificates.KB.topOk CFSG.KBRoute.K10084c.T1.amap (nat_lit 8) = true := by
  quickRfl

#kb_checks K10084c include_bytes "data/K10084c.meta" 9049 17618135647787881860 0
#kb_checks K10084c include_bytes "data/K10084c.meta" 9049 17618135647787881860 1

#kb_cert CFSG.KBRoute.K10084c T1 K10084c include_bytes "data/K10084c.meta" 9049 17618135647787881860 CFSG.KBRoute.K10084c.rels

theorem CFSG.KBRoute.K10084c.t1 : CFSG.KBRoute.K10084c.T1.ok = true := by kb_assemble K10084c

theorem CFSG.KBFact.K10084c :
    CFSG.Certificates.KB.TableFact 8 CFSG.KBRoute.K10084c.rels CFSG.KBRoute.K10084c.T1.words 480 :=
  CFSG.Certificates.KB.TableFact.intro CFSG.KBRoute.K10084c.t1 CFSG.KBRoute.K10084c.top

#kc_repo #kc_blocked_root CFSG.KBData.K10084d.F "Certificates/Kernel/Co2Smith/data/K10084d.F.bin" 12 6 18446744073709551615 112176 4619891767181402639
#kc_repo #kc_blocked_root CFSG.KBData.K10084d.D "Certificates/Kernel/Co2Smith/data/K10084d.D.bin" 12 4 65535 13668 3148632816485055379
#kc_repo #kc_items_root CFSG.KBData.K10084d.Wd "Certificates/Kernel/Co2Smith/data/K10084d.Wd.items" 5497 8666132328059856929
#kc_repo #kc_items_root CFSG.KBData.K10084d.Wd2 "Certificates/Kernel/Co2Smith/data/K10084d.Wd2.items" 9912 6083579588785286266
#kc_repo #kc_items_root CFSG.KBData.K10084d.R "Certificates/Kernel/Co2Smith/data/K10084d.R.items" 370 7418354648296984549
#kc_repo #kc_items_root CFSG.KBData.K10084d.S "Certificates/Kernel/Co2Smith/data/K10084d.S.items" 4 14007230941556241898
#kc_repo #kc_list_root CFSG.KBData.K10084d.wl0 "Certificates/Kernel/Co2Smith/data/K10084d.wl0.items" 1 243966 1613076730057911167
#kc_repo #kc_list_root CFSG.KBData.K10084d.cv0 "Certificates/Kernel/Co2Smith/data/K10084d.cv0.items" 1 47248 8172511790183602103

#kb_table CFSG.KBRoute.K10084d T1 K10084d include_bytes "data/K10084d.meta" 2205 11107975957893315326 513 CFSG.KBRoute.K10084d.rels ""

theorem CFSG.KBRoute.K10084d.top :
    CFSG.Certificates.KB.topOk CFSG.KBRoute.K10084d.T1.amap (nat_lit 2) = true := by
  quickRfl

#kb_checks K10084d include_bytes "data/K10084d.meta" 2205 11107975957893315326 0

#kb_cert CFSG.KBRoute.K10084d T1 K10084d include_bytes "data/K10084d.meta" 2205 11107975957893315326 CFSG.KBRoute.K10084d.rels

theorem CFSG.KBRoute.K10084d.t1 : CFSG.KBRoute.K10084d.T1.ok = true := by kb_assemble K10084d

theorem CFSG.KBFact.K10084d :
    CFSG.Certificates.KB.TableFact 2 CFSG.KBRoute.K10084d.rels CFSG.KBRoute.K10084d.T1.words 6048 :=
  CFSG.Certificates.KB.TableFact.intro CFSG.KBRoute.K10084d.t1 CFSG.KBRoute.K10084d.top

end
