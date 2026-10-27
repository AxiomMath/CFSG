module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TPtAct
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UGlue1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped commutatorElement
open CFSG.Quasithin.H13.L828T

section Mod1

variable {G : Type} [Group G] [Finite G] {T L I H : Subgroup G} {h : G} {k : ℕ}
  [IsMulCommutative ↥(fsuV T I)]

theorem ob5_centralAbelian (c : S828Ctx T L I H h k) :
    PtActCentralAbelian (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82U (fsuV T I) h) := by
  have S := ob5_setup_of_c c
  exact ⟨fun u hu p hp => S.hUc u hu p (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hp),
    fun p hp q hq => c.hP2 p hp q hq⟩

theorem ob5_ptActSetup (c : S828Ctx T L I H h k) :
    PtActSetup (fsuV T I) (ch82B (fsuV T I) h) (ch82U (fsuV T I) h)
      (pCoreOf 2 (ch82I (fsuV T I) h)) (ch82A (fsuV T I) h) h := by
  have S := ob5_setup_of_c c
  refine
    { hBV := fun x hx => ((S.hBdef x).mp hx).1
      hBP := fun x hx => ((S.hBdef x).mp hx).2
      hAP := fun x hx => ((S.hAdef x).mp hx).2
      hUA := fun u hu => (S.hAdef u).mpr ⟨((S.hU u).mp hu).2, ((S.hBdef u).mp (S.hUB u hu)).2⟩
      hPeq := c.hPeq
      hhU := fun u hu => S.hUc u hu h c.hhI
      hhB := fun b hb => S.hhB b hb
      hhA := fun a ha => S.hhA a ha
      hAB := fun x hx => (S.hU x).mpr
        ⟨((S.hBdef x).mp (Subgroup.mem_inf.mp hx).2).1, ((S.hAdef x).mp (Subgroup.mem_inf.mp hx).1).1⟩ }

end Mod1

end CFSG.Quasithin.H13
