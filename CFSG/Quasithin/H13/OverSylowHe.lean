module

public import CFSG.Quasithin.H13.OverSylowDc
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovP3
public import Certificates.Certificate7030

public section

namespace CFSG.Quasithin.H13.LocDbl.OverHe

open CFSG.Blueprint CFSG.Sporadic.He CFSG.QuasithinUnique

theorem overSylow_J :
    ∀ X S : Subgroup J, Nat.card S = 2 ^ 10 → S ≤ X → 5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X → False :=
  Certificates.certificate7030.2.2

theorem overSylow2HeCov_holds :
    CFSG.Quasithin.H13.OverSylow2HeCov := by
  intro X S _ hS1024 hSX h5 h9
  have key := no_overgroup_transport (A := CFSG.Blueprint.NativeSporadic.He) (B := ↥J) heEquivJ
    overSylow_J
  exact (key X S hS1024 hSX h5 h9).elim

end CFSG.Quasithin.H13.LocDbl.OverHe
