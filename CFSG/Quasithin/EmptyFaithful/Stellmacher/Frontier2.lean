module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42B1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42Irred

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Hss42CardGtAt (H M : Subgroup G) : Prop :=
  ∀ α β α' : Geo H M, IsCritData α β α' → vtype α = false →
    (∀ μ : Geo H M, (graph (H ⊔ M) H M).Adj α μ → bMin H M < bAt μ) →
    ⁅Zv α, Zv α'⁆ = ⊥ → 1 < bMin H M → Nat.card (Zv β) = 2

theorem hss42CommAt_of_gt (hA : F53Amalgam H M S) (h41 : Hss41At H M) (hirr : IrrSec)
    (hgt : Hss42CardGtAt H M) : Hss42CommAt H M := by
  intro α β α' hc hα hnb hz
  rcases (bMin_pos hA).lt_or_eq with hb | hb
  · exact isOrthSec_or_isNatSec_of_card_Zv_eq_two hA hα hc.adj
      (h41 α β hc.adj hα hc.bAt_eq (hnb β hc.adj)) (hgt α β α' hc hα hnb hz hb)
  · exact hss42Comm_b_one hA hirr hc hα hz hb.symm

end F53.Stellmacher

@[expose] def F53.Stellmacher.Hss42CardGt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S →
    F53.Stellmacher.Hss42CardGtAt H M

end CFSG.Quasithin
