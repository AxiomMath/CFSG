module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.IrrSec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26Bridge
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Assembly2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Hss32Final

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem f53DichAt2_of_frontier4 (hA : F53Amalgam H M S) (hres : Hss26ResidualAt H M)
    (h33 : Hss33At H M) (h34 : Hss34At H M) (h35o : Hss35OrthAt H M) (h36n : Hss36NatAt H M)
    (hgt : Hss42CardGtAt H M) (h43 : Hss43At H M) : F53DichAt2 H M :=
  have h26 := hss26AAt_of_residual hA hres
  have h41 := hss41At_of_hss26A hA h26
  f53DichAt2_of_steps hA (hss28At_of_hss26A hA h26) (hss32At_of_hss26A_only hA h26) h33 h34
    (hss36At_of hA h34 h36n h35o) h41
    (hss42At_of_hss113c hA h41 (hss113cAt_of hA)
      (hss42CommAt_of_gt hA h41 EmptyFaithful.Stellmacher.OrdinaryProofs.irrSec hgt)) h43

end F53.Stellmacher

@[expose] def F53.Stellmacher.Hss26Residual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S →
    F53.Stellmacher.Hss26ResidualAt H M

theorem F53.Stellmacher.f53Dichotomy2_of_frontier4 (hres : F53.Stellmacher.Hss26Residual)
    (h33 : F53.Stellmacher.Hss33) (h34 : F53.Stellmacher.Hss34)
    (h35o : F53.Stellmacher.Hss35Orth) (h36n : F53.Stellmacher.Hss36Nat)
    (hgt : F53.Stellmacher.Hss42CardGt) (h43 : F53.Stellmacher.Hss43) : F53Dichotomy2 := by
  intro G _ _ H M S hA
  exact F53.Stellmacher.f53DichAt2_of_frontier4 hA (hres G H M S hA) (h33 G H M S hA)
    (h34 G H M S hA) (h35o G H M S hA) (h36n G H M S hA) (hgt G H M S hA) (h43 G H M S hA)

end CFSG.Quasithin
