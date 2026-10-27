module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S15
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S27Twist
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S27Lift
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss113
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.NoA5Transvection
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.TwoEight
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.TwoSeven
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step32

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss28At_of_hss26A (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) : Hss28At H M :=
  hss28At_of_hss26A_of_mod hA h26 (Hss28Mod_of_modPack28 modPack28_holds G H M S hA)

theorem hss27At_of_hss26A (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) : Hss27At H M := by
  have h28 := hss28At_of_hss26A hA h26
  intro hb α β hαβ hα hn
  cases hv : vtype α
  · exact hss27S5At_of hA h26 h28 (hss113cAt_of hA) secLiftFix hb α β hαβ hv hα hn
  · exact hss27S3At_of_hss26A hA h26 h28 hb α β hαβ hv hα hn

theorem hss41At_of_hss26A (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) : Hss41At H M :=
  hss41At_of hA (hss27S5At_of hA h26 (hss28At_of_hss26A hA h26) (hss113cAt_of hA) secLiftFix) hss15

theorem hss32At_of_hss26A (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hdef : Hss32DEFAt H M) : Hss32At H M :=
  hss32At_of_defAt hA (hss27S3At_of_hss26A hA h26 (hss28At_of_hss26A hA h26))
    (hss113aAt_of hA) noA5Transvection_holds hdef

end F53.Stellmacher

end CFSG.Quasithin
