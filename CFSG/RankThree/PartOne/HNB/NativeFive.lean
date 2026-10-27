module

public import CFSG.RankThree.PartOne.HNB.NativeFinal

public section

namespace CFSG.RankThree.PartOne.HNB

open CFSG.Sporadic.HNSchreier
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem hnNativeFive_holds :
    HNNativeFive := by
  have hN : NativeData (Carrier .HN) :=
    nativeData_of_mulEquiv (M := Carrier .HN) (N := JH) hnEquivJ nativeData_JH
  have hs : IsSimpleGroup (Carrier .HN) := fam_hn_certified_simplicity.2
  have hN' := hN
  obtain ⟨_, _, K, _, -, -, -, -, -, ⟨a, b, hab⟩, -⟩ := hN'
  exact ⟨hs, ⟨(a : Carrier .HN), (b : Carrier .HN), fun h => hab (Subtype.ext h)⟩, hN⟩

end CFSG.RankThree.PartOne.HNB
