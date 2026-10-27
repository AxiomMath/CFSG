module

public import CFSG.Sporadic.HNSchreier.EmbeddedOrbit
public import CFSG.Sporadic.HNSchreier.PackedOrbitAccess

public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

namespace CFSG.Sporadic.HNSchreier.Native

theorem hnsOrbit_alpha_valid : (hnsOrbitData ()).alpha.valid = true := by decide +kernel
theorem hnsOrbit_beta_valid : (hnsOrbitData ()).beta.valid = true := by decide +kernel

theorem hnsOrbit_alpha_ap (i : Nat) :
    CFSG.Sporadic.Th.Native.ap (hnsOrbit ()).alpha i =
      (UInt32.ofNat ((hnsOrbitData ()).alpha.get i)).toNat :=
  OrbitNats.table_ap _ hnsOrbit_alpha_valid i

theorem hnsOrbit_beta_ap (i : Nat) :
    CFSG.Sporadic.Th.Native.ap (hnsOrbit ()).beta i =
      (UInt32.ofNat ((hnsOrbitData ()).beta.get i)).toNat :=
  OrbitNats.table_ap _ hnsOrbit_beta_valid i

end CFSG.Sporadic.HNSchreier.Native
