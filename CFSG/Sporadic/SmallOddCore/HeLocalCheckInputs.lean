module

public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def heOmega0 : Array Nat :=
  #[15, 50, 76, 120, 311, 414, 425, 622, 648, 693, 825, 867, 935, 983, 1189, 1534, 1560, 1654, 2035,
    2036, 2115, 2126, 2204, 2276, 2639, 2691, 2761, 2990, 3044, 3068, 3096, 3234, 3292, 3570, 3600,
    3754, 3776, 3801, 3962, 4043, 4060, 4212, 4260, 4274, 4402, 4523, 4633, 4666, 4679, 4747, 4891,
    4938, 4941, 4998, 5009, 5020, 5040, 5082, 5114, 5177, 5242, 5256, 5275, 5476, 5607, 5639, 5730,
    5757, 5884, 5927, 6296, 6391, 6403, 6458, 6473, 6539, 6581, 6744, 7147, 7354, 7358, 7369, 7386,
    7504, 7594, 7684, 7698, 7789, 7805, 7844, 7864, 7878, 7920, 7935, 7960, 7982, 7989, 8024, 8068,
    8088, 8101, 8111, 8228, 8318, 8324]

@[expose] def heKGens : Array Tab :=
  Array.ofFn (n := 9) fun j => restrictArr heOmega0.toList (heInnerC0 j.val)

@[expose] def heKInvs : Array Tab := heKGens.map (invTab 105)

@[expose] def heDWords : List (List Nat) := [[3, 1], [4, 1, 4, 1], [4, 3], [5, 3], [8, 4]]

@[expose] def heDGens : Array Tab :=
  Array.ofFn (n := 5) fun j => wordTabS 105 heKGens (heDWords.getD j.val [])

@[expose] def heDInvs : Array Tab := heDGens.map (invTab 105)

@[expose] def heDClassWords : List (List Nat) :=
  [[], [1], [2, 0], [4, 3], [4, 2, 1], [0], [4, 3, 0], [3, 4, 1], [4, 0], [4, 0, 0]]

@[expose] def heDClassSizes : List Nat := [1, 315, 1260, 1260, 1260, 2240, 2880, 2880, 4032, 4032]

@[expose] def heKEnum : Enum := enumBFS 105 heKGens 40320

@[expose] def heDEnum : Enum := enumBFS 105 heDGens 20160

@[expose] def heDOrbits : Array Enum :=
  Array.ofFn (n := 10) fun l => orbitBFS 105 heDGens heDInvs
    (wordTabS 105 heDGens (heDClassWords.getD l.val [])) 5000

end CFSG.Sporadic.SmallOddCore
