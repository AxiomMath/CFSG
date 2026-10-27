module

public import Certificates.Data.CFSGNative.AS91.M24Fuse

public section

namespace CFSG.KC.M24G

@[expose] def laneP (c j : Nat) : Nat := c / 32 ^ (23 - j) % 32

@[expose] def mulGoP (a : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, b => mulGoP a n (b / 32) * 32 + laneP a (b % 32)

@[expose] def mulP (a b : Nat) : Nat := mulGoP a 24 b

@[expose] def conjP (p : Nat × Nat) (x : Nat) : Nat := mulP p.1 (mulP x p.2)

@[expose] def fusePairsP : List (Nat × Nat) :=
  [(130618774265195527788604973352306154, 130618774265195527788604973352306154),
    (136564164338441043102435244607166003, 766391294027834038598208565066323179),
    (766391294027834038598208565066323179, 136564164338441043102435244607166003)]

@[expose] def fuseStepsP : List (Nat → Nat) := fusePairsP.map conjP

@[expose] def fusePiAP : Nat := 1383171691800334295666612796838646

@[expose] def fusePiBP : Nat := 41662807927711450695705460877286068

end CFSG.KC.M24G
