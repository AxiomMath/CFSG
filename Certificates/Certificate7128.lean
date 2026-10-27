module

public import CFSG.Quasithin.Background.E2TwoProofSporJ1Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.Sporadic.J1.Setup
public import Certificates.Certificate3119
import Certificates.Kernel.J1Dc.Final

public section

namespace Certificates

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.E2P.SporB.J1Lat CFSG.Sporadic.J1 in
theorem certificate7128 : ∀ (Z : Subgroup CFSG.Sporadic.J1.J),
    Subgroup.closure {x | x ∈ j1Words.map (wordElt (a : CFSG.Sporadic.J1.J) (b : CFSG.Sporadic.J1.J))} ≤ Z →
      (Nat.card Z = 168 → Z ≤ Subgroup.normalizer
        ((Subgroup.closure {x | x ∈ j1Words.map (wordElt (a : CFSG.Sporadic.J1.J) (b : CFSG.Sporadic.J1.J))} : Subgroup CFSG.Sporadic.J1.J) : Set CFSG.Sporadic.J1.J)) ∧
      (Nat.card Z = 120 → ∃ u ∈ Subgroup.closure {x | x ∈ j1Words.map (wordElt (a : CFSG.Sporadic.J1.J) (b : CFSG.Sporadic.J1.J))},
        orderOf u = 2 ∧ Z ≤ Subgroup.centralizer ({u} : Set CFSG.Sporadic.J1.J)) :=
  fun Z hZ => CFSG.KD.J1Dc.j1K_facts Z hZ

end Certificates
