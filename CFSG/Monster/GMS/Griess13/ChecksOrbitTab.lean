module

public import CFSG.Monster.GMS.Griess13.ChecksOrbitInputs
public import CFSG.Monster.GMS.Griess13.OrbTabData

@[expose] public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

@[expose] noncomputable def orbTabR : Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  (OrbTab.cls.toArray, OrbTab.dist.toArray, OrbTab.par.toArray, OrbTab.gen.toArray)

@[expose] noncomputable def orbitClassR (w : Fin 6 → ZMod 3) : ℕ := orbTabR.1[codeOf w]!

@[expose] noncomputable def orbCheckR : Bool :=
  (List.range 729).all fun c => c == 0 ||
    ((orbTabR.1[c]! == 1 || orbTabR.1[c]! == 2 || orbTabR.1[c]! == 3) &&
      (if c == repCode orbTabR.1[c]! then orbTabR.2.1[c]! == 0 else
        decide (0 < orbTabR.2.2.1[c]!) && decide (orbTabR.2.2.1[c]! < 729) &&
        decide (orbTabR.2.2.2[c]! < 2) &&
        stepS orbTabR.2.2.2[c]! orbTabR.2.2.1[c]! == c &&
        orbTabR.1[orbTabR.2.2.1[c]!]! == orbTabR.1[c]! &&
        decide (orbTabR.2.1[orbTabR.2.2.1[c]!]! < orbTabR.2.1[c]!)))

@[expose] noncomputable def orbitIndexR (w : Fin 6 → ZMod 3) : Fin 3 :=
  if orbitClassR w = 1 then 0 else if orbitClassR w = 2 then 1 else 2

end CFSG.Monster.GMS.Griess13.Co1Data
