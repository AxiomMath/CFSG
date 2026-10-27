
module

public import Certificates.Data.Kernel.PermCent.L34MTwin
public import CFSG.GH74.Uniqueness.SU.KI1r4L34ModelInputs

public section

namespace CFSG.Certificates.Kernel.PkCV.L34Mod

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def bfsC (gens : List (CV 42)) :
    Nat → List (CV 42) → List (CV 42) → List (CV 42)
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | n + 1, seen, g :: rest =>
    let new := gens.foldl (fun acc s =>
      let h := g * s
      if h ∈ seen ∨ h ∈ acc then acc else acc ++ [h]) []
    bfsC gens n (seen ++ new) (rest ++ new)

@[expose] noncomputable def gS : List (CV 42) := s0gens.map cOf

@[expose] noncomputable def sC : List (CV 42) := bfsC gS 200 [1] [1]

@[expose] noncomputable def gA : List (CV 42) := [PA, PB, sg0, sg1, sg2].map cOf

@[expose] noncomputable def modelC (LA LP S G : List (CV 42)) : Bool :=
  LA.all fun g =>
    (!(G.all fun s => eq22C g s s g) || decide (g ∈ S)) &&
      (!powOneC g 2 || siftC QP g 0 ||
        !(G.all fun s => decide (g * s * g⁻¹ ∈ S)) ||
        !decide (9 ∣ (LP.filter fun h => eq22C h g g h).length) ||
        gA.all fun a => siftC QP (a * g * a⁻¹ * g⁻¹) 0)

end CFSG.Certificates.Kernel.PkCV.L34Mod

end
