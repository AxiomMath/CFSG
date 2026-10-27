module

public import Certificates.Data.Kernel.L5.WBfs
public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.GH74.GLS.C3.Layer2.L5C3bInputs

public section

namespace CFSG.KD.L5

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.C3.Layer2.Model

instance : Small 16 := ⟨by decide⟩

@[expose] noncomputable def trC (v : Fin 16) : CV 16 := (tr1L.map cOf).getD v.val 1

@[expose] noncomputable def ovC (s : CV 16) : Bool :=
  v4L.any fun d => (List.finRange 16).all fun i => decide (d i =
    ((List.finRange 16).find? fun j => decide (s * trC i * s⁻¹ = trC j)).getD 0)

@[expose] noncomputable def gC : List (CV 16) := [tr1 1, tr1 2, tr1 4, tr1 8, gS1, gS2].map cOf

@[expose] noncomputable def fixC : List (CV 16) :=
  [tr1 (cHat 1), tr1 (cHat 2), tr1 (cHat 4), tr1 (cHat 8)].map cOf

@[expose] noncomputable def SC : List (CV 16) := (closureList (sh1Gens.map cOf) 12).filter ovC

@[expose] noncomputable def tabC : List (CV 16 × List ℕ) := wBfsTabG gC 12

@[expose] def t1 : List ℕ × List ℕ × List ℕ := ([4, 1], [4], [1, 2])

@[expose] def t2 : List ℕ × List ℕ × List ℕ := ([5], [1, 5], [1, 3])

@[expose] def t3 : List ℕ × List ℕ × List ℕ := ([5, 4], [5], [2, 4])

@[expose] noncomputable def holdsC (imgs : List (CV 16)) (t : List ℕ × List ℕ × List ℕ) : Bool :=
  decide (wval imgs t.2.2 = wval imgs t.1 * wval imgs t.2.1)

@[expose] noncomputable def AC : List (CV 16) := SC.filter fun u => holdsC (fixC ++ [u, 1]) t1

@[expose] noncomputable def BC : List (CV 16) := SC.filter fun u => holdsC (fixC ++ [1, u]) t2

end CFSG.KD.L5

end
