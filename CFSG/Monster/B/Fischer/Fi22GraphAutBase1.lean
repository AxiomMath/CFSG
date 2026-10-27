
module


public import CFSG.Monster.B.Fischer.Fi22GraphBound

@[expose] public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates

theorem fi22Graph_adj_inv
    {g : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22P) (x y : Fin 3510) :
    fi22Graph.Adj (g x) (g y) ↔ fi22Graph.Adj x y := by
  rw [← fi22Nbr_adj, ← fi22Nbr_adj, fi22Nbr_inv hg x y]

theorem fi22Graph_adj_zero
    (k : Fin 3510) : fi22Graph.Adj 0 k ↔ k ∈ fi22N0 :=
  (fi22Nbr_adj 0 k).symm.trans (fi22Nbr_zero k)

end CFSG.Monster.B.Fischer
