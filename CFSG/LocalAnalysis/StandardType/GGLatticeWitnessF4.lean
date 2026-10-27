module

public import CFSG.LocalAnalysis.StandardType.GGLatticeWitness

public section

namespace CFSG.StandardType

@[expose] def lwf_F4Rcodes : List ℕ :=
  [25926, 30022, 30278, 30294, 30310, 30566, 34662, 30295, 30311, 30567, 34663, 30583, 34679,
    34935, 34951, 30312, 30568, 34664, 30584, 34680, 34936, 30600, 34696, 30856, 39048, 35208,
    39304, 34968, 35224, 39320, 35240, 39336, 39592, 34953, 34969, 35225, 39321, 35241, 39337,
    39593, 39609, 35242, 39338, 39594, 39610, 39626, 39882, 43978]

@[expose] def lwf_F4R : List (List ℤ) := lwf_F4Rcodes.map (ggLWdecode 4)

theorem lwf_F4R_closed : ggLWclosed (ggLWmatC CartanMatrix.F₄) 4 lwf_F4R = true := by
  decide +kernel

@[expose] def lwf_F4TRcodes : List ℕ :=
  [25686, 25687, 25703, 25959, 30055, 26215, 30311, 34407, 26231, 30327, 34423, 30583, 34679,
    34935, 34951, 26232, 30328, 34424, 30584, 34680, 34936, 30600, 34696, 30856, 39048, 35208,
    39304, 34968, 35224, 39320, 35480, 39576, 43672, 34953, 34969, 35225, 39321, 35481, 39577,
    43673, 35497, 39593, 43689, 39849, 43945, 44201, 44217, 44218]

@[expose] def lwf_F4TR : List (List ℤ) := lwf_F4TRcodes.map (ggLWdecode 4)

theorem lwf_F4TR_closed :
    ggLWclosed (ggLWmatC (Matrix.transpose CartanMatrix.F₄)) 4 lwf_F4TR = true := by
  decide +kernel

theorem lwf_cell_F4_k1 :
    ggLWdata (ggLWmat (ggAttachCartan CartanMatrix.F₄ (1 : Fin 4))) 4 lwf_F4R [4, 2] 1
      [1, 4, 3, 1, 2, 1] 0 = true := by
  decide +kernel

theorem lwf_cell_F4_k2 :
    ggLWdata (ggLWmat (ggAttachCartan CartanMatrix.F₄ (2 : Fin 4))) 4 lwf_F4R [4, 3] 2
      [4, 2, 1, 2, 4, 0, 1] 2 = true := by
  decide +kernel

theorem lwf_cell_F4T_k1 :
    ggLWdata (ggLWmat (ggAttachCartan (Matrix.transpose CartanMatrix.F₄) (1 : Fin 4))) 4 lwf_F4TR
      [4, 2] 1 [1, 4, 3, 1, 2, 1] 0 = true := by
  decide +kernel

theorem lwf_cell_F4T_k2 :
    ggLWdata (ggLWmat (ggAttachCartan (Matrix.transpose CartanMatrix.F₄) (2 : Fin 4))) 4 lwf_F4TR
      [4, 3] 2 [4, 2, 1, 2, 4, 0, 1] 2 = true := by
  decide +kernel

end CFSG.StandardType
