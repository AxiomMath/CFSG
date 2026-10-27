module

public import CFSG.RankThree.GF2n.Smith81.S81A5Cent

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

@[expose] noncomputable def tInv1 (K : Type*) [Field K] : GL (Fin 6) K :=
  transvGL K 0 1 (by decide) 1

@[expose] noncomputable def tInv2 (K : Type*) [Field K] : GL (Fin 6) K :=
  tInv1 K * transvGL K 2 3 (by decide) 1

@[expose] noncomputable def tInv3 (K : Type*) [Field K] : GL (Fin 6) K :=
  tInv2 K * transvGL K 4 5 (by decide) 1

end CFSG.RankThree.GF2n.Smith81.A5Cube
