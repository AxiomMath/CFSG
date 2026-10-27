module

public import Certificates.Data.Kernel.B45Ind.Defs
public import Certificates.Data.SmithB45MatIndM24

public section

namespace CFSG.KC.B45Ind

open CFSG.Quasithin.B45Mat.Ind CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

@[expose] def ts24L : List (List ℕ) :=
  (m24CosC.map decW).map (wordL bridgePAImage bridgePBImage)

@[expose] def gen24L (z : Bool) : List ℕ :=
  if z then bridgePBImage else bridgePAImage

@[expose] def k24L (i : ℕ) (z : Bool) : List ℕ :=
  indColsL (m24Xd i) (m24Xc i) ts24L (gen24L z) 0

@[expose] def coset24L : Bool :=
  cosetOKL bridgePAImage bridgePBImage ts24L 24 0

@[expose] def flag24L (i : ℕ) : Bool :=
  flagCore (24 * m24Xd i) (k24L i) (m24P i) (invColsL (24 * m24Xd i) (m24P i)) (m24Ns i)
    fun j => m24Std ((m24Typs i).getD j 0)

end CFSG.KC.B45Ind
