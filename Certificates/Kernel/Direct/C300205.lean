module

public import CFSG.Quasithin.Background.Harris.R1.D4VertCheck
public import CFSG.Quasithin.Background.Harris.R1.D4VertWords
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.IdxChunks

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelDirect.C300205

open CFSG.Quasithin.Background.Harris.R1.D4Vert CFSG.LargeExtraspecial.S63

theorem gensInvolOK_eq_true : gensInvolOK () = true := by
  decide +kernel

@[expose] noncomputable def hRelsPiece (j : Nat) : Bool :=
  ((hRels.drop (j * 2)).take 2).all fun r => wordR d4Gens (substWord hWords r) == oneR

#kc_each hRelsPiece 0 7

@[expose] noncomputable def nRelsPiece (j : Nat) : Bool :=
  ((nRels.drop (j * 2)).take 2).all fun r => wordR d4Gens (substWord nWords r) == oneR

#kc_each nRelsPiece 0 14

theorem relsHold_h : relsHold hWords hRels = true := by
  refine CFSG.KC.IdxChunks.all_chunks_of _ 2 7 hRels (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact hRelsPiece0
  | 1, _ => exact hRelsPiece1
  | 2, _ => exact hRelsPiece2
  | 3, _ => exact hRelsPiece3
  | 4, _ => exact hRelsPiece4
  | 5, _ => exact hRelsPiece5
  | 6, _ => exact hRelsPiece6
  | k + 7, h => exact absurd h (by omega)

theorem relsHold_n : relsHold nWords nRels = true := by
  refine CFSG.KC.IdxChunks.all_chunks_of _ 2 14 nRels (by decide +kernel) fun j hj => ?_
  match j, hj with
  | 0, _ => exact nRelsPiece0
  | 1, _ => exact nRelsPiece1
  | 2, _ => exact nRelsPiece2
  | 3, _ => exact nRelsPiece3
  | 4, _ => exact nRelsPiece4
  | 5, _ => exact nRelsPiece5
  | 6, _ => exact nRelsPiece6
  | 7, _ => exact nRelsPiece7
  | 8, _ => exact nRelsPiece8
  | 9, _ => exact nRelsPiece9
  | 10, _ => exact nRelsPiece10
  | 11, _ => exact nRelsPiece11
  | 12, _ => exact nRelsPiece12
  | 13, _ => exact nRelsPiece13
  | k + 14, h => exact absurd h (by omega)

end CertificateChecks.KernelDirect.C300205
