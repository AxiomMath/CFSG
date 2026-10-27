module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AltPermInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic

public section

namespace CFSG.QuasithinUnique.Setup.X3
open Equiv CFSG.QuasithinUnique

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
private theorem card7_h :
    Fintype.card
          {σ : Perm (Fin 7) // σ ∈ relStab blkX7 ∧ σ ∈ relStab blkY7} = 48 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem card8_h :
    Fintype.card
          {σ : Perm (Fin 8) // σ ∈ relStab blkX8 ∧ σ ∈ relStab blkY8} = 128 := by
  decide +kernel

end CFSG.QuasithinUnique.Setup.X3

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X3 in
open Equiv CFSG.QuasithinUnique in
theorem certificate4138 : (Fintype.card
            {σ : Perm (Fin 7) // σ ∈ relStab blkX7 ∧ σ ∈ relStab blkY7} = 48)
    ∧ (Fintype.card
            {σ : Perm (Fin 8) // σ ∈ relStab blkX8 ∧ σ ∈ relStab blkY8} = 128) :=
  ⟨CFSG.QuasithinUnique.Setup.X3.card7_h, CFSG.QuasithinUnique.Setup.X3.card8_h⟩

end Certificates
