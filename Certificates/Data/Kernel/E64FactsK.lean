module

public import Certificates.Data.Kernel.E64AutK
public import Certificates.Data.E64Facts

public noncomputable section

namespace CFSG.KC.E64FactsK

open CFSG.KC.WrTwin CFSG.KC.E64AutK CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117 Certificates.E64Facts

@[expose] def ptsIn (s : Finset (Fin 7)) : List (Fin 7) :=
  (List.finRange 7).filter fun i => decide (i ∈ s)

@[expose] def memAtK (α : Finset (Fin 7)) (b : Bool) : List (Wr 7) :=
  match ptsIn α with
  | [a₀, a₁, a₂, a₃] => memLC a₀ a₁ a₂ a₃ b
  | _ => []

@[expose] def memSK (ℓ : Finset (Fin 7)) : List (Wr 7) := memAtK ℓᶜ true ++ memAtK ℓᶜ false

@[expose] def centK (ℓ : Finset (Fin 7)) : List (Wr 7) :=
  match ptsIn ℓ with
  | [p, q, r] => centLC p q r (ptsIn ℓᶜ)
  | _ => []

@[expose] def commP (pp x : Nat) (S : List Nat) : Bool :=
  S.all fun s => inModPi pp (pm x s) [pm s x]

@[expose] def centCOK (pp : Nat) (P : List (Nat × Nat)) (V S C : List Nat) : Bool :=
  P.all fun t => !(S.all fun s => samePerm (pm t.1 s) (pm s t.1)) ||
    V.all fun v => !(commP pp (pm v t.1) S) || inModPi pp (pm v t.1) C

end CFSG.KC.E64FactsK

end
