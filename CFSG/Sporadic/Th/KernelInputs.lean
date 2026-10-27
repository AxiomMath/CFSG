
module


public import CFSG.Sporadic.Th.ChainBase1
public import CFSG.Sporadic.Th.Max3.AllConjBase1
public import CFSG.Sporadic.ThSchreier.Row

public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier TauCeti Pointwise

@[expose] noncomputable def fusionConj (w : List ℕ) (r : J) : J :=
  ((Max3.AllConj.abProd w)⁻¹ * r * Max3.AllConj.abProd w * a) ^ 9 * (Max3.AllConj.abProd w)⁻¹

@[expose] noncomputable def genPair (c : J) : Set J :=
  {Max3.x * (c⁻¹ * (Max3.x * c)), Max3.y * (c⁻¹ * (Max3.y * c))}

@[expose] def GenFact (w : List ℕ) (r : J) : Prop :=
  fusionConj w r * r * (fusionConj w r)⁻¹ = a ∧
    a ∈ Subgroup.closure (genPair (fusionConj w r)) ∧ b ∈ Subgroup.closure (genPair (fusionConj w r))

structure KernelFacts : Prop where
  finite : Finite P
  card_le : Nat.card P ≤ thOrder
  dvd2 : 2 ^ 15 ∣ Nat.card J
  dvd3 : 3 ^ 10 ∣ Nat.card J
  dvd5 : 5 ^ 3 ∣ Nat.card J
  dvd7 : 7 ^ 2 ∣ Nat.card J
  dvd13 : 13 ∣ Nat.card J
  dvd19 : 19 ∣ Nat.card J
  dvd31 : 31 ∣ Nat.card J
  ab19 : (a * b) ^ 19 = 1
  fwd : ∃ ψ : P →* J, (∀ i < 7, ψ (gen i) ∈ H ∧ ψ (gen i) • Wset = Wset) ∧
    ψ (gen 0) ^ 2 = 1 ∧ a ∈ ψ.range ∧ b ∈ ψ.range
  x_fix : xJ • Wset = Wset
  y_fix : yJ • Wset = Wset
  b_moves : b • Wset ≠ Wset
  dce : DceFacts
  gen0 : GenFact fusionWord0' (Max3.q 0)
  gen1 : GenFact fusionWord1' Max3.x

end CFSG.Sporadic.Th.Kernel
