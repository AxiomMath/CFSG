module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFive_four_le_finrank
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    4 ≤ Module.finrank (ZMod p) V := by
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hcfg.1
  have hp : p.Prime := hβ.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
  have hBmax : LargeEvenIsBmax p B := hS.1
  have hp4B : p ^ 4 ≤ Nat.card B := pow_four_le_card_of_bmax hp hBmax h4
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  have : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hcard : Nat.card Bs = Nat.card V := Nat.card_congr ι.toEquiv
  have hfin : p ^ Module.finrank (ZMod p) V = Nat.card V :=
    FiniteField.pow_finrank_eq_natCard p V
  have hle : p ^ 4 ≤ p ^ Module.finrank (ZMod p) V :=
    calc p ^ 4 ≤ Nat.card B := hp4B
      _ ≤ Nat.card Bs := hBBs
      _ = Nat.card V := hcard
      _ = p ^ Module.finrank (ZMod p) V := hfin.symm
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hle

end CFSG.StandardType

end
