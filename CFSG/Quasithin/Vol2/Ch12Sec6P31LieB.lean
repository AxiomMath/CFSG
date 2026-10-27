module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem psl34_card_aut {K : Type} [Group K] [Finite K]
    (hK : IsPSL 3 2 2 K) : Nat.card (MulAut K) = 241920 := by
  obtain ⟨ε⟩ := CFSG.ComponentClassification.PSL3Four.nonempty_equiv_of_stated K hK
  obtain ⟨e, -, -⟩ := CFSG.ComponentClassification.PSL3Four.full_automorphism_action
  let ψ : MulAut K ≃* ↥CFSG.ComponentClassification.PSL3Four.R :=
    (MulAut.congr ε).trans e.symm
  rw [Nat.card_congr ψ.toEquiv, CFSG.ComponentClassification.PSL3Four.card_R]

end CFSG.Quasithin.H13.S126P31
