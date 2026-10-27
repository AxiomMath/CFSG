module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParFact
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabD
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem psl34_card_normalizer_sylow {K : Type} [Group K] [Finite K] (hK : IsPSL 3 2 2 K)
    (T : Subgroup K) (hT : IsSylowTwoOf T ⊤) :
    Nat.card ↥(Subgroup.normalizer (T : Set K)) = 192 := by
  have hX : CFSG.Blueprint.LieModel K .PSL 3 2 2 := Or.inl ⟨by decide, hK⟩
  obtain ⟨k, _, hk, e, he⟩ := CFSG.Quasithin.H13.exists_mulEquiv_sylow_eq hX hT
  have : Finite k :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hk
  have hN := CFSG.GH74.QTGen4.DSGen4.L34.card_normalizer_U (F := k) hk
  rw [← Subgroup.card_map_of_injective (K := Subgroup.normalizer (T : Set K))
      (f := e.toMonoidHom) e.injective, Subgroup.map_equiv_normalizer_eq, he]
  exact hN

end CFSG.Quasithin.H13.S126P31
