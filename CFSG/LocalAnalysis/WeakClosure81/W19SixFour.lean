module

public import CFSG.LocalAnalysis.WeakClosure81.W19SixFourE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem card_inf_J193 (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V')
    {g : G} {K : Subgroup G} (hc : Conf196 D V X g K) :
    Nat.card ↥(X ⊓ J193 D X (conjSubgroup V g) K) = p :=
  le_antisymm
    (card_le_of_tie h763 (hc.tieData c h162) c.hyp.prime c.hyp.odd inf_le_right
      (fun x hx => c.hyp.exponent x hx.1) (hc.A_le_normalizer_sup c))
    (hc.p_le_card_inf_J193 c)

theorem sup_eq_eGen_sup (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V') :
    E1.eGen 1 (X ⊔ D.T) D.T (E3.gammaSet V 0 (X ⊔ D.T)) ⊔ D.T = X ⊔ D.T :=
  c.sup_eq_eGen_sup_of_card fun _ _ hc => c.card_inf_J193 h162 h763 hc

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
