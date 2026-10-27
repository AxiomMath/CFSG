module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Syl
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Order
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Close

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Dickson.Sec6

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem three_pow_nine_dvd_ordTwistedE6_two : 3 ^ 9 ∣ ordTwistedE6 2 := by
  decide

theorem three_pow_nine_dvd_ordD_four_eight : 3 ^ 9 ∣ ordD 4 (2 ^ 3) := by
  decide

theorem three_pow_nine_dvd_card_of_isCatalogLieIso_d48 {Q : Type*} [Group Q]
    (hQ : IsCatalogLieIso Q IsD48Index) : 3 ^ 9 ∣ Nat.card Q := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hQ
  cases d with
  | D r q =>
    obtain ⟨rfl, hp, he⟩ := hd
    rw [Nat.card_congr e.toEquiv,
      CFSG.AGLEmbedding.card_catGroup_D_even (d := ⟨.D 4 q, hv⟩) hp rfl, he]
    exact three_pow_nine_dvd_ordD_four_eight
  | _ => exact hd.elim

theorem card_eq_ordTwistedE6_two_of_isCatalogLieIso {Q : Type} [Group Q]
    (hQ : IsCatalogLieIso Q IsTwE62Index) : Nat.card Q = ordTwistedE6 2 := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hQ
  cases d with
  | twistedE6 q =>
    obtain ⟨K, fK, σ, hK, hσ, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    have hq : q.p ^ q.exponent = 2 ^ 1 := by rw [hd.1, hd.2]
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    rw [Nat.card_congr (e.trans eC).toEquiv,
      CFSG.LieType.SeitzGeneration.ExcHighThree.card_twistedE6RootGroup_eq (ℓ := 2) (f := 1)
        Nat.prime_two le_rfl σ (by rw [hK, hq]) (fun c => by rw [hσ, hq])]
    norm_num
  | _ => exact hd.elim

theorem three_pow_nine_dvd_card_of_isCatalogLieIso_twE62 {Q : Type} [Group Q]
    (hQ : IsCatalogLieIso Q IsTwE62Index) : 3 ^ 9 ∣ Nat.card Q := by
  rw [card_eq_ordTwistedE6_two_of_isCatalogLieIso hQ]
  exact three_pow_nine_dvd_ordTwistedE6_two

end CFSG.StandardType.FrameRoute.FS81

end
