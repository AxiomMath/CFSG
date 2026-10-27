module

public import CFSG.Quasithin.Vol2.Ch11SecBK4I
public import CFSG.Quasithin.Vol2.Ch11SecBK4E
public import CFSG.Quasithin.Vol2.Ch11SecBK4G
public import CFSG.Quasithin.Vol2.Ch11SecBK4H

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall
open CFSG.Open (quasithinG2 IsElemAbelian)
open scoped IsMulCommutative

theorem factRootInv_holds : FactRootInv := by
  intro G _ _ L V X T n m hV hn hLV hVL hnat hm _ hXN hTS _ hTL x hx hx2 hx1 hmx
  obtain ⟨hc, hnat'⟩ := hnat
  have hG2 : SecA.FactG2DerivedOrder := KGNat.factG2DerivedOrder_holds
  have hxV := hx.2
  have hxL := hXN hx
  have hτ2 : SecA.conjV V x hxV * SecA.conjV V x hxV = 1 := by
    rw [← SecA.conjV_mul]
    exact BK4.conjV_eq_one_of_mem _ (by rwa [← sq])
  rcases hnat' with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    have hk := BK4.kindSL3_of_isCoord hK hf
    have hmn : m = n := by
      rcases hm with ⟨hk', -⟩ | ⟨-, hmn⟩
      · exact (SecA.kind_not_SL3_G2 hG2 hn hk hk').elim
      · exact hmn
    subst hmn
    obtain ⟨g, hg, h1⟩ := BK4.rootInv_sl3 hV hLV hVL hn hK hf hTS hTL hxV hxL hx1 hmx
    exact ⟨2, _, le_rfl, Or.inl ⟨⟨fun h => SecA.kind_not_SL3_Sp4 (by omega) hk h,
      fun h => SecA.kind_not_SL3_G2 hG2 hn hk h⟩, rfl, rfl⟩, g, hg, h1⟩
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
    have hk := BK4.kindSp4_of_isCoord hK hf
    have hmn : m = n := by
      rcases hm with ⟨hk', -⟩ | ⟨-, hmn⟩
      · exact (SecA.kind_not_Sp4_G2 hG2 hn hk hk').elim
      · exact hmn
    subst hmn
    obtain ⟨g, hg, h1⟩ := BK4.rootInv_sp4 hV hLV hVL hn hK hf hTS hTL hxV hxL hx1 hτ2 hmx
    exact ⟨3, _, le_rfl, Or.inr ⟨Or.inl hk, rfl⟩, g, hg, h1⟩
  · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (G2Q8.lmG K) hπ
    have hk := BK4.kindG2_of_isCoord hn hK hf
    have hmn : m = 2 * n := by
      rcases hm with ⟨-, hmn⟩ | ⟨hk', -⟩
      · exact hmn
      · exact (hk' hk).elim
    subst hmn
    obtain ⟨W, hW, g, hg, h1⟩ :=
      BK4.rootInv_g2 hV hLV hVL hn hK hf hTS hTL hxV hxL hx1 hτ2 hmx
    exact ⟨3, W, hW, Or.inr ⟨Or.inr hk, rfl⟩, g, hg, h1⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
