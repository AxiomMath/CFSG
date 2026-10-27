module

public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Def
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Ord
public import CFSG.Quasithin.EmptyFaithful.S151CLJ4Fix
public import CFSG.Quasithin.EmptyFaithful.S151CLDef

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem compListNoJ4_of_local
    (hB42 : Input15120B42List) (hloc : Input15120J4Local) : CompListNoJ4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hJ4
  have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hfix : AutFixOn L (s1516 T Z₁ ⊓ L) := autFixOn_of_isSporadic_j4 hcomp.2.2 hSyl hJ4
  have hcent := s151s_cent_le_mZ hc hcomp hfix
  obtain ⟨K, hKmem, hKchar, hK24, hKsup⟩ := hloc G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hJ4
  have hKM : K ≤ mZ1516 Mc Z₁ := by
    by_contra hnot
    have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
      J4Excl.isQuasisimple_of_isSporadic_m24 hK24
    have hcK : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ K := ⟨hc.ctx, hc.h17, hc.h18, hc.h19, hKmem, hKq, hnot⟩
    exact J4Excl.not_lists_of_isSporadic_m24 hK24 (hB42 G T Mc M Z₁ Z₂ V₁ V₂ K hcK hKchar)
  apply hc.hL.not_le
  rw [← hKsup]
  exact sup_le hKM fun x hx => (hcent hx).1

end CFSG.Quasithin
