module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtB42ListFCtx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtB42ListFTypes
public import CFSG.Quasithin.EmptyFaithful.S151S2

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

theorem input15120B42ListF_holds
    (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hlj : Input15120LJ) (h56 : AsB56) (hcover : AsA36NoOddCover)
    (hG2 : FactG2Cayley) : Input15120B42ListF := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar
  obtain ⟨Y, _, _, ρ, hρ, hker, hY, hl⟩ := B42ListF.star_data h37 h38 hlj h56 hc hchar
  have hq := hc.ctx.qtfe
  have hpcX : CFSG.Open.pCoreOf 2 (L ⊔ s1516 T Z₁) ≠ ⊥ :=
    (quasithinIsLocal_iff_lFamily.mp hc.hL.mem.2).2.2
  have hSQX : SQTKGroup ↥(L ⊔ s1516 T Z₁) :=
    sqtkGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpcX
  have hSQL : SQTKGroup ↥L := B5.sqtk_of_le hSQX le_sup_left
  have hSQ : SQTKGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    InternalSec.sqtkGroup_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)
      hSQL
  have hO2 : CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    Setup.Campbell.pCore_quotient_pCore_eq_bot' 2
  exact B42ListF.list_of_b56 hcover hG2 hc.hL.quasi hSQ hO2 hY ρ hρ hker hl

end CFSG.Quasithin
