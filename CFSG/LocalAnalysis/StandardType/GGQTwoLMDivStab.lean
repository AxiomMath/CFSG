module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivStabBound
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivStabQm

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMSkel_suFull_stabDirectL {G : Type}
    [Group G] [Finite G] {B Bs L : Subgroup G}
    {x : G} {D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m : ℕ}
    (F : QTwoFrame m (QTwoQm m) ↥(sumZero m 3) Bs L x) (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hrt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hFrameL : QTwoFrameL 3 B Bs x L D J)
    (hFm : hFrameL.m = m) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hV : IsQmModel m (QTwoQm m) F.permV) (hVT : IsAugModel m ↥(sumZero m 3) F.permVT) :
    Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, F.hx⟩ = ⟨x, F.hx⟩} ≤
        2 * m.factorial ∧
      DirectP3At 3 Bs L x F.hx :=
  qTwoLMDivStab_stabDirect_of_rigid F hG hBs hL hrt hFrameL hFm hm h3 hV hVT
    fun _ hU hc _ hψ hfix => qTwoLMDivStab_qm_rigid (by omega) hV hU hc hψ hfix

end CFSG.StandardType.QTwo

end
