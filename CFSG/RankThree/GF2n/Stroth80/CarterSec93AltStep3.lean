module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93XH
public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeL123
public import CFSG.RankThree.GF2n.Stroth80.Sec94FreeL4
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAbsorb
public import CFSG.RankThree.GF2n.Stroth80.CarterSec93CNInv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem Vt_CN_eq_of_mem_Z0 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G}
    (hcfg : HS9.Cfg93c hc n t r Z0 h) {s : G} (hsZ : s ∈ Z0) (hsQ : s ∉ Q) :
    Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t ∧ hc.CN s = hc.CN t := by
  have hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t :=
    Rt_eq_of_mem_Z091 h34 h311a h311bComm h312b hcfg.hs hcfg.hr hcfg.hZ0 hsZ hsQ
  have hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t :=
    S94F.Vt_eq_of_mem_Z0 h34 h311a h311bComm h312b
      (CFSG.RankThree.GF2n.Stroth80.step94Point_holds h34) hcfg.hs hcfg.hZ0 hsZ hsQ
  exact ⟨hV, CFSG.RankThree.GF2n.Stroth80.CN_eq_of_rt_vt hc hc hR hV⟩

theorem step93L2AltXH_CN_inv_of_cfg (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G}
    (hcfg : HS9.Cfg93c hc n t r Z0 h) {g : G} (hgM : g ∈ M)
    (hgL : conjSubgroup g (LB M Q B) = LB M Q B) :
    conjSubgroup g (LB M Q B ⊓ hc.CN t) = LB M Q B ⊓ hc.CN t :=
  step93L2AltXH_CN_inv h34 h311a h311bComm h312b hcfg.hs hcfg.hr hcfg.hZ0 hcfg.hsc
    (fun s hsZ hsQ => (Vt_CN_eq_of_mem_Z0 h34 h311a h311bComm h312b hcfg hsZ hsQ).1)
    hgM hgL

end HS9

end CFSG.RankThree.GF2n.Stroth80
