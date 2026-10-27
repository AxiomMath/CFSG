module

public import CFSG.Quasithin.MS93.S38EPU
public import CFSG.Quasithin.MS93.S38ESecMod

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.Open
open scoped commutatorElement

@[expose] def D6Case : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    T ⊓ Subgroup.centralizer (Z0q M T : Set G) = pCoreOf 2 M → ⁅Xq M, L⁆ ≤ Uq M T L →
    (IsHatA6U M T L ∨ IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1) →
    ¬ IsSL3U M T L → ¬ IsSp4U M T L →
    ∀ (hD : XOffData M T) (hCU : XOffCentU M T L),
    (∀ F : Subgroup G, IsXOff M T F → (pCoreOf 2 M).relIndex F ≤ 4) →
    ∀ (hb : critDist (puAmalgam h.le) = 4)
      (hstar : ∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
        stab _ (geo _ ε ε' 2) ≤ Subgroup.normalizer
          ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) ∧
        puTrans h.le L (geo _ ε ε' 2) ≤ Subgroup.centralizer
          ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal))
      (h8 : ∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
        ¬ Vv (puAmalgam h.le) ε ≤ Qv (puAmalgam h.le) (geo _ ε' ε 2))
      (α' : Vtx (puAmalgam h.le)) (hc : IsCritical _ (baseA _) α')
      (hgeo : geo _ (baseA _) α' 1 = baseB _)
      (lam : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆ →* ℂˣ)
      (hlam1 : ∀ c : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆,
        (c : (puAmalgam h.le).Universal) ∈
          ⁅⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆, Qv _ (baseB _)⁆ →
          lam c = 1),
      (∃ c : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆,
        (c : (puAmalgam h.le).Universal) ∈
          ⁅⁅Vv (puAmalgam h.le) (baseA _), puTrans h.le L (baseA _)⁆,
            Vv (puAmalgam h.le) (baseA _)⁆ ∧ lam c ≠ 1) →
      AlternatingNatural ((endSetup_base h hD hCU hb hstar h8 hc hgeo).kS lam hlam1) ⊤ ⊥ 6 →
        False

end CFSG.Quasithin.MS93.S38E
