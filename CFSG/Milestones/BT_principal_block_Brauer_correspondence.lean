module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem

public section

universe u v w

namespace CFSG.BrauerThirdMainTheorem

open CFSG in
theorem _root_.CFSG.Milestones.brauer_third_main_theorem (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (hpm : (p : BlocksAlgInt) ∈ m)
    (G : Type) [Group G] [Finite G] (P H : Subgroup G) (hP : IsPGroup p P)
    (hPH : P ≤ H) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (β : Set (H → ℂ)) (hβ : BlocksIsBlock m H β) :
    BlocksBrauerCorr m P H β (BlocksPrincipalBlock m G) ↔ β = BlocksPrincipalBlock m H :=
  _root_.CFSG.BrauerThirdMainTheorem.brauer_third_main_theorem p hp m hm hpm G P H hP hPH hCH hHN β hβ

end CFSG.BrauerThirdMainTheorem
