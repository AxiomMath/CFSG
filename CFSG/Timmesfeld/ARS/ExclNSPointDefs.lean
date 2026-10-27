module

public import CFSG.Timmesfeld.ARS.ExclNSFrame

public section

namespace CFSG.Timmesfeld.ARS.ExclNS

open CFSG.LieType.Universal CFSG.LieType.Steinberg

@[expose] def PointTypeInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)) (A A₀ : Subgroup G), Sec13 R A A₀ →
    ∀ (F : NSLFrameData (LeviBar R A A₀) (quotClass (levi R A A₀) (leviSet R A A₀)))
      (B : Subgroup G),
      (F.D.cartan = Spin.cartanB F.D.rank ∨ F.D.cartan = Symplectic.cartanC F.D.rank) →
      3 ≤ F.D.rank → LowMember F B →
      (⨆ i, F.H i).map F.Ψ ≤ stabBar R A A₀ B →
      (∀ s : Fin F.D.rank, s.val ≠ 0 → F.Ψ (F.n s) ∈ stabBar R A A₀ B) → False

end CFSG.Timmesfeld.ARS.ExclNS
