module

public import CFSG.Quasithin.Vol2.Ch12Sec6Final
public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin S126

@[expose] def Claim12_6_33ab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → Case2 T L H K →
        ∀ h : HypF918 T V L F.V1 F.V5 H K, ∀ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) →
          (∃ I : Subgroup G, F.V1 ≤ I ∧ I ≤ conjClosure F.V5 H ∧
              IsIrrPlusTilde F.V1 (conjClosure K T) I ∧
              ⁅⁅conjClosure F.V5 H, K⁆, conjSub t⁻¹ K⁆ ≤ conjClosure I H ∧
              ⁅⁅conjClosure I H, K⁆, conjSub t⁻¹ K⁆ ≤ F.V1) ∨
            @Omega4PlusModule _ (commGroupOfElemAbelian h.toHypF98.toHypF91.isElemAbelian_tilde)
              (autOn (tildeOf F.V1 (conjClosure K T)) (tildeOf F.V1 (conjClosure F.V5 H))) 2

end CFSG.Quasithin.H13
