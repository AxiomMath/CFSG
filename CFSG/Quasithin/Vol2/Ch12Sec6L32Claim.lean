module

public import CFSG.Quasithin.Vol2.Ch12Sec6Final

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank S126

@[expose] def Claim12_6_32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → Case1 T L H K →
        ∀ h : HypF918 T V L F.V1 F.V5 H K,
          ∃ I : Subgroup G, ∃ t ∈ T, F.V1 ≤ I ∧ I ≤ conjClosure F.V5 H ∧
            K ≤ Subgroup.normalizer (I : Set G) ∧
            tildeOf F.V1 I ⊓ tildeOf F.V1 (conjSub t I) = ⊥ ∧
            tildeOf F.V1 I ⊔ tildeOf F.V1 (conjSub t I) =
              tildeOf F.V1 (conjClosure F.V5 H) ∧
            @BinaryNaturalSL _ (commGroupOfElemAbelian h.toHypF98.toHypF91.isElemAbelian_tilde)
              (autOn (tildeOf F.V1 K) (tildeOf F.V1 (conjClosure F.V5 H)))
              ((tildeOf F.V1 I).subgroupOf (tildeOf F.V1 (conjClosure F.V5 H))) ⊥ 3 2

end CFSG.Quasithin.H13
