module

public import CFSG.Quasithin.Vol2.Ch12Sec6Final
public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin S126

@[expose] def FFSteps12633I : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → Case2 T L H K →
        ∀ h : HypF918 T V L F.V1 F.V5 H K, ∀ I : Subgroup G, F.V1 ≤ I →
          ∀ hIHU : conjClosure I H ≤ conjClosure F.V5 H,
            conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) →
            tildeOf F.V1 (conjClosure I H) ≠ ⊥ →
            tildeOf F.V1 ⁅conjClosure I H, conjClosure K T⁆ = tildeOf F.V1 (conjClosure I H) →
              (¬ F9.IsStrongFFInt (tildeOf F.V1 (conjClosure K T ⊔ T))
                    (tildeOf F.V1 (conjClosure I H)) (h.isElemAbelian_tilde_of_le hIHU) ∧
                  ¬ F9.IsStrongFFInt
                    (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
                      (conjClosure K T ⊔ T))
                    (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
                      (conjClosure F.V5 H))
                    (h.isElemAbelian_quotient (conjClosure I H))) ∧
                (@Omega4PlusModule _ (commGroupOfElemAbelian (h.isElemAbelian_tilde_of_le hIHU))
                    (autOn (tildeOf F.V1 (conjClosure K T)) (tildeOf F.V1 (conjClosure I H))) 2 →
                  ¬ IsFFInt (tildeOf F.V1 (conjClosure K T ⊔ T)) (tildeOf F.V1 (conjClosure I H))
                    (h.isElemAbelian_tilde_of_le hIHU)) ∧
                (IsFFInt
                    (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
                      (conjClosure K T ⊔ T))
                    (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
                      (conjClosure F.V5 H))
                    (h.isElemAbelian_quotient (conjClosure I H)) →
                  tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ =
                    tildeOf F.V1 (conjClosure F.V5 H) →
                  ∀ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) →
                    ⁅⁅conjClosure F.V5 H, K⁆, conjSub t⁻¹ K⁆ ≤ conjClosure I H)

end CFSG.Quasithin.H13
