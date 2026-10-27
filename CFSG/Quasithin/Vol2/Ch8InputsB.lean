module

public import CFSG.Quasithin.H13.J4TypeDefs
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3

@[expose] def InputAS91 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      J4.IsTypeJ4Core (Subgroup.centralizer ({z} : Set G)) (J4.selfC z) →
      J4.IsAutTripleM22 (Subgroup.centralizer ({z} : Set G) ⧸
        CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G))) →
      (∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
        g⁻¹ * z * g ≠ z) →
      Nonempty (G ≃* NativeSporadic.J4)

@[expose] def Input7_0_2_unique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    IsUniqueM (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (fsuV T I : Set G) :
      Subgroup G) : Set G)) (fsuM T L)

@[expose] def Input8_3_Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    T ⊓ Subgroup.centralizer (fsuV T I : Set G) = pCoreOf 2 (fsuL0 T L ⊔ T)

@[expose] def Input8_3_z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
      ∃ z : G, orderOf z = 2 ∧
        fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z

end CFSG.Quasithin.H13
