module

public import CFSG.Quasithin.Vol2.Ch12Sec7Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Ident1277 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
      ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) →
        ∃ z : G, orderOf z = 2 ∧
          Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃* ↥(Subgroup.centralizer
            ({transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))) ∧
          ∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
            g⁻¹ * z * g ≠ z

@[expose] def Ident12714 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
    ∀ z ∈ V, (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 →
      Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) →
      ¬ V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) →
        orderOf z = 2 ∧
          Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃* ↥(Subgroup.centralizer
            ({transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))) ∧
          ∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
            g⁻¹ * z * g ≠ z

end CFSG.Quasithin.H13
