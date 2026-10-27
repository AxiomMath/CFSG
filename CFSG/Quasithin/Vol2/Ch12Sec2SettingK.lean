module

public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Asc94_M24He_L52TypeK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), IsSimpleGroup G →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → orderOf z = 2 →
    Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃*
      ↥(Subgroup.centralizer
        ({transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))) →
    (∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
      g⁻¹ * z * g ≠ z) →
      (LieModel G .PSL 5 2 1 ∨ Nonempty (G ≃* NativeSporadic.M24) ∨
          Nonempty (G ≃* NativeSporadic.He)) ∧
        ((∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
            ∃ φ : ↥(Subgroup.normalizer (E : Set G)) →* GL (Fin 4) (ZMod 2),
              Function.Surjective φ ∧
              φ.ker = (Subgroup.centralizer (E : Set G)).subgroupOf
                (Subgroup.normalizer (E : Set G))) →
          ¬ Nonempty (G ≃* NativeSporadic.He) ∧
            (LieModel G .PSL 5 2 1 ∨ Nonempty (G ≃* NativeSporadic.M24)))

theorem asc94K_of_asc94 (h : Asc94_M24He_L52Type) : Asc94_M24He_L52TypeK :=
  fun G _ _ z hs _ hord hC hnw => h G z hs hord hC hnw

end CFSG.Quasithin.H13
