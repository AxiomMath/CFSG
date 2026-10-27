module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.H13.J4TypeDefs
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Case8_2 (T L I : Subgroup G) [IsMulCommutative ↥(fsuV T I)] : Prop :=
  (∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M22Code T L I ∨ Row711M24Code T L I ∨
    Row711M24Cocode T L I

@[expose] def ch8Lz (L : Subgroup G) (z : G) : Subgroup G :=
  perfectCore (L ⊓ Subgroup.centralizer ({z} : Set G))

@[expose] def ch8Vz (V L : Subgroup G) (z : G) : Subgroup G :=
  ⁅V, pCoreOf 2 (ch8Lz L z)⁆

@[expose] def ch8E (V L : Subgroup G) (z : G) : Subgroup G :=
  conjClosure (ch8Vz V L z) (Subgroup.centralizer ({z} : Set G))

@[expose] def Stmt8_2_9_three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ¬ Row711M24Code T L I

@[expose] def Stmt8_2_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ fsuV T I = pCoreOf 2 L ∧
        ∃ z : G, orderOf z = 2 ∧ fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z

@[expose] def Stmt8_2_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      quasithinGenFitting (Subgroup.centralizer ({z} : Set G)) =
          pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
        ((∀ n : ℕ, Row711L3Nine T L I n →
            Nonempty (↥(ch8E (fsuV T I) L z) ≃* J4.D8CentralProduct 4)) ∧
          (Row711M22Code T L I → Nonempty (↥(ch8E (fsuV T I) L z) ≃* J4.D8CentralProduct 4)) ∧
          (Row711M24Cocode T L I →
            Nonempty (↥(ch8E (fsuV T I) L z) ≃* J4.D8CentralProduct 6) ∧
            J4.IsTypeJ4Core (Subgroup.centralizer ({z} : Set G)) (J4.selfC z))) ∧
        ch8E (fsuV T I) L z = pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
        pCoreOf 2 (ch8Lz L z) = ch8E (fsuV T I) L z ⊔ fsuV T I ∧
        ch8Vz (fsuV T I) L z = ch8E (fsuV T I) L z ⊓ fsuV T I

@[expose] def Stmt8_2_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      (Row711M24Cocode T L I ∧ fsuV T I ≤ L ∧ L ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
        L ⊓ Subgroup.centralizer (fsuV T I : Set G) = fsuV T I ∧
        Nat.card ↥(fsuV T I) = 2 ^ 11 ∧
        NativeCocode24 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥) ∧
      L = fsuM T L ∧
      ∀ z : G, orderOf z = 2 →
        fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
        J4.IsAutTripleM22 (Subgroup.centralizer ({z} : Set G) ⧸
          CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G)))

@[expose] def Stmt8_2_14_fusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      ∃ g ∈ L, g⁻¹ * z * g ∈ ch8Vz (fsuV T I) L z ∧ g⁻¹ * z * g ≠ z

end CFSG.Quasithin.H13
