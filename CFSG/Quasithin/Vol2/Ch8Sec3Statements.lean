module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def ch83X (T L : Subgroup G) (z : G) : Subgroup G :=
  twoResidual (fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G))

@[expose] def ch83S (T L : Subgroup G) (z : G) : Subgroup G :=
  pCoreOf 2 (ch83X T L z ⊔ T)

@[expose] def ch83Kz (T L : Subgroup G) (z : G) : Subgroup G :=
  conjClosure (ch83X T L z) (Subgroup.centralizer ({z} : Set G))

@[expose] def Stmt8_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
      ∀ hV : IsElemAbelian 2 (fsuV T I), sParam hV = 3

@[expose] def Stmt8_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      Subgroup.normalizer (wClos (fsuV T I) 0 (ch83S T L z) : Set G) ≤ fsuM T L ∧
        Subgroup.centralizer (cClos (fsuV T I) 1 (ch83S T L z) : Set G) ≤ fsuM T L

@[expose] def Stmt8_3_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      (∃ (K : Subgroup G) (s : G), s ∈ T ∧ s ∉ Subgroup.normalizer (K : Set G) ∧
          quasithinIsCComponent K (Subgroup.centralizer ({z} : Set G)) ∧
          ch83Kz T L z = K ⊔ CFSG.conjugate K s ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
            Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
        IsHStar T (fsuM T L) (ch83Kz T L z ⊔ T) ∧
        ch83X T L z ⊔ (T ⊓ ch83Kz T L z) = ch83Kz T L z ⊓ fsuM T L ∧
        Subgroup.centralizer ({z} : Set G) = ch83Kz T L z ⊔ T ∧
        fsuM T L = fsuL0 T L ⊔ T ∧
        IsSylowIn 2 (ch83S T L z) (ch83Kz T L z ⊔ ch83S T L z) ∧
        E1.nParam (ch83Kz T L z ⊔ ch83S T L z) = 2

@[expose] def Stmt8_3_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      wClos (fsuV T I) 2 (ch83S T L z) ≤ Subgroup.centralizer (fsuV T I : Set G)

end CFSG.Quasithin.H13
