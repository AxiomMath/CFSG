module

public import CFSG.Quasithin.Vol2.Ch8Sec3Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Stmt8_3_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      Subgroup.centralizer ({z} : Set G) =
          ch83Kz T L z ⊔ (fsuM T L ⊓ Subgroup.centralizer ({z} : Set G)) ∧
        ((∃ (K : Subgroup G) (s : G), s ∈ T ∧ s ∉ Subgroup.normalizer (K : Set G) ∧
            quasithinIsCComponent K (Subgroup.centralizer ({z} : Set G)) ∧
            ch83Kz T L z = K ⊔ CFSG.conjugate K s ∧
            ∃ p : ℕ, p.Prime ∧
              CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 p 1) ∨
          CFSG.Assembly.LowTwoRank.StatedClassicalModel
            (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z)) .PSL 4 2 1 ∨
          CFSG.Assembly.LowTwoRank.StatedClassicalModel
            (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z)) .PSL 5 2 1 ∨
          Nonempty (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z) ≃*
            NativeSporadic.Carrier .He))

@[expose] def ch83Val {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := rfl
  map_mul' := IntMod.val_mul

@[expose] def ch83CR {T I : Subgroup G} (hV : IsElemAbelian 2 (fsuV T I)) : Subgroup G :=
  (fixV (⨆ A ∈ E3.aSet 2 (autI hV T), A)).map (ch83Val hV)

@[expose] def Stmt8_3_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I),
      Subgroup.centralizer (ch83CR hV : Set G) ≤ fsuM T L

@[expose] def Stmt8_3_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
      ∀ H : Subgroup G, IsHStar T (fsuM T L) H → E1.nParam H = 2

@[expose] def Claim8310Excl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      ((∃ (K : Subgroup G) (s : G), s ∈ T ∧ s ∉ Subgroup.normalizer (K : Set G) ∧
            quasithinIsCComponent K (Subgroup.centralizer ({z} : Set G)) ∧
            ch83Kz T L z = K ⊔ CFSG.conjugate K s ∧
            ∃ p : ℕ, p.Prime ∧ p ≠ 5 ∧
              CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 p 1) ∨
          CFSG.Assembly.LowTwoRank.StatedClassicalModel
            (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z)) .PSL 4 2 1 ∨
          CFSG.Assembly.LowTwoRank.StatedClassicalModel
            (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z)) .PSL 5 2 1 ∨
          Nonempty (↥(ch83Kz T L z) ⧸ CFSG.pCore 2 ↥(ch83Kz T L z) ≃*
            NativeSporadic.Carrier .He)) →
        ∀ H : Subgroup G, IsHStar T (fsuM T L) H → H ≤ ch83Kz T L z ⊔ T → E1.nParam H = 1

@[expose] def Claim8310Gz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      (∃ (K : Subgroup G) (s : G), s ∈ T ∧ s ∉ Subgroup.normalizer (K : Set G) ∧
          quasithinIsCComponent K (Subgroup.centralizer ({z} : Set G)) ∧
          ch83Kz T L z = K ⊔ CFSG.conjugate K s ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
            Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      IsHStar T (fsuM T L) (ch83Kz T L z ⊔ T) →
      ch83X T L z ⊔ (T ⊓ ch83Kz T L z) = ch83Kz T L z ⊓ fsuM T L →
        Subgroup.centralizer ({z} : Set G) = ch83Kz T L z ⊔ T

@[expose] def Claim8310N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      (∃ (K : Subgroup G) (s : G), s ∈ T ∧ s ∉ Subgroup.normalizer (K : Set G) ∧
          quasithinIsCComponent K (Subgroup.centralizer ({z} : Set G)) ∧
          ch83Kz T L z = K ⊔ CFSG.conjugate K s ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
            Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      ch83X T L z ⊔ (T ⊓ ch83Kz T L z) = ch83Kz T L z ⊓ fsuM T L →
        E1.nParam (ch83Kz T L z ⊔ ch83S T L z) ≤ 2

end CFSG.Quasithin.H13
