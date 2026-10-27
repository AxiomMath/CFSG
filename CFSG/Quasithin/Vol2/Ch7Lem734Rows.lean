module

public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.HDefs
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

@[expose] def Stmt7_3_4_nPrime_SU3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ∀ n : ℕ, 2 ≤ n →
        BinaryNaturalSU3 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n →
          nPrime (autI hV ⊤) = 2 * n

@[expose] def Stmt7_3_4_nPrime_Sz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ∀ n : ℕ, BinaryNaturalSz (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n →
        nPrime (autI hV ⊤) = n

@[expose] def Stmt7_3_4_nPrime_L3Nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ∀ n : ℕ, Row711L3Nine T L I n → nPrime (autI hV ⊤) = 2 * n

@[expose] def Stmt7_3_4_nPrime_Mathieu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      (Row711M12 T L I ∨ Row711M22Hat T L I ∨ Row711M22Code T L I ∨ Row711M22Cocode T L I ∨
        Row711M23Code T L I ∨ Row711M23Cocode T L I ∨ Row711M24Code T L I ∨
        Row711M24Cocode T L I) →
        nPrime (autI hV ⊤) = 2

@[expose] def Stmt7_3_4_nPrime_SL3Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ∀ n : ℕ, 2 ≤ n → Row711SL3Pair T L I n → nPrime (autI hV ⊤) = n

@[expose] def Stmt7_3_4_nPrime_SL3One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      Row711SL3Pair T L I 1 → nPrime (autI hV ⊤) = 1

@[expose] def Stmt7_3_4_nPrime_Sp4Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      IsTwistedPair T L I → ∀ n : ℕ, 2 ≤ n →
        BinaryNaturalSp4 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
          (I.subgroupOf (fsuV T I)) ⊥ n →
          nPrime (autI hV ⊤) = n

@[expose] def Stmt7_3_4_nPrime_A6Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      IsTwistedPair T L I →
        AlternatingNatural (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
          (I.subgroupOf (fsuV T I)) ⊥ 6 →
          nPrime (autI hV ⊤) = 1

@[expose] def Stmt7_3_4_nPrime_S7Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      Row711S7Pair T L I → nPrime (autI hV ⊤) = 2

@[expose] def Stmt7_3_4_nPrime_L3Wreath : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      Row711L3Wreath T L I → nPrime (autI hV ⊤) = 2

@[expose] def Stmt7_2_1_m_Sz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ∀ n : ℕ, BinaryNaturalSz (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n →
        2 * n ≤ mParam (autI hV ⊤) ∧ 3 ≤ n

@[expose] def Stmt7_2_1_m_L3Nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ∀ n : ℕ, Row711L3Nine T L I n → 3 * n ≤ mParam (autI hV ⊤)

@[expose] def Stmt7_2_1_m_Mathieu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      (Row711M12 T L I ∨ Row711M22Hat T L I ∨ Row711M22Code T L I ∨ Row711M22Cocode T L I ∨
        Row711M23Code T L I ∨ Row711M23Cocode T L I ∨ Row711M24Code T L I ∨
        Row711M24Cocode T L I) →
        3 ≤ mParam (autI hV ⊤)

@[expose] def Stmt7_2_1_m_SL3Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ∀ n : ℕ, Row711SL3Pair T L I n → 2 * n ≤ mParam (autI hV ⊤)

@[expose] def Stmt7_2_1_m_L3Wreath : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      Row711L3Wreath T L I → 3 ≤ mParam (autI hV ⊤)

@[expose] def Stmt7_3_4_E336_wreath : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ _ : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      Row711L3Wreath T L I →
        IsTISetUnder (fsuV T I) (fsuM T L) ∧
          ∀ H : Subgroup G, IsHStar T (fsuM T L) H → 1 < E1.nParam H →
            H ⊓ fsuM T L = H ⊓ Subgroup.normalizer (fsuV T I : Set G) ∧
              H ⊓ fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (H ⊓ fsuM T L)

end CFSG.Quasithin.H13
