module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.HDefs
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section AlphaE

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] noncomputable def alphaE (M : Subgroup (MulAut V)) : ℕ∞ :=
  ⨅ k ∈ alphaSet M, (k : ℕ∞)

theorem alphaSet_eq_empty_of_alphaH_eq_one {M : Subgroup (MulAut V)} (h : alphaH M = 1) :
    alphaSet M = ∅ := by
  by_contra hne
  have hne' : (alphaSet M).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  unfold alphaH at h
  rw [ite_eq_left hne'] at h
  have := (Nat.sInf_mem hne').1
  omega

theorem alphaE_eq_top_of_alphaH_eq_one {M : Subgroup (MulAut V)} (h : alphaH M = 1) :
    alphaE M = ⊤ := by
  unfold alphaE
  rw [alphaSet_eq_empty_of_alphaH_eq_one h]
  simp

theorem alphaE_eq_top_of_not_isFOneModule {M : Subgroup (MulAut V)} (h : ¬ IsFOneModule M) :
    alphaE M = ⊤ :=
  alphaE_eq_top_of_alphaH_eq_one (alphaH_eq_one_of_not_isFOneModule h)

end AlphaE

section Column

variable {G : Type} [Group G]

@[expose] def IsNPrime721 (T L I : Subgroup G) (k : ℕ) : Prop :=
  ∀ _ : IsMulCommutative ↥(fsuV T I),
    (∀ n : ℕ, 2 ≤ n →
      BinaryNaturalSU3 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n → k = 2 * n) ∧
    (∀ n : ℕ,
      BinaryNaturalSz (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n → k = n) ∧
    (∀ n : ℕ, Row711L3Nine T L I n → k = 2 * n) ∧
    (Row711M12 T L I ∨ Row711M22Hat T L I ∨ Row711M22Code T L I ∨ Row711M22Cocode T L I ∨
      Row711M23Code T L I ∨ Row711M23Cocode T L I ∨ Row711M24Code T L I ∨
      Row711M24Cocode T L I → k = 2) ∧
    (∀ n : ℕ, Row711SL3Pair T L I n → k = n) ∧
    (∀ n : ℕ, 2 ≤ n → IsTwistedPair T L I →
      BinaryNaturalSp4 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
        (I.subgroupOf (fsuV T I)) ⊥ n → k = n) ∧
    (IsTwistedPair T L I → AlternatingNatural (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
        (I.subgroupOf (fsuV T I)) ⊥ 6 → k = 1) ∧
    (Row711S7Pair T L I → k = 2) ∧
    (Row711L3Wreath T L I → k = 2)

end Column

@[expose] def Stmt7_1_1_normal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I),
      (Row711SU3 T L I ∨ Row711Sz T L I ∨ (∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M12 T L I ∨
        Row711M22Hat T L I ∨ Row711M22Code T L I ∨ Row711M22Cocode T L I ∨
        Row711M23Code T L I ∨ Row711M23Cocode T L I ∨ Row711M24Code T L I ∨
        Row711M24Cocode T L I ∨ (∃ n : ℕ, Row711SL3Pair T L I n) ∨ Row711Sp4Pair T L I ∨
        Row711S7Pair T L I) →
      T ≤ Subgroup.normalizer (L : Set G)

@[expose] def Stmt7_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), (mParam (autI hV ⊤) : ℕ∞) ≤ rParam (fsuV T I)

@[expose] def Stmt7_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I),
      (∀ H : Subgroup G, IsHStar T (fsuM T L) H →
        wParam T (fsuV T I) ≤ E1.nParam H ∧ E1.nParam H ≤ (nPrime (autI hV ⊤) : ℕ∞)) ∧
      wParam T (fsuV T I) ≤ (nPrime (autI hV ⊤) : ℕ∞) ∧
      ((∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Row711SU3 T L I →
          nPrime (autI hV ⊤) < sParam hV) ∧
        (∀ _ : IsMulCommutative ↥(fsuV T I), Row711SU3 T L I →
          (nPrime (autI hV ⊤) : ℕ∞) < rParam (fsuV T I))) ∧
      IsNPrime721 T L I (nPrime (autI hV ⊤))

@[expose] def Stmt7_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    fsuM T L ≤ Subgroup.normalizer (L : Set G) → ∀ hV : IsElemAbelian 2 (fsuV T I),
      min (alphaE (autI hV ⊤)) (betaH (autI hV ⊤)) ≤ rParam (fsuV T I)

@[expose] def Stmt7_2_1_SU3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I),
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ∀ n : ℕ, 2 ≤ n →
        BinaryNaturalSU3 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n →
        aParam (autI hV ⊤) ≤ n ∧ mParam (autI hV ⊤) = 2 * n ∧
          CFSG.Open.pRank 2 (autI hV ⊤) ≤ n + 1 ∧ ((4 * n : ℕ) : ℕ∞) ≤ betaH (autI hV ⊤) ∧
          alphaH (autI hV ⊤) = 1

@[expose] def Stmt7_2_1_Sz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I),
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ∀ n : ℕ, BinaryNaturalSz (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ n →
        CFSG.Open.pRank 2 (autI hV ⊤) ≤ n ∧ ((8 * n : ℕ) : ℕ∞) ≤ 3 * betaH (autI hV ⊤) ∧
          alphaH (autI hV ⊤) = 1

@[expose] def Stmt7_2_1_M22Hat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I),
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      Row711M22Hat T L I →
        CFSG.Open.pRank 2 (autI hV ⊤) ≤ 5 ∧ (8 : ℕ∞) ≤ betaH (autI hV ⊤) ∧
          alphaH (autI hV ⊤) = 1

@[expose] def Stmt7_2_1_SL3Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      ∀ n : ℕ, 2 ≤ n → Row711SL3Pair T L I n →
        CFSG.Open.pRank 2 (autI hV ⊤) ≤ 2 * n ∧ ((4 * n : ℕ) : ℕ∞) ≤ betaH (autI hV ⊤) ∧
          alphaH (autI hV ⊤) = 1

@[expose] def Stmt7_2_1_Sp4Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      IsTwistedPair T L I →
        (∀ n : ℕ, 2 ≤ n → BinaryNaturalSp4 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
            (I.subgroupOf (fsuV T I)) ⊥ n →
          aParam (autI hV ⊤) < 2 * n ∧ 3 * n ≤ mParam (autI hV ⊤)) ∧
        (AlternatingNatural (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))
            (I.subgroupOf (fsuV T I)) ⊥ 6 →
          aParam (autI hV ⊤) < 2 ∧ 3 ≤ mParam (autI hV ⊤))

end CFSG.Quasithin.H13
