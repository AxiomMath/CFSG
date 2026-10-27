module

public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Pointwise

@[expose] def TmpL6_3_2_2_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I →
    fsuVM T L I ≤ fsuM T L ∧ IsPrimeReduced 2 ((fsuVM T L I).subgroupOf (fsuM T L))

@[expose] def TmpL6_3_2_2_eight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I →
    fsuV T I ≤ fsuL0 T L ⊔ T ∧ IsPrimeReduced 2 ((fsuV T I).subgroupOf (fsuL0 T L ⊔ T)) ∧
      pCoreOf 2 (fsuL0 T L ⊔ T) = T ⊓ Subgroup.centralizer (fsuV T I : Set G)

@[expose] def AS_p696_notFF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    ∀ _ : IsMulCommutative ↥(fsuV T I),
      (∃ n : ℕ, Row711OmegaPlus T L I n) ∨ Row711L3Wreath T L I → ¬ Concl701FF T L I

@[expose] def Sub326iii {G : Type} [Group G] (T L I : Subgroup G) : Prop :=
  L < fsuL0 T L ∧ ∃ _ : IsMulCommutative ↥(fsuVM T L I),
    Nonempty (↥(autOn L (fsuVM T L I)) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    DirectSumOfCopies (V := ↥(fsuVM T L I)) (autOn L (fsuVM T L I))
      ((fsuUL T L I).subgroupOf (fsuVM T L I)) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 ∧
    (Nonempty (↥(twoResidual (autOn (fsuM T L) (fsuVM T L I) ⊓
          Subgroup.centralizer (autOn (fsuL0 T L) (fsuVM T L I) :
            Set (MulAut ↥(fsuVM T L I))))) ≃* Multiplicative (ZMod 5)) ∨
      Nonempty (↥(twoResidual (autOn (fsuM T L) (fsuVM T L I) ⊓
          Subgroup.centralizer (autOn (fsuL0 T L) (fsuVM T L I) :
            Set (MulAut ↥(fsuVM T L I))))) ≃* Multiplicative (ZMod 5 × ZMod 5)))

@[expose] def TmpL6_3_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    (∃ _ : IsMulCommutative ↥(fsuV T I),
      qhatOf (V := ↥(fsuV T I)) (autOn (fsuL0 T L ⊔ T) (fsuV T I)) ≤ 2) ∧
    (∃ _ : IsMulCommutative ↥(fsuVM T L I),
      qhatOf (V := ↥(fsuVM T L I)) (autOn (fsuM T L) (fsuVM T L I)) ≤ 2) ∧
    ((∃ _ : IsMulCommutative ↥(fsuV T I), I = fsuV T I ∧ fsuV T I = fsuVM T L I ∧
        ((∃ n : ℕ, Row711OmegaPlus T L I n) ∨ Row711L3Wreath T L I)) ∨
      Concl326Three T L I)

@[expose] def TmpL6_3_2_10_eight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I Vp : Subgroup G), FSU G T L I →
    (Sub326iii T L I ∧ Vp = fsuVM T L I ∨ ¬ Sub326iii T L I ∧ Vp = fsuV T I) →
    thompsonJ T ≤ Subgroup.centralizer (Vp : Set G) →
    ∀ S : Subgroup G, IsPGroup 2 S → thompsonJ T ≤ S →
      thompsonJ T = thompsonJ S ∧ Subgroup.normalizer (S : Set G) ≤ fsuM T L

@[expose] def TmpL6_3_2_10_nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I Vp : Subgroup G), FSU G T L I →
    (Sub326iii T L I ∧ Vp = fsuVM T L I ∨ ¬ Sub326iii T L I ∧ Vp = fsuV T I) →
    thompsonJ T ≤ Subgroup.centralizer (Vp : Set G) →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ ∧
        Vp ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥

structure TmpL6_Hyp4_2_1 (G : Type) [Group G] [Finite G] (T M L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  maxTwoLocal : quasithinIsMaxTwoLocal M
  le : T ≤ M
  maximal : quasithinIsMaximalLocal T L
  faithful : quasithinIsFaithfulLocal T L
  leM : L ≤ M
  quasisimple : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def TmpL6_4_4_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S MH : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    pCoreOf 2 H ≠ ⊥ → 1 < E1.nParam H → QuasithinUnique.IsSylowTwoOf S H →
    IsUniqueMaxOver H S MH →
      E1.IsTwoClosed (MH ⊓ oTwoUpper H) ∧
      ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B MH →
        (∀ (p : ℕ) (A : Subgroup G), p.Prime → A ≤ B → IsElemAbelian p A →
          (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G) →
            H = MH ⊔ (H ⊓ Subgroup.normalizer (A : Set G)) ∧
              ¬ H ⊓ Subgroup.normalizer (A : Set G) ≤ MH) ∧
        ∀ M Mp : Subgroup G, quasithinIsMaxTwoLocal M → S ≤ M → MH = M ⊓ H →
          Mp = oTwoUpper Mp → Mp ≤ M → M ≤ Subgroup.normalizer (Mp : Set G) →
            ((B ⊓ sectionCentralizer Mp (pCoreOf 2 Mp) : Subgroup G) : Set G) * (S : Set G) =
              (S : Set G) * ((B ⊓ sectionCentralizer Mp (pCoreOf 2 Mp) : Subgroup G) : Set G)

@[expose] def Tmp1_4_1_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → (quasithinIsMaximalLocal T L ∨ IsXiStar T L) → IsXf L →
      ∃ V : Subgroup G, V ≤ fsuL0 T L ⊔ T ∧
        IsPrimeReduced 2 (V.subgroupOf (fsuL0 T L ⊔ T)) ∧ ⁅V, fsuL0 T L⁆ ≠ ⊥

end CFSG.Quasithin.Vol2.Ch10
