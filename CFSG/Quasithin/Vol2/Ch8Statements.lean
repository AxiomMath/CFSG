module

public import CFSG.Quasithin.Background.HMathieuStatements
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

@[expose] def CocodeRow {G : Type} [Group G] (T L I : Subgroup G)
    [IsMulCommutative ↥(fsuV T I)] : Prop :=
  Row711M22Cocode T L I ∨ Row711M23Cocode T L I ∨ Row711M24Cocode T L I

@[expose] def Stmt8_1_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), CocodeRow T L I → ∀ hV : IsElemAbelian 2 (fsuV T I),
      ∀ x : IntMod (fsuV T I) hV, Mathieu.IsCocodeO2 (autI hV (fsuL0 T L)) x →
        Subgroup.centralizer ({x.val} : Set G) ≤ fsuM T L

@[expose] def Stmt8_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I),
      (Row711M22Cocode T L I → (6 : ℕ∞) ≤ rParam (fsuV T I)) ∧
      (Row711M23Cocode T L I → (7 : ℕ∞) ≤ rParam (fsuV T I)) ∧
      (Row711M24Cocode T L I → (8 : ℕ∞) ≤ rParam (fsuV T I))

@[expose] def Stmt8_1_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), CocodeRow T L I →
      Row711M24Cocode T L I ∧ rParam (fsuV T I) = 8 ∧ wParam T (fsuV T I) = 2 ∧
      (∀ H : Subgroup G, IsHStar T (fsuM T L) H → E1.nParam H = 2) ∧
      ∀ (hV : IsElemAbelian 2 (fsuV T I)) (A : Subgroup G), IsWOffender T (fsuV T I) A →
        rk ↥(A ⊓ Subgroup.centralizer (fsuV T I : Set G)) = 3 ∧ rk ↥(autI hV A) = 6 ∧
          rk ↥(fixV (autI hV A)) = 3

end CFSG.Quasithin.H13
