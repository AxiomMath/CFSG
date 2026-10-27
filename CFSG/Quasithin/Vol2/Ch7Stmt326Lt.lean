module

public import CFSG.Quasithin.Vol2.Ch7Bridge326

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative

@[expose] def Stmt3_2_6Lt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    (∃ _ : IsMulCommutative ↥(fsuV T I), I = fsuV T I ∧ fsuV T I = fsuVM T L I ∧
        ((∃ n : ℕ, Row711OmegaPlus T L I n) ∨ Row711L3Wreath T L I)) ∨
      Concl326ThreeC T L I

theorem stmt3_2_6Lt_of (h326 : Stmt3_2_6) : Stmt3_2_6Lt := fun G _ _ T L I hfsu hlt =>
  (tmpL6_3_2_6_of_stmt3_2_6 h326 G T L I hfsu hlt).2.2.imp_right
    concl326ThreeC_of_concl326Three

end CFSG.Quasithin.H13
