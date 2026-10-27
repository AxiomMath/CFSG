module

public import CFSG.Quasithin.Vol2.Ch10SecA1010
public import CFSG.Quasithin.Vol2.Ch10T326CBridge

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

@[expose] def Stmt10_1_0C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    ∀ _ : IsMulCommutative ↥(fsuV T I),
      Concl701FF T L I ∨ Concl701J4 T L I ∨ Concl701Orth T L I → Concl326ThreeC T L I

theorem stmt10_1_0C_of (h326 : Stmt3_2_6C) (hnFF : AS_p696_notFF) : Stmt10_1_0C := by
  intro G _ _ T L I hfsu hlt hc hconcl
  obtain ⟨-, -, hcase⟩ := tmpL6_3_2_6C_of_stmt3_2_6C h326 G T L I hfsu hlt
  rcases hcase with ⟨_, -, -, hrow⟩ | h3
  · exfalso
    rcases hconcl with hFF | hJ4 | ⟨a, ha, hOrth⟩
    · exact hnFF G T L I hfsu hlt hc hrow hFF
    · have hV := hJ4.2.2.1
      rcases hrow with ⟨n, hn⟩ | hw
      · rw [SecA.card_fsuV_of_omegaPlus hn] at hV
        have := Nat.pow_right_injective (le_refl 2) hV
        omega
      · rw [SecA.card_fsuV_of_l3Wreath hw] at hV
        norm_num at hV
    · have hA := SecA.card_autOn_of_orth hOrth
      rcases hrow with ⟨n, hn⟩ | hw
      · rw [SecA.card_autOn_of_omegaPlus hn] at hA
        exact SecA.omegaPlus_orth_card_ne hn.2.1 (by omega) hA
      · rw [SecA.card_autOn_of_l3Wreath hw] at hA
        exact SecA.l3Wreath_orth_card_ne ha hA
  · exact h3

end CFSG.Quasithin.Vol2.Ch10
