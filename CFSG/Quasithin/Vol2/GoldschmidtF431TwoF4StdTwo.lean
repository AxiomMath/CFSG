module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdTwoCls
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Orient3

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

set_option linter.unusedSectionVars false

section Model


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem f4_stdTwo (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.Quasithin.H13.F431.Lift.StdTwo (Gm K a) (Ug K a) (Pg K a ⟨1, by decide⟩)
      (Pg K a ⟨0, by decide⟩) (zg hK) (tg hK) where
  z_mem := zg_mem_Ug hK
  t_mem := tg_mem_Ug hK
  z_two := orderOf_zg hK
  t_two := orderOf_tg hK
  cls := cls_gm ha hK
  noconj := noconj_gm ha hK
  center := center_gm ha hK
  aut_z := aut_z_gm ha hK
  aut_t := aut_t_gm ha hK
  cent_z := Or.inl (centralizer_zg_le ha hK)
  cent_t := Or.inr (centralizer_tg_le hK)

end Model

end CFSG.Quasithin.H13.F431.TwoF4
