module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6E

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11

theorem smallCase6 : SmallCase6 := by
  intro hT V _ _ _ Γ A m hyp hsolv _ hm hd
  have hm2 : m = 2 := by
    have := hyp.bound
    omega
  subst hm2
  have hC : SmD6.Ctx Γ A :=
    ⟨hyp, hd, hsolv, fun _ hSΓ hSp => SmD6.card_le_27_of_isPGroup hT hd hyp.quotient hSΓ hSp⟩
  rcases hC.simple_or_planes with hs | ⟨W, hW⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hC.concl3_of_simple hs⟩)))
  · exact (hC.false_of_planes hW).elim

end CFSG.Quasithin.SzN31
