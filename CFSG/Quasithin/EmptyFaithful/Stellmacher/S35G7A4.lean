module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7A3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7A2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.G7

open CFSG.Quasithin.F53Mod Equiv

theorem abstractPlaneLemma : AbstractPlaneLemma := by
  intro M hf t ht π hsurj hπ U hU hinj hcard hgen f H1 H2
  obtain ⟨s, hs, hπs, hker⟩ := A.exists_section M hf ht π hsurj hπ
  exact A.plane_core M π hπ s hs hπs hker U hU hinj hcard hgen f H1 H2

end CFSG.Quasithin.F53.Stellmacher.S35.G7
