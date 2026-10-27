module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35At16
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35At15
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35At9
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChCent

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.At

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem arcDict (hC : Ch.Ctx H M S) : ArcDict H M := fun δ l ε c hδ hl hε hne =>
  ⟨by rw [← hC.Rl_eq hδ hl hε hne]; exact c.img_Rl hC hδ hl, c.img_Zv_nbr hC.sit hδ hl⟩

theorem claimR (hC : Ch.Ctx H M S) : ClaimR H M :=
  claimR_of_dict hC.sit hC.orthZ (arcDict hC)

theorem claim9 (hC : Ch.Ctx H M S) : Claim9 H M :=
  claim9_of_dict hC.sit hC.orthZ (arcDict hC)

theorem claim16a (hC : Ch.Ctx H M S) : Claim16a H M :=
  claim16a_of_dict hC.sit hC.orthZ (arcDict hC)

theorem claim15c (hC : Ch.Ctx H M S) : Claim15c H M :=
  claim15c_of_dict hC.sit hC.orthZ (arcDict hC)

end S35.At

end F53.Stellmacher

end CFSG.Quasithin
