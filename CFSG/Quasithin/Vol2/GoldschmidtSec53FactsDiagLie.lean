module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsDiag

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

@[expose] def LieBorelFactsDiag (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (f : ℕ), IsSec53Param t m f → LieModel Y t m 2 f →
    ∀ U : Subgroup Y, IsSylowTwoOf U ⊤ → ∃ (H : Subgroup Y) (F E : Subgroup (MulAut Y)),
      BA.BorelAutDiag U H F E

theorem lieAutFacts_of_lieBorelFactsDiag {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}
    (h : LieBorelFactsDiag t m) : LieAutFacts t m := by
  intro Y _ _ f hpar hY A hP hU
  obtain ⟨H, F, E, D⟩ := h Y f hpar hY A.TD A.yam.1
  exact BA.lieAut_of_borelAutDiag D A rfl hP hU

end CFSG.Quasithin.H13.Sec53F
