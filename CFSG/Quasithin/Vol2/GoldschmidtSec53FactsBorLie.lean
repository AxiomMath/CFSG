module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAutMain

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

@[expose] def LieBorelFacts (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (f : ℕ), IsSec53Param t m f → LieModel Y t m 2 f →
    ∀ U : Subgroup Y, IsSylowTwoOf U ⊤ → ∃ (H : Subgroup Y) (F : Subgroup (MulAut Y)),
      BA.BorelAutData U H F

theorem lieAutFacts_of_lieBorelFacts {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}
    (h : LieBorelFacts t m) : LieAutFacts t m := by
  intro Y _ _ f hpar hY A hP hU
  obtain ⟨H, F, D⟩ := h Y f hpar hY A.TD A.yam.1
  exact BA.lieAut_of_borelAutData D A rfl hP hU

end CFSG.Quasithin.H13.Sec53F
