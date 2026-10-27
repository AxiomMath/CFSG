module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplit

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

@[expose] def KnownOn (S : Fin 11 → Prop) : Prop :=
  ∀ i : Fin 11, S i → KnownOver (DatumOn (fam i))

theorem known_of_knownOn {S : Fin 11 → Prop} (hS : KnownOn S)
    (hrest : ∀ i : Fin 11, ¬ S i → KnownOver (DatumOn (fam i))) : GGTablePThreeKnown :=
  known_iff_families.mpr fun i => by
    by_cases hi : S i
    · exact hS i hi
    · exact hrest i hi

end CFSG.StandardType.TablePThreeKG

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTablePThreeKnownRest : Prop :=
  TablePThreeKG.KnownOn fun i => i ≠ 0 ∧ i ≠ 10

theorem ggTablePThreeKnown_of_rest (h : GGTablePThreeKnownRest) (hLin : TablePThreeKG.LeafLin)
    (hSmall : TablePThreeKG.LeafSmallVac) : GGTablePThreeKnown :=
  TablePThreeKG.known_of_knownOn h fun i hi => by
    by_cases h0 : i = 0
    · subst h0
      exact hLin
    · have h10 : i = 10 := by
        by_contra h10
        exact hi ⟨h0, h10⟩
      subst h10
      exact TablePThreeKG.knownOn_small hSmall

end CFSG.StandardType

end
