module

public import CFSG.Quasithin.EmptyFaithful.S146F2
public import CFSG.Quasithin.EmptyFaithful.S146zUBSetup

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem fourList_of_invariant (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hD310 : D310)
    (hD391 : D391) (hI4 : Insp4) (S : Setting146 G T M) {L : Subgroup G}
    (hL : L ∈ cComp (mcOf T)) (hs : IsSimpleGroup (KBar L))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : FourList (KBar L) := by
  have hF := hypF918_of_setting146 hA37 hA38 S hL hs
  have hH : SQTKGroup ↥(conjClosure L T ⊔ T) :=
    S.sqtkGroup_of_isHTM (S.isHTM_conjClosure_sup hA37 hA38 hL)
  have hK : conjClosure L T = L :=
    le_antisymm (conjClosure_le fun t ht l hl =>
      (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl) (le_conjClosure L T)
  exact fourList_kbar hF hH hK hs hD310 hD391 hI4

theorem fiveShape_of_not_invariant (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (S : Setting146 G T M) {L : Subgroup G} (hL : L ∈ cComp (mcOf T))
    (hs : IsSimpleGroup (KBar L)) (hTL : ¬ T ≤ Subgroup.normalizer (L : Set G)) :
    FiveShape (KBar L) := by
  obtain ⟨s, hsT, hsN⟩ := IsConcreteLE.not_le_iff_exists.mp hTL
  have hF := hypF918_of_setting146 hA37 hA38 S hL hs
  have hH : SQTKGroup ↥(conjClosure L T ⊔ T) :=
    S.sqtkGroup_of_isHTM (S.isHTM_conjClosure_sup hA37 hA38 hL)
  exact fiveShape_kbar hF hH (S146zU.UB.conjClosure_ne_self hsT hsN) hs hD36 hD37 hD321 hI5 hA37
    hA38

end CFSG.Quasithin.S146zX
