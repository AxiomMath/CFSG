module

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Special.Gamma

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Open

variable {G : Type*} [Group G] {D : Set G}

theorem rootClosure_of_singleton (hsing : ∀ d ∈ D, rootSet D d = {d}) : RootClosure D := by
  intro d hd a ha b hb hab
  rw [hsing d hd] at ha hb
  exact absurd ((Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm) hab

theorem specialClosure_of_singleton (hD : IsRootInvolutionSet D)
    (hsing : ∀ d ∈ D, rootSet D d = {d}) : SpecialClosure D := by
  intro d hd e he h4 b hb
  rw [hsing e he] at hb
  rw [Set.mem_singleton_iff.1 hb]
  exact mem_rootSet_self (hD.sq_mem hd he h4)

theorem rootSet_eq_singleton_of_forall (hD : ∀ d ∈ D, ∀ e ∈ rootSet D d, e = d) {d : G}
    (hd : d ∈ D) : rootSet D d = {d} := by
  ext e
  constructor
  · intro he
    exact Set.mem_singleton_iff.2 (hD d hd e he)
  · intro he
    rw [Set.mem_singleton_iff.1 he]
    exact mem_rootSet_self hd

end CFSG.Timmesfeld
