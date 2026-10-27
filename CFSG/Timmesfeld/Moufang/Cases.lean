module

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Reduction.RootClass

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Blueprint

variable {G : Type*} [Group G] {D : Set G}

theorem rootMoufang_of_singleton (hsing : ∀ d ∈ D, rootSet D d = {d})
    (h3 : ∀ d ∈ D, ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) → orderOf (d * c) = 3) :
    RootMoufang D := by
  intro d hd c hc hdc hodd a ha
  rw [hsing d hd] at ha
  rw [Set.mem_singleton_iff.1 ha]
  refine ⟨c, ?_, h3 d hd c hc hdc hodd⟩
  rw [hsing c hc]
  exact Set.mem_singleton c

end CFSG.Timmesfeld.Moufang
