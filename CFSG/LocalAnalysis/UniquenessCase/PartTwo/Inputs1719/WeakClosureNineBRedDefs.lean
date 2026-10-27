module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

@[expose] def NGFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L1b L2b Tb : Subgroup X),
    CFSG.LocalAnalysis.UniquenessCase.UC22.IsL3 ↥L1b 1 →
    (∃ t ∈ Tb, L2b = L1b.map (MulAut.conj t).toMonoidHom) → L1b ≠ L2b →
    (∀ t ∈ Tb, L1b.map (MulAut.conj t).toMonoidHom = L1b ∨
      L1b.map (MulAut.conj t).toMonoidHom = L2b) →
    ⁅L1b, L2b⁆ = ⊥ → (L1b ⊔ L2b).Normal →
    centralizer ((L1b ⊔ L2b : Subgroup X) : Set X) = ⊥ → L1b ⊔ L2b ⊔ Tb = ⊤ →
    IsSylowIn 2 Tb ⊤ → NineFifteenBarFacts X L1b L2b Tb

end CFSG.LocalAnalysis.WeakClosure81

