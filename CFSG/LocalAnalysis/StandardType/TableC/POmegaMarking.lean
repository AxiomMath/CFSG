module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmModel

public section

namespace CFSG.StandardType.TableC

open CFSG.Assembly CFSG.Blueprint

theorem not_largeEvenSplit_marking_omModel
    {G : Type} [Group G] {K' : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hM : OmNonsplit.OmModel F K') {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1) :
    ¬ LargeEvenMarking ↥K' (fun lab _ _ _ _ _ => LargeEvenSplit p lab) := by
  intro hmk
  refine OmNonsplit.not_ggNbrClauseFiveMarking_of_omModel (x := (1 : G)) hF hM hp hp2 hq1 hq2
    ⟨1, K'.one_mem, fun l _ => by simp⟩ ?_
  exact largeEvenMarking_mono (fun lab _ _ _ _ _ hS => Or.inl (Or.inl hS)) hmk

end CFSG.StandardType.TableC

end
