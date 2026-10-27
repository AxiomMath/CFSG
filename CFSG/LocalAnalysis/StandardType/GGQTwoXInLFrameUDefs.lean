module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUBasic
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLAugDefs

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom)

variable {G : Type} [Group G]

structure GGQTwoXInLUFrame (Bs X : Subgroup G) (N : ℕ) (K : Type) [Field K] where
  field : UnitaryFieldData 2 1 K
  φ : ↥(unitarySU 2 1 K N) →* G
  range_eq : φ.range = X
  ker_le : φ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K N)
  δ : G → Fin N → Kˣ
  pair : ∀ b ∈ Bs, (b, diagHom N (δ b)) ∈ SUTorus.suPairs φ

structure GGQTwoXInLUCoord (Bs X L : Subgroup G) (x : G) (n : ℕ) (K : Type) [Field K] where
  field : UnitaryFieldData 2 1 K
  φ : ↥(unitarySU 2 1 K (n + 1)) →* G
  range_eq : φ.range = X
  ker_le : φ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K (n + 1))
  ω : Kˣ
  ω_ne_one : ω ≠ 1
  ι : Additive ↥Bs ≃+ ↥(GGQTwoXInLAug n)
  diag : ∀ b : ↥Bs, ∃ s : ↥(unitarySU 2 1 K (n + 1)),
    (s : GL (Fin (n + 1)) K) = diagHom (n + 1)
      (fun i => ω ^ ((ι (Additive.ofMul b) : Fin (n + 1) → ZMod 3) i).val) ∧ φ s = b
  mem_x : x ∈ Bs
  ι_x : ((ι (Additive.ofMul ⟨x, mem_x⟩) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
    fun i => if i = 0 then 0 else -1
  L_eq : L = (TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 0)).map φ

end CFSG.StandardType

end
