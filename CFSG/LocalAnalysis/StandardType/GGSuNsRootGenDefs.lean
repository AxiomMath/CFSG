module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFrame

public section

namespace CFSG.StandardType

namespace SuNsRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2

variable {K : Type} [Field K] {n d : ℕ}

@[expose] def IsDiagTorusModelU (p : ℕ) {L' : Type} [Group L']
    (φ : ↥(unitarySU 2 n K d) →* L') (A : Subgroup (MulAut L')) : Prop :=
  ∀ a : MulAut L', a ∈ A ↔ ∃ D : ↥(unitarySU 2 n K d),
    (∃ σ : Fin d → Kˣ, (D : GL (Fin d) K) = diagHom d σ) ∧ D ^ p = 1 ∧ a = MulAut.conj (φ D)

theorem coe_swapU_eq_permGL (h : UnitaryFieldData 2 n K) (i j : Fin d) :
    ((SURep.swapU h i j : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = permGL (Equiv.swap i j) :=
  rfl

variable (n) in
@[expose] def pairCentU (p : ℕ) (K : Type) [Field K] (i j : Fin d) :
    Subgroup ↥(unitarySU 2 n K d) :=
  Subgroup.centralizer {D : ↥(unitarySU 2 n K d) | ∃ σ : Fin d → Kˣ,
    (D : GL (Fin d) K) = diagHom d σ ∧ σ i = σ j ∧ ∀ k, σ k ^ p = 1}

end SuNsRootGen

end CFSG.StandardType

end
