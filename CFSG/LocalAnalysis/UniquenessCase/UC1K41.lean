module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3
import CFSG.GroupTheory.HyperplaneDecomposition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)

variable {G : Type} [Group G] [Finite G] {p : ℕ}
variable {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem fixV_eq_invariants (ρ : Representation (ZMod p) G V) (A : Subgroup G) :
    fixV ρ A = Representation.invariants (ρ.comp A.subtype) := by
  ext v
  exact ⟨fun h a => h a a.2, fun h a ha => h ⟨a, ha⟩⟩

theorem iSup_fixV_hyperplanes_eq_top [Finite V] (ρ : Representation (ZMod p) G V)
    (hp : p.Prime) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian q A) (hA1 : A ≠ ⊥) :
    ⨆ B : ↥(hyperplanes q A), fixV ρ B.1 = ⊤ := by
  simp only [fixV_eq_invariants]
  exact CFSG.SolvableHall.iSup_invariants_hyperplanes_eq_top ρ hp hq hqp hA hA1

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
