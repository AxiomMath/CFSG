module

public import CFSG.RankThree.FFModules.Offenders
import CFSG.GroupTheory.HyperplaneDecomposition
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.RankThree.FFModules (fixSub mem_fixSub)

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def hyperplaneSet (q : ℕ) (A : Subgroup G) : Set (Subgroup G) :=
  {B | B ≤ A ∧ B.relIndex A = q}

private theorem fixSub_eq_invariants (ρ : Representation (ZMod 2) G V) (A : Subgroup G) :
    fixSub ρ A = Representation.invariants (ρ.comp A.subtype) := by
  ext v
  exact ⟨fun h a => h a a.2, fun h a ha => h ⟨a, ha⟩⟩

theorem iSupIndep_fixSub_hyperplane (ρ : Representation (ZMod 2) G V) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian q A)
    (hfix : fixSub ρ A = ⊥) :
    iSupIndep (fun B : hyperplaneSet q A => fixSub ρ (B : Subgroup G)) := by
  simp only [fixSub_eq_invariants] at hfix ⊢
  exact CFSG.SolvableHall.iSupIndep_invariants_hyperplanes ρ Nat.prime_two hq hq2 hA hfix

theorem iSup_fixSub_hyperplane_eq_top (ρ : Representation (ZMod 2) G V) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian q A) (hA1 : A ≠ ⊥) :
    ⨆ B : hyperplaneSet q A, fixSub ρ (B : Subgroup G) = ⊤ := by
  simp only [fixSub_eq_invariants]
  exact CFSG.SolvableHall.iSup_invariants_hyperplanes_eq_top ρ Nat.prime_two hq hq2 hA hA1

end CFSG.LocalAnalysis.UniquenessCase.UCK
