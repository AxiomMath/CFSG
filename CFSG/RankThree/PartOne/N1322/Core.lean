module

public import CFSG.RankThree.PartOne.N1322.MonoExtract
public import CFSG.RankThree.PartOne.N1322.CoreHyp

public section

namespace CFSG.RankThree.PartOne.N1322

open Equiv CFSG.RankThree.SubgroupLists

theorem two_ne_zero_of_five_le {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

@[expose] def PrimitiveResidual : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (d : CoreData (ZMod p)), CoreHyp d → IsTransitiveMonomial d.X

theorem core_main (hres : PrimitiveResidual) {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)}
    (h : CoreHyp d) :
    d.n = 4 ∧ Nonempty (d.X ≃* Multiplicative (ZMod 2) × Perm (Fin 4)) :=
  core_of_monomial (two_ne_zero_of_five_le h.p5) h.toMonoHyp (hres p d h)

end CFSG.RankThree.PartOne.N1322
