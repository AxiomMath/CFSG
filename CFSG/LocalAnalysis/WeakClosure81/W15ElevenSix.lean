module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenX

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace XData15

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem ne_bot (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) : X ≠ ⊥ := by
  intro hbot
  apply c.not_le_iHull15
  rw [← hX.sup_eq, hbot, bot_sup_eq]

theorem not_le_M (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    ¬ X ≤ M := by
  intro hXM
  haveI : Fact p.Prime := ⟨c.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV₀2 : IsPGroup 2 V₀ := c.cex.hyp.isPGroup.to_le c.cex.hyp.h6.le
  have hnorm : ∀ x ∈ X, ∀ y ∈ V₀, x * y * x⁻¹ ∈ V₀ := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 (by rw [c.cex.hyp.normalizer₀]; exact hXM hx) y).1 hy
  have hXV : X ≤ V₀ := by
    rw [← hX.comm_eq]
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    have hy' : y ∈ V₀ := (Subgroup.zpowers_le.2 hX.mem) hy
    rw [commutatorElement_def]
    exact V₀.mul_mem (hnorm x hx y hy') (V₀.inv_mem hy')
  have hdis := IsPGroup.disjoint_of_ne p 2 c.p_ne_two X X hX.isPGroup (hV₀2.to_le hXV)
  exact hX.ne_bot c (disjoint_self.1 hdis)

theorem inf_centralizer_X (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    V₀ ⊓ centralizer (X : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  by_contra hw1
  refine hX.not_le_M c fun x hx => c.cex.hyp.centralizer_le hw.1 hw1 ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact (Subgroup.mem_centralizer_iff.1 hw.2 x hx).symm

theorem inf_centralizer_kHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) : V₀ ⊓ centralizer (kHull15 V₀ H : Set G) = ⊥ :=
  eq_bot_iff.2 <| (inf_le_inf_left V₀ (Subgroup.centralizer_le hX.le_kHull15)).trans
    (hX.inf_centralizer_X c).le

end XData15

end CFSG.LocalAnalysis.WeakClosure81
