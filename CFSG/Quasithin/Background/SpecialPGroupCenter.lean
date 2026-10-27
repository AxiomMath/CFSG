module

public import CFSG.Quasithin.Background.F1Lemma10
public import CFSG.Walter.Cited.HuppertBasic
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem IsSpecialPGroup.commutator_le_centerOf {p : ℕ} {Q : Subgroup G}
    (h : IsSpecialPGroup p ↥Q) : ⁅Q, Q⁆ ≤ centerOf Q := by
  obtain ⟨-, hab | ⟨hcomm, -, -⟩⟩ := h
  · have hcenter : Q ≤ centerOf Q := by
      intro x hx
      exact Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (hab.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)⟩
    exact (Subgroup.commutator_le_self Q).trans hcenter
  · have hZ : ∀ w ∈ Subgroup.center ↥Q, (w : G) ∈ centerOf Q := fun w hw =>
      Subgroup.mem_inf.mpr ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, hy⟩)⟩
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine hZ ⁅(⟨x, hx⟩ : ↥Q), (⟨y, hy⟩ : ↥Q)⁆ ?_
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem IsSpecialPGroup.pow_mem_centerOf {p : ℕ} [Fact p.Prime] {Q : Subgroup G} [Finite ↥Q]
    (h : IsSpecialPGroup p ↥Q) {x : G} (hx : x ∈ Q) : x ^ p ∈ centerOf Q := by
  obtain ⟨hp, hab | ⟨-, hfr, -⟩⟩ := h
  · exact Subgroup.mem_inf.mpr ⟨Q.pow_mem hx p,
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (hab.1.is_comm.comm ⟨y, hy⟩ ⟨x ^ p, Q.pow_mem hx p⟩)⟩
  · have hZ : ∀ w ∈ Subgroup.center ↥Q, (w : G) ∈ centerOf Q := fun w hw =>
      Subgroup.mem_inf.mpr ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, hy⟩)⟩
    refine hZ (⟨x, hx⟩ ^ p) ?_
    rw [← hfr]
    exact CFSG.Walter.Huppert.mem_frattini_of_isPGroup hp _

end CFSG.Quasithin
