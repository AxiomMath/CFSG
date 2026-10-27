module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.CentralizerOfInnerTrivial
public import CFSG.Sporadic.SmallOddCore.Assembly

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Sporadic.SmallOddCore

theorem card_mulAut_eq_card_of_allInner {G : Type*} [Group G] (hc : center G = ⊥)
    (h : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) : Nat.card (MulAut G) = Nat.card G :=
  (Nat.card_congr (Equiv.ofBijective (MulAut.conj : G →* MulAut G)
    ⟨conj_injective_of_center_eq_bot hc, fun α => by
      obtain ⟨g, hg⟩ := h α
      exact ⟨g, hg.symm⟩⟩)).symm

theorem autModel_self_of_allInner {M : Type*} [Group M] {P : Subgroup M} (hc : center P = ⊥)
    (h : ∀ α : MulAut P, ∃ g : P, α = MulAut.conj g) : AutModel P P where
  le := le_rfl
  conj_mem := fun x hx _ hp => P.mul_mem (P.mul_mem hx hp) (P.inv_mem hx)
  surj := fun α => by
    obtain ⟨g, hg⟩ := h α
    exact ⟨g, g.2, fun p => by rw [hg]; simp [MulAut.conj_apply]⟩
  inj := fun x hx hcomm => by
    have hmem : (⟨x, hx⟩ : P) ∈ center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2).symm
    rw [hc, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem

end CFSG.RankThree.PartOne
