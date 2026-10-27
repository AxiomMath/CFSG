module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartOne

open CFSG

theorem exists_embedding_into_centralizer {D G : Type*} [Group D] [Group G] (S E : Subgroup D)
    (hES : E ≤ S) (e : G ≃* S) (s : G) (c : S) (hs : e s = c⁻¹)
    (hc : ∀ x ∈ E, x * (c : D) = (c : D) * x) :
    ∃ ι : E →* Subgroup.centralizer ({s} : Set G), Function.Injective ι := by
  let ι0 : E →* G := e.symm.toMonoidHom.comp (Subgroup.inclusion hES)
  have hι0 : ∀ x : E, ι0 x ∈ Subgroup.centralizer ({s} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    have hcomm : Commute (Subgroup.inclusion hES x) c := Subtype.ext (hc x x.2)
    rw [map_mul, map_mul, hs]
    show e (e.symm (Subgroup.inclusion hES x)) * c⁻¹ = c⁻¹ * e (e.symm (Subgroup.inclusion hES x))
    rw [MulEquiv.apply_symm_apply]
    exact (hcomm.inv_right).eq
  refine ⟨ι0.codRestrict _ hι0, fun x y hxy => ?_⟩
  have h1 : ι0 x = ι0 y := congrArg Subtype.val hxy
  have h2 : Subgroup.inclusion hES x = Subgroup.inclusion hES y := e.symm.injective h1
  exact Subgroup.inclusion_injective hES h2

theorem exists_quasisimple_range_of_injective {Q C G : Type*} [Group Q] [Group C] [Group G]
    (ι : Q →* C) (hι : Function.Injective ι) (hq : IsQuasisimple Q)
    (hz : Nat.card (Subgroup.center Q) = 2) (θ : Q ⧸ Subgroup.center Q ≃* G) :
    ∃ K : Subgroup C, IsQuasisimple K ∧ Nat.card (Subgroup.center K) = 2 ∧
      Nonempty (K ⧸ Subgroup.center K ≃* G) := by
  let eK : Q ≃* ι.range := MonoidHom.ofInjective hι
  refine ⟨ι.range, CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hq, ?_, ?_⟩
  · exact (Nat.card_congr (Subgroup.centerCongr eK).symm.toEquiv).trans hz
  · exact ⟨(QuotientGroup.congr _ _ eK.symm (Subgroup.map_center_eq eK.symm)).trans θ⟩

end CFSG.RankThree.PartOne
