module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem6
public import CFSG.Quasithin.Vol2.Ch6NatA5
public import CFSG.Quasithin.Vol2.Ch6Skeleton

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem isTwoReducedIn_reducedAggregate (X : Subgroup G) :
    IsTwoReducedIn X (reducedAggregate X) := by
  rw [isTwoReducedIn_iff_isPrimeReduced_subgroupOf]
  refine ⟨Subgroup.map_subtype_le _, ?_⟩
  rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  exact isPrimeReduced_primeReducedAggregate 2

namespace Hyp611

theorem le_reducedAggregate (h : Hyp611 G T M L V n) : V ≤ reducedAggregate (L ⊔ T) :=
  calc V = (V.subgroupOf (L ⊔ T)).map (L ⊔ T).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le h.module.1).symm
    _ ≤ (primeReducedAggregate ↥(L ⊔ T) 2).map (L ⊔ T).subtype :=
        Subgroup.map_mono (le_primeReducedAggregate h.module.2.1)

theorem lemma_6_1_6_three (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h : Hyp611 G T M L V n) :
    ⁅V, L⁆ = ⁅reducedAggregate (L ⊔ T), L⁆ := by
  have hVR := h.le_reducedAggregate
  have hRred := isTwoReducedIn_reducedAggregate (L ⊔ T)
  have hnatV := (h.lemma_6_1_6_one_two h331 h432 h512 h614 h615).2.1
  have hVL : ⁅V, L⁆ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ := Subgroup.commutator_mono hVR le_rfl
  have hRL0 : ⁅reducedAggregate (L ⊔ T), L⁆ ≠ ⊥ := fun h0 =>
    h.module.2.2 (eq_bot_iff.mpr (h0 ▸ hVL))
  have hRLR : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ reducedAggregate (L ⊔ T) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hRred.2.1)
  have hRc : ∀ a ∈ ⁅reducedAggregate (L ⊔ T), L⁆, ∀ b ∈ ⁅reducedAggregate (L ⊔ T), L⁆,
      a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hRred.2.2.1 (hRLR ha) (hRLR hb)
  have hR : Hyp611 G T M L (reducedAggregate (L ⊔ T)) n :=
    { toHyp5_0_1 := h.toHyp5_0_1
      module := ⟨hRred.1, (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hRred).2, hRL0⟩
      not_a5 := by
        rintro ⟨rfl, hA5⟩
        exact false_of_isNatModCh5_le_isA5ModuleSum hnatV hVL hRc hA5
      nParam_eq_one := h.nParam_eq_one
      noLie := h.noLie }
  have hnatR := (hR.lemma_6_1_6_one_two h331 h432 h512 h614 h615).2.1
  rcases hnatR.irreducible ⁅V, L⁆ hVL (le_sup_left.trans h.sup_le_normalizer_commutator) with
    h0 | h0
  · exact absurd h0 h.module.2.2
  · exact h0

end Hyp611

theorem stmt6_1_6 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2) (h614 : Stmt6_1_4)
    (h615 : Stmt6_1_5) : Stmt6_1_6 := fun _ _ _ _ _ _ _ _ h =>
  ⟨(h.lemma_6_1_6_one_two h331 h432 h512 h614 h615).1,
    (h.lemma_6_1_6_one_two h331 h432 h512 h614 h615).2,
    h.lemma_6_1_6_three h331 h432 h512 h614 h615⟩

end CFSG.Quasithin.H13
