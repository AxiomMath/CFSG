module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.ARS.BasicBridge

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

theorem Opposite.exists_mem_eq_conjSub {G : Type*} [Group G] [Finite G] {R : Set (Subgroup G)}
    (hR : IsRootClass R) {A B E : Subgroup G} (hA : A ∈ R) (hE : E ∈ R) (h : Opposite A B)
    (hle : E ≤ A ⊔ B) (hne : E ≠ A) : ∃ a ∈ A, E = conjSub B a := by
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => hR.mul_self A hA a ha
  obtain ⟨x, hx, hxE⟩ := h.exists_conjSub_eq hsq hle (hR.isPGroup hE) (hR.card_eq hE hA)
  have hR1 := h.isElemAbRankOne_of_mul_self hsq
  have hx' : E.subgroupOf (A ⊔ B) = (A.subgroupOf (A ⊔ B)).map
      (MulAut.conj (⟨x, hx⟩ : ↥(A ⊔ B))).toMonoidHom := by
    rw [map_conj_subgroupOf_mk hx, hxE]
  have hne' : (A.subgroupOf (A ⊔ B)).map
      (MulAut.conj (⟨x, hx⟩ : ↥(A ⊔ B))).toMonoidHom ≠ A.subgroupOf (A ⊔ B) := by
    intro heq
    apply hne
    exact (subgroupOf_inj_of_le hle le_sup_left).1 (hx' ▸ heq)
  obtain ⟨a, ha, haE⟩ := hR1.exists_eq_of_map_conj_ne hne'
  have haA : (a : G) ∈ A := ha
  refine ⟨(a : G), haA, ?_⟩
  have hEsub : E.subgroupOf (A ⊔ B) = (conjSub B (a : G)).subgroupOf (A ⊔ B) := by
    rw [hx', haE, map_conj_subgroupOf_mk (x := (a : G)) a.2]
  exact (subgroupOf_inj_of_le hle (conjSub_le le_sup_right a.2)).1 hEsub

end CFSG.Timmesfeld.Transvection
