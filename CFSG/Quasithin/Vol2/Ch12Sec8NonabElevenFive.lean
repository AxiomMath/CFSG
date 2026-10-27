module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

namespace Hyp1281Two

theorem relIndex_wOfU_eq_two (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    (wOfU T M).relIndex (uOfL22 T M) = 2 := by
  obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ uOfL22 T M, u₀ ∉ wOfU T M := by
    by_contra hall
    push Not at hall
    exact h.not_le_centralizer_VZ_of_nonabelian hU fun u hu => (hall u hu).2
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨u₀, hu₀U⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : G) ∈ wOfU T M
  · right
    refine ⟨hb, fun hbu => hu₀W ?_⟩
    have := (wOfU T M).mul_mem ((wOfU T M).inv_mem hb) hbu
    simpa using this
  · left
    refine ⟨?_, hb⟩
    have hb' : (b : G)⁻¹ ∉ wOfU T M := fun hb'' => hb (by simpa using (wOfU T M).inv_mem hb'')
    rcases h.mem_wOfU_or_inv_mul_mem ((uOfL22 T M).inv_mem b.2) hu₀U hb' with h1 | h1
    · exact absurd h1 hu₀W
    · simpa using h1

section

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g)

include h hU hg

theorem lemma_12_8_11_five :
    2 * (wOfU T M ⊓ rconj (wOfU T M) g ⊓ centerOf (uOfL22 T M)).relIndex
        (wOfU T M ⊓ rconj (wOfU T M) g) *
      (rconj (centerOf (uOfL22 T M)) g ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)).relIndex
        (rconj (wOfU T M) g) = (centerOf (uOfL22 T M)).relIndex (uOfL22 T M) := by
  have hZuU : centerOf (uOfL22 T M) ≤ uOfL22 T M := inf_le_left
  have hEW : wOfU T M ⊓ rconj (wOfU T M) g ≤ wOfU T M := inf_le_left
  have hEU : wOfU T M ⊓ rconj (wOfU T M) g ≤ uOfL22 T M := hEW.trans (wOfU_le_uOfL22 T M)
  have hZuW : centerOf (uOfL22 T M) ≤ wOfU T M := centerOf_uOfL22_le_wOfU T M
  have hsupW : centerOf (uOfL22 T M) ⊔ (wOfU T M ⊓ rconj (wOfU T M) g) ≤ wOfU T M :=
    sup_le hZuW hEW
  have hchain : (centerOf (uOfL22 T M)).relIndex (uOfL22 T M) =
      (centerOf (uOfL22 T M)).relIndex (centerOf (uOfL22 T M) ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)) *
        (centerOf (uOfL22 T M) ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)).relIndex (wOfU T M) *
          (wOfU T M).relIndex (uOfL22 T M) := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hsupW,
      Subgroup.relIndex_mul_relIndex _ _ _ hZuW (wOfU_le_uOfL22 T M)]
  have hNorm : uOfL22 T M ≤ Subgroup.normalizer (centerOf (uOfL22 T M) : Set G) :=
    fun u hu => normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer hu)
  have hsecond : (centerOf (uOfL22 T M)).relIndex
      (centerOf (uOfL22 T M) ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)) =
      (wOfU T M ⊓ rconj (wOfU T M) g ⊓ centerOf (uOfL22 T M)).relIndex
        (wOfU T M ⊓ rconj (wOfU T M) g) := by
    have : ((centerOf (uOfL22 T M)).subgroupOf (uOfL22 T M)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hNorm
    have h1 := Subgroup.relIndex_sup_left (K := (centerOf (uOfL22 T M)).subgroupOf (uOfL22 T M))
      (H := (wOfU T M ⊓ rconj (wOfU T M) g).subgroupOf (uOfL22 T M))
    rw [← Subgroup.subgroupOf_sup hZuU hEU, Subgroup.relIndex_subgroupOf (sup_le hZuU hEU),
      Subgroup.relIndex_subgroupOf hEU] at h1
    rw [h1, ← Subgroup.inf_relIndex_right, inf_comm]
  have hgE : g ∈ Subgroup.normalizer ((wOfU T M ⊓ rconj (wOfU T M) g : Subgroup G) : Set G) :=
    h.sup_le_normalizer_inf_rconj_wOfU hU hg (hg.mem_sup _)
  have hconj : ∀ A B : Subgroup G, (rconj A g).relIndex (rconj B g) = A.relIndex B := fun A B =>
    Subgroup.relIndex_map_map_of_injective A B (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulEquiv.injective _)
  have hthird : (rconj (centerOf (uOfL22 T M)) g ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)).relIndex
      (rconj (wOfU T M) g) =
      (centerOf (uOfL22 T M) ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)).relIndex (wOfU T M) := by
    have h1 := hconj (centerOf (uOfL22 T M) ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)) (wOfU T M)
    rw [rconj_sup_eq, rconj_eq_of_mem_normalizer hgE] at h1
    exact h1
  rw [hthird, hchain, hsecond, h.relIndex_wOfU_eq_two hU]
  ring

end

end Hyp1281Two

end CFSG.Quasithin
