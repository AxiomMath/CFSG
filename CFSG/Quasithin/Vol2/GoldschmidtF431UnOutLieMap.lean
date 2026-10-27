module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieSub
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOutLie

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431

universe u

section Chain

variable {G : Type u} [Group G] (K₀ : Subgroup G)

theorem sub_reflTransGen {r : G → G → Prop} {r' : K₀ → K₀ → Prop}
    (hr : ∀ (a b : G) (ha : a ∈ K₀) (hb : b ∈ K₀), r a b → r' ⟨a, ha⟩ ⟨b, hb⟩)
    (hK : ∀ a b : G, r a b → a ∈ K₀ ∧ b ∈ K₀) {a b : G} (h : Relation.ReflTransGen r a b)
    (ha : a ∈ K₀) : ∀ hb : b ∈ K₀, Relation.ReflTransGen r' ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact fun _ => Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    intro hc
    have hb := (hK _ _ hbc).1
    exact (ih hb).tail (hr _ _ hb hc hbc)

theorem sub_spWf {T : Subgroup G} (hT : T ≤ K₀) (a : K₀) :
    spWf (T.subgroupOf K₀) a = (spWf T (a : G)).subgroupOf K₀ := by
  have hX : spTf T (a : G) ≤ K₀ := inf_le_left.trans hT
  have e : spTf (T.subgroupOf K₀) a = (spTf T (a : G)).subgroupOf K₀ :=
    sub_inf_centralizer K₀ a
  ext x
  rw [Subgroup.mem_subgroupOf, spWf, spWf, Subgroup.mem_inf, Subgroup.mem_inf, e]
  have h1 := sub_mem_iff_of_map K₀ (sub_centerOf_map K₀ hX) x
  have h2 : ∀ y : K₀, y ∈ ⁅(spTf T (a : G)).subgroupOf K₀, (spTf T (a : G)).subgroupOf K₀⁆ ↔
      (y : G) ∈ ⁅spTf T (a : G), spTf T (a : G)⁆ := fun y => by
    refine sub_mem_iff_of_map K₀ ?_ y
    rw [Subgroup.map_commutator, sub_map_subgroupOf K₀ hX]
  rw [h1, h2]

end Chain

end CFSG.Quasithin.H13.F431.Un
