module

public import CFSG.Permutation.FiveTransitive.Degree31FifteenFixed
public import Mathlib.Data.Set.Card.Arithmetic

public section

namespace CFSG

namespace FiveTransitive.Degree31FivePairsExclusion

open MulAction
open scoped BigOperators

private theorem fixes_pair
    {X : Type*} (g : X → X) (hg : Function.Injective g)
    (c : Set X) (hc : c.ncard = 2) (hstable : ∀ x ∈ c, g x ∈ c)
    (a : X) (ha : a ∈ c) (hga : g a = a) : ∀ x ∈ c, g x = x := by
  obtain ⟨v,w,hvw,hcset⟩ := Set.ncard_eq_two.mp hc
  have ha' : a = v ∨ a = w := by simpa only [hcset,Set.mem_insert_iff,Set.mem_singleton_iff] using ha
  intro x hx
  have hx' : x = v ∨ x = w := by simpa only [hcset,Set.mem_insert_iff,Set.mem_singleton_iff] using hx
  have hgx : g x = v ∨ g x = w := by
    simpa only [hcset,Set.mem_insert_iff,Set.mem_singleton_iff] using hstable x hx
  rcases ha' with rfl | rfl
  · rcases hx' with rfl | rfl
    · exact hga
    · exact hgx.resolve_left (fun he => hvw (hg (hga.trans he.symm)))
  · rcases hx' with rfl | rfl
    · exact hgx.resolve_right (fun he => hvw (hg (he.trans hga.symm)))
    · exact hga

private theorem card_le_five_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (H : Subgroup P) (s : Set X) (hs : s.ncard = 5)
    (hHle : H ≤ fixingSubgroup P s) (c : Fin 5 → Set X)
    (hc : ∀ i, (c i).ncard = 2)
    (hdis : Pairwise (fun i j => Disjoint (c i) (c j)))
    (hcs : ∀ i, Disjoint (c i) s)
    (hstable : ∀ (h : H) i x, x ∈ c i → h • x ∈ c i) : Nat.card H ≤ 512 := by
  classical
  let D (i : Fin 5) : SubMulAction H X :=
    { carrier := c i
      smul_mem' := fun h x hx => hstable h i x hx }
  let Y := (i : Fin 5) → D i
  let _ : ∀ i, Fintype (D i) := fun _ => Fintype.ofFinite _
  have hD (i : Fin 5) : Fintype.card (D i) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (c i) = 2
    rw [Nat.card_coe_set_eq,hc]
  have hY : Fintype.card Y = 32 := by
    rw [Fintype.card_pi]
    simp only [hD,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    norm_num
  let _ : ∀ i, Nonempty (D i) := fun i => Fintype.card_pos_iff.mp (by rw [hD]; norm_num)
  let y : Y := fun i => Classical.choice (inferInstance : Nonempty (D i))
  let K := stabilizer H y
  have hindex : K.index ≤ 32 := by
    rw [index_stabilizer]
    have hh := Set.ncard_le_ncard (Set.subset_univ (orbit H y))
    rw [Set.ncard_univ,Nat.card_eq_fintype_card,hY] at hh
    exact hh
  let A : Set X := s ∪ ⋃ i, c i
  have hpaircard : (⋃ i, c i).ncard = 10 := by
    rw [Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) hdis]
    simp only [hc,finsum_eq_sum_of_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hAdis : Disjoint s (⋃ i, c i) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hy
    exact Set.disjoint_left.mp (hcs i) hi hx
  have hA : A.ncard = 15 := by rw [Set.ncard_union_eq hAdis,hs,hpaircard]
  let R : Subgroup P := K.map H.subtype
  have hRcard : Nat.card R = Nat.card K := Subgroup.card_map_of_injective H.subtype_injective
  have hRfix : ∀ r : R, ∀ x ∈ A, r • x = x := by
    intro r x hx
    obtain ⟨q,hq,he⟩ := r.property
    change r.val • x = x
    rw [← he]
    rcases hx with hx | hx
    · exact (mem_fixingSubgroup_iff P).mp (hHle q.property) x hx
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      have hqy : q • y = y := hq
      have hqa : q.val.val (y i).val = (y i).val :=
        congrArg Subtype.val (congrFun hqy i)
      exact fixes_pair q.val.val q.val.val.injective (c i) (hc i)
        (hstable q i) (y i).val (y i).property hqa x hi
  have hR16 := Degree31FifteenFixed.card_le_sixteen P hcard h5 hnotAlt R A hA hRfix
  rw [hRcard] at hR16
  have hm := K.index_mul_card
  have hb := Nat.mul_le_mul hindex hR16
  rw [hm] at hb
  exact hb

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (H : Subgroup P) (hHcard : Nat.card H = 4096)
    (s : Set X) (hs : s.ncard = 5) (hHle : H ≤ fixingSubgroup P s)
    (c : Fin 5 → Set X) (hc : ∀ i, (c i).ncard = 2)
    (hdis : Pairwise (fun i j => Disjoint (c i) (c j)))
    (hcs : ∀ i, Disjoint (c i) s)
    (hstable : ∀ (h : H) i x, x ∈ c i → h • x ∈ c i) : False := by
  have hbound := card_le_five_twelve P hcard h5 hnotAlt H s hs hHle c hc hdis hcs hstable
  omega

end FiveTransitive.Degree31FivePairsExclusion

end CFSG
