module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lbl0

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem ncard_nbr {o : V} (hv : valence Γ o = 5) : (Γ.neighborSet o).ncard = 5 := by
  rw [← Nat.card_coe_set_eq]
  exact hv

theorem finite_nbr {o : V} (hv : valence Γ o = 5) : (Γ.neighborSet o).Finite :=
  Set.finite_of_ncard_ne_zero (by rw [ncard_nbr hv]; norm_num)

theorem exists_nbr_not_mem {o : V} (hv : valence Γ o = 5) (S : Finset V) (hS : S.card ≤ 4) :
    ∃ r : V, Γ.Adj o r ∧ r ∉ S := by
  by_contra hcon
  push Not at hcon
  have hsub : Γ.neighborSet o ⊆ (S : Set V) := fun r hr => hcon r hr
  have := Set.ncard_le_ncard hsub S.finite_toSet
  rw [ncard_nbr hv, Set.ncard_coe_finset] at this
  omega

theorem exists_five_nbrs {o a₁ a₂ a₃ : V} (hv : valence Γ o = 5) (n12 : a₁ ≠ a₂)
    (n13 : a₁ ≠ a₃) (n23 : a₂ ≠ a₃) :
    ∃ a₄ a₅ : V, Γ.Adj o a₄ ∧ Γ.Adj o a₅ ∧ [a₁, a₂, a₃, a₄, a₅].Nodup := by
  classical
  obtain ⟨a₄, h₄, hn₄⟩ := exists_nbr_not_mem hv {a₁, a₂, a₃}
    (Finset.card_le_three.trans (by norm_num))
  obtain ⟨a₅, h₅, hn₅⟩ := exists_nbr_not_mem hv {a₁, a₂, a₃, a₄}
    (Finset.card_le_four)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn₄ hn₅
  have n14 : a₁ ≠ a₄ := fun h => hn₄.1 h.symm
  have n24 : a₂ ≠ a₄ := fun h => hn₄.2.1 h.symm
  have n34 : a₃ ≠ a₄ := fun h => hn₄.2.2 h.symm
  have n15 : a₁ ≠ a₅ := fun h => hn₅.1 h.symm
  have n25 : a₂ ≠ a₅ := fun h => hn₅.2.1 h.symm
  have n35 : a₃ ≠ a₅ := fun h => hn₅.2.2.1 h.symm
  have n45 : a₄ ≠ a₅ := fun h => hn₅.2.2.2 h.symm
  exact ⟨a₄, a₅, h₄, h₅, by simp [List.nodup_cons, n12, n13, n23, n14, n24, n34, n15, n25, n35,
    n45]⟩

theorem mem_of_five {o : V} (hv : valence Γ o = 5) {l : List V} (hl : l.Nodup)
    (hlen : l.length = 5) (hadj : ∀ u ∈ l, Γ.Adj o u) : ∀ w, Γ.Adj o w → w ∈ l := by
  classical
  intro w hw
  by_contra hnot
  have hsub : ((insert w l.toFinset : Finset V) : Set V) ⊆ Γ.neighborSet o := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_insert, List.mem_toFinset] at hx
    rcases hx with rfl | hx
    · exact hw
    · exact hadj x hx
  have h1 := Set.ncard_le_ncard hsub (finite_nbr hv)
  rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simpa using hnot),
    List.toFinset_card_of_nodup hl, hlen, ncard_nbr hv] at h1
  omega

structure LblBase (Γ : SimpleGraph V) (z : G) (α o : V) : Prop where
  adj : Γ.Adj α o
  v5 : valence Γ o = 5
  cinv : z ∈ Cinv G α
  ball : z ∈ ballStab Γ G 2 α
  prod5 : ∀ l : List V, l.Nodup → l.length = 5 → (∀ u ∈ l, Γ.Adj o u) →
    (l.map (Lb z α)).prod = 1

theorem mkBase (F : FanTree Γ G) {z : G} {α o : V} (hadj : Γ.Adj α o)
    (hv5 : valence Γ o = 5) (hcinv : z ∈ Cinv G α) (hball : z ∈ ballStab Γ G 2 α)
    (hprod : ∀ (l : List V) (h : V → G), l.Nodup → (∀ u, u ∈ l ↔ Γ.Adj o u) →
      (∀ u, Γ.Adj o u → h u • α = u) →
        (l.map fun u => h u * z * (h u)⁻¹).Pairwise Commute ∧
          (l.map fun u => h u * z * (h u)⁻¹).prod = 1) :
    LblBase Γ z α o where
  adj := hadj
  v5 := hv5
  cinv := hcinv
  ball := hball
  prod5 := by
    intro l hl hlen hadj'
    have hmem := mem_of_five hv5 hl hlen hadj'
    have hex : ∀ u : V, ∃ g : G, Γ.Adj o u → g • α = u := fun u => by
      by_cases hu : Γ.Adj o u
      · obtain ⟨g, hg⟩ := exists_conj_of_adj F hadj hu
        exact ⟨g, fun _ => hg⟩
      · exact ⟨1, fun h => absurd h hu⟩
    choose h hh using hex
    have hp := (hprod l h hl (fun u => ⟨fun hu => hadj' u hu, fun hu => hmem u hu⟩) hh).2
    have hmap : l.map (fun u => h u * z * (h u)⁻¹) = l.map (Lb z α) := by
      apply List.map_congr_left
      intro u hu
      exact (Lb_eq hcinv (hh u (hadj' u hu))).symm
    rw [← hmap]
    exact hp

structure LblCtx (Γ : SimpleGraph V) (z : G) (α o : V) : Prop where
  adj : Γ.Adj α o
  v5 : valence Γ o = 5
  cinv : z ∈ Cinv G α
  ball : z ∈ ballStab Γ G 2 α
  prod5 : ∀ l : List V, l.Nodup → l.length = 5 → (∀ u ∈ l, Γ.Adj o u) →
    (l.map (Lb z α)).prod = 1
  ne : ∀ u u' : V, Γ.Adj o u → Γ.Adj o u' → u ≠ u' → Lb z α u ≠ Lb z α u'

namespace LblCtx

variable {z : G} {α o : V}

theorem commute (F : FanTree Γ G) (C : LblCtx Γ z α o) {u u' : V} (h2 : Γ.Adj o u)
    (h3 : Γ.Adj o u') : Lb z α u * Lb z α u' = Lb z α u' * Lb z α u :=
  Lb_commute F C.cinv C.ball C.adj h2 h3

theorem conj_ex (F : FanTree Γ G) (C : LblCtx Γ z α o) {u : V} (h2 : Γ.Adj o u) :
    ∃ g : G, g • α = u := exists_conj_of_adj F C.adj h2

theorem sq (F : FanTree Γ G) (C : LblCtx Γ z α o) {u : V} (h2 : Γ.Adj o u) :
    Lb z α u * Lb z α u = 1 := Lb_mul_self C.cinv (C.conj_ex F h2)

theorem ne_one (F : FanTree Γ G) (C : LblCtx Γ z α o) {u : V} (h2 : Γ.Adj o u) :
    Lb z α u ≠ 1 := Lb_ne_one C.cinv (C.conj_ex F h2)

theorem prod4_ne (F : FanTree Γ G) (C : LblCtx Γ z α o) {p q p' q' : V} (hp : Γ.Adj o p)
    (hq : Γ.Adj o q) (hp' : Γ.Adj o p') (hq' : Γ.Adj o q') (hpq : p ≠ q) (hpp : p ≠ p')
    (hpq' : p ≠ q') (hqp : q ≠ p') (hqq : q ≠ q') (hpq2 : p' ≠ q')
    (hW : Lb z α p * Lb z α q = Lb z α p' * Lb z α q') : False := by
  classical
  obtain ⟨r, hr, hnr⟩ := exists_nbr_not_mem C.v5 {p, q, p', q'} Finset.card_le_four
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnr
  have hl : [p, q, p', q', r].Nodup := by
    have n1 : p ≠ r := fun h => hnr.1 h.symm
    have n2 : q ≠ r := fun h => hnr.2.1 h.symm
    have n3 : p' ≠ r := fun h => hnr.2.2.1 h.symm
    have n4 : q' ≠ r := fun h => hnr.2.2.2 h.symm
    simp [List.nodup_cons, hpq, hpp, hpq', hqp, hqq, hpq2, n1, n2, n3, n4]
  have h1 := C.prod5 [p, q, p', q', r] hl rfl (by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> assumption)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h1
  have hc : Lb z α q * Lb z α p = Lb z α p * Lb z α q := C.commute F hq hp
  have hWW : (Lb z α p * Lb z α q) * (Lb z α p * Lb z α q) = 1 := by
    calc (Lb z α p * Lb z α q) * (Lb z α p * Lb z α q)
        = Lb z α p * (Lb z α q * Lb z α p) * Lb z α q := by simp only [mul_assoc]
      _ = Lb z α p * (Lb z α p * Lb z α q) * Lb z α q := by rw [hc]
      _ = (Lb z α p * Lb z α p) * (Lb z α q * Lb z α q) := by simp only [mul_assoc]
      _ = 1 := by rw [C.sq F hp, C.sq F hq, one_mul]
  have h2 : Lb z α r = 1 := by
    have e : Lb z α p * (Lb z α q * (Lb z α p' * (Lb z α q' * Lb z α r))) =
        ((Lb z α p * Lb z α q) * (Lb z α p * Lb z α q)) * Lb z α r := by
      rw [← mul_assoc (Lb z α p') (Lb z α q'), ← hW]
      simp only [mul_assoc]
    rw [e, hWW, one_mul] at h1
    exact h1
  exact C.ne_one F hr h2

theorem two_subset (F : FanTree Γ G) (C : LblCtx Γ z α o) {p q p' q' : V} (hp : Γ.Adj o p)
    (hq : Γ.Adj o q) (hp' : Γ.Adj o p') (hq' : Γ.Adj o q') (hpq : p ≠ q) (hpq2 : p' ≠ q')
    (hW : Lb z α p * Lb z α q = Lb z α p' * Lb z α q') :
    (p = p' ∧ q = q') ∨ (p = q' ∧ q = p') := by
  by_cases h1 : p = p'
  · subst h1
    left
    refine ⟨rfl, ?_⟩
    by_contra hne
    exact C.ne q q' hq hq' hne (mul_left_cancel hW)
  by_cases h2 : p = q'
  · subst h2
    right
    refine ⟨rfl, ?_⟩
    by_contra hne
    rw [C.commute F hp' hp] at hW
    exact C.ne q p' hq hp' hne (mul_left_cancel hW)
  by_cases h3 : q = p'
  · subst h3
    right
    refine ⟨?_, rfl⟩
    by_contra hne
    rw [C.commute F hp hq] at hW
    exact C.ne p q' hp hq' hne (mul_left_cancel hW)
  by_cases h4 : q = q'
  · subst h4
    left
    refine ⟨?_, rfl⟩
    by_contra hne
    exact C.ne p p' hp hp' hne (mul_right_cancel hW)
  exact (C.prod4_ne F hp hq hp' hq' hpq h1 h2 h3 h4 hpq2 hW).elim

end LblCtx

end P514

end CFSG.Quasithin.Fan86
