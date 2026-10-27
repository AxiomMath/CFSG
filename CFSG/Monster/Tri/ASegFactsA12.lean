module

public import CFSG.Monster.Tri.ASegFactsFusion
public import CFSG.Monster.GMS.S46Basic
public import CFSG.Monster.GMS.NotConj

public section

namespace CFSG.Monster.Tri

open Equiv Equiv.Perm SimpleGraph CFSG.Monster.GMS CFSG.Monster.GMS.S36Lines
  CFSG.Monster.GMS.S46 CFSG.Blueprint.NativeSporadic

section Perms

private def pt (i : ℕ) : Fin 12 := Fin.ofNat 12 (i + 11)

private def sw (i j : ℕ) : Fin 12 × Fin 12 := (pt i, pt j)

private def tr (i j : ℕ) : Perm (Fin 12) := swap (pt i) (pt j)

private def alt (p : Perm (Fin 12)) (h : sign p = 1 := by decide) : alternatingGroup (Fin 12) :=
  ⟨p, mem_alternatingGroup.mpr h⟩

private def swapsProd : List (Fin 12 × Fin 12) → Perm (Fin 12)
  | [] => 1
  | (p, q) :: l => swap p q * swapsProd l

private def DisjointSwaps : List (Fin 12 × Fin 12) → Prop
  | [] => True
  | (p, q) :: l => p ≠ q ∧ swapsProd l p = p ∧ swapsProd l q = q ∧ DisjointSwaps l

private instance (l : List (Fin 12 × Fin 12)) : Decidable (DisjointSwaps l) := by
  induction l with
  | nil => exact isTrue trivial
  | cons pq l ih =>
    obtain ⟨p, q⟩ := pq
    exact inferInstanceAs
      (Decidable (p ≠ q ∧ swapsProd l p = p ∧ swapsProd l q = q ∧ DisjointSwaps l))

private theorem cycleType_swapsProd :
    ∀ l : List (Fin 12 × Fin 12), DisjointSwaps l →
      (swapsProd l).cycleType = Multiset.replicate l.length 2
  | [], _ => by simp [swapsProd]
  | (p, q) :: l, ⟨hpq, hp, hq, hl⟩ => by
    have hdisj : Disjoint (swap p q) (swapsProd l) := by
      intro x
      by_cases hxp : x = p
      · exact Or.inr (hxp ▸ hp)
      by_cases hxq : x = q
      · exact Or.inr (hxq ▸ hq)
      exact Or.inl (swap_apply_of_ne_of_ne hxp hxq)
    rw [swapsProd, hdisj.cycleType_mul, isSwap_iff_cycleType.mp ⟨p, q, hpq, rfl⟩,
      cycleType_swapsProd l hl, List.length_cons, Multiset.replicate_succ]
    rfl

private abbrev IsTwoA (σ : alternatingGroup (Fin 12)) : Prop :=
  (σ : Perm (Fin 12)).cycleType = {2, 2} ∨ (σ : Perm (Fin 12)).cycleType = {2, 2, 2, 2, 2, 2}

private abbrev IsTwoB (σ : alternatingGroup (Fin 12)) : Prop :=
  (σ : Perm (Fin 12)).cycleType = {2, 2, 2, 2}

private theorem isTwoA_of {σ : alternatingGroup (Fin 12)} {l : List (Fin 12 × Fin 12)}
    (h : (σ : Perm (Fin 12)) = swapsProd l ∧ DisjointSwaps l ∧ (l.length = 2 ∨ l.length = 6)) :
    IsTwoA σ := by
  obtain ⟨h1, h2, h3 | h3⟩ := h
  · left
    rw [h1, cycleType_swapsProd l h2, h3]
    rfl
  · right
    rw [h1, cycleType_swapsProd l h2, h3]
    rfl

private theorem isTwoB_of {σ : alternatingGroup (Fin 12)} {l : List (Fin 12 × Fin 12)}
    (h : (σ : Perm (Fin 12)) = swapsProd l ∧ DisjointSwaps l ∧ l.length = 4) : IsTwoB σ := by
  obtain ⟨h1, h2, h3⟩ := h
  show (σ : Perm (Fin 12)).cycleType = {2, 2, 2, 2}
  rw [h1, cycleType_swapsProd l h2, h3]
  rfl

private def u85 : alternatingGroup (Fin 12) := alt (tr 1 2 * tr 3 4)

private def v85 : alternatingGroup (Fin 12) := alt (tr 1 4 * tr 2 3)

private def x85 : alternatingGroup (Fin 12) := alt (tr 5 6 * tr 7 8)

private def c85 : alternatingGroup (Fin 12) :=
  alt (tr 1 3 * tr 2 4 * tr 5 7 * tr 6 8 * tr 9 10 * tr 11 12)

end Perms

section Model

variable {G : Type*} [Group G] {a z₀ : G} {φ : alternatingGroup (Fin 12) →* G}

set_option maxRecDepth 100000 in
theorem config85 (h : S36Lines.A12Fusion a z₀ φ) :
    ∃ b t t' c : G, Cfg a z₀ b t t' false true true true ∧
      c ∈ twoANbr a b ∩ twoANbr a t ∩ twoANbr a t' := by
  have hb : IsConj a (φ u85) := h.isConj_a _ (isTwoA_of (l := [sw 1 2, sw 3 4]) (by decide))
  have ht : IsConj a (φ v85) := h.isConj_a _ (isTwoA_of (l := [sw 1 4, sw 2 3]) (by decide))
  have hbt : IsConj a (φ u85 * φ v85) := by
    rw [← map_mul]
    exact h.isConj_a _ (isTwoA_of (l := [sw 1 3, sw 2 4]) (by decide))
  have ht' : IsConj a (φ x85) := h.isConj_a _ (isTwoA_of (l := [sw 5 6, sw 7 8]) (by decide))
  have hbt' : IsConj z₀ (φ u85 * φ x85) := by
    rw [← map_mul]
    exact h.isConj_z _ (isTwoB_of (l := [sw 1 2, sw 3 4, sw 5 6, sw 7 8]) (by decide))
  have htt' : IsConj z₀ (φ v85 * φ x85) := by
    rw [← map_mul]
    exact h.isConj_z _ (isTwoB_of (l := [sw 1 4, sw 2 3, sw 5 6, sw 7 8]) (by decide))
  have hbtt' : IsConj z₀ (φ u85 * (φ v85 * φ x85)) := by
    rw [← map_mul, ← map_mul]
    exact h.isConj_z _ (isTwoB_of (l := [sw 1 3, sw 2 4, sw 5 6, sw 7 8]) (by decide))
  have hc : IsConj a (φ c85) := h.isConj_a _
    (isTwoA_of (l := [sw 1 3, sw 2 4, sw 5 7, sw 6 8, sw 9 10, sw 11 12]) (by decide))
  have hbc : IsConj a (φ u85 * φ c85) := by
    rw [← map_mul]
    exact h.isConj_a _
      (isTwoA_of (l := [sw 1 4, sw 2 3, sw 5 7, sw 6 8, sw 9 10, sw 11 12]) (by decide))
  have htc : IsConj a (φ v85 * φ c85) := by
    rw [← map_mul]
    exact h.isConj_a _
      (isTwoA_of (l := [sw 1 2, sw 3 4, sw 5 7, sw 6 8, sw 9 10, sw 11 12]) (by decide))
  have ht'c : IsConj a (φ x85 * φ c85) := by
    rw [← map_mul]
    exact h.isConj_a _
      (isTwoA_of (l := [sw 1 3, sw 2 4, sw 5 8, sw 6 7, sw 9 10, sw 11 12]) (by decide))
  exact ⟨φ u85, φ v85, φ x85, φ c85, Cfg.of_two hb ⟨ht, hbt⟩ ⟨ht', hbt'⟩ ⟨htt', hbtt'⟩,
    ⟨⟨hc, hbc⟩, ⟨hc, htc⟩⟩, ⟨hc, ht'c⟩⟩

end Model

section Eight5

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem conj_mem_twoANbr {x w : G} (g : G) (h : w ∈ twoANbr a x) :
    g * w * g⁻¹ ∈ twoANbr a (g * x * g⁻¹) := by
  refine ⟨h.1.trans (isConj_conj_self g w), ?_⟩
  have e : g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
  rw [e]
  exact h.2.trans (isConj_conj_self g _)

theorem aseg_h85_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (F : ASegFacts a z₀) :
    ∀ x u v : ConjVert a, (x : G) * u = u * x → (x : G) * v = v * x →
      (twoAGraph a).Adj u v →
        (u = x ∨ (twoAGraph a).Adj u x) ∨ (v = x ∨ (twoAGraph a).Adj v x) ∨
          ∃ c : ConjVert a, (twoAGraph a).Adj c x ∧ (twoAGraph a).Adj c u ∧
            (twoAGraph a).Adj c v := by
  intro x u v hxu hxv huv
  have ha : orderOf a = 2 := hG.1.1
  have hz : orderOf z₀ = 2 := hG.2.1
  have hnc : ¬ IsConj a z₀ := GMSF1Type.not_isConj hG
  by_cases hu : u = x ∨ (twoAGraph a).Adj u x
  · exact Or.inl hu
  by_cases hv : v = x ∨ (twoAGraph a).Adj v x
  · exact Or.inr (Or.inl hv)
  refine Or.inr (Or.inr ?_)
  have hxx := mul_self_of_vertex ha x
  have huu := mul_self_of_vertex ha u
  have hvv := mul_self_of_vertex ha v
  have huv' : (u : G) * v = v * u := commute_of_adj' ha huv
  have hBclass : ∀ w : ConjVert a, (x : G) * w = w * x → ¬ (w = x ∨ (twoAGraph a).Adj w x) →
      IsConj z₀ ((x : G) * w) := by
    intro w hxw hw
    have hww := mul_self_of_vertex ha w
    have hinv2 : ((x : G) * w) * ((x : G) * w) = 1 := by
      calc (x : G) * w * ((x : G) * w) = x * (w * x) * w := by group
        _ = x * (x * w) * w := by rw [← hxw]
        _ = (x * x) * (w * w) := by group
        _ = 1 := by rw [hxx, hww, mul_one]
    have hne1 : (x : G) * w ≠ 1 := by
      intro h1
      apply hw
      left
      have e : (x : G) = w := by
        rw [mul_eq_one_iff_eq_inv.1 h1, inv_eq_of_mul_eq_one_right hww]
      exact Subtype.ext e.symm
    rcases aseg_hinv_of I hG _ hne1 hinv2 with hA | hB
    · exfalso
      apply hw
      right
      refine adj_of_conj (fun e => hw (Or.inl (Subtype.ext e))) ?_
      rw [← hxw]
      exact hA
    · exact hB
  have hxuB := hBclass u hxu hu
  have hxvB := hBclass v hxv hv
  have hnotB : ¬ IsConj z₀ (x : G) := fun h => hnc (x.2.trans h.symm)
  have hl : IsLineTriple a (u : G) v := ⟨u.2, v.2, huv.2⟩
  have he : IsEightExt (u : G) v x := by
    refine ⟨hxx, hxu, hxv, ne_one_of_isConj ha x.2, fun e => hu (Or.inl (Subtype.ext e.symm)),
      fun e => hv (Or.inl (Subtype.ext e.symm)), fun e => ?_⟩
    have hxu' : (x : G) * u = v := by
      calc (x : G) * u = u * v * u := by rw [e]
        _ = u * (v * u) := by rw [mul_assoc]
        _ = u * (u * v) := by rw [← huv']
        _ = (u * u) * v := by rw [mul_assoc]
        _ = v := by rw [huu, one_mul]
    rw [hxu'] at hxuB
    exact hnc (v.2.trans hxuB.symm)
  have hxuvB : IsConj z₀ ((x : G) * u * v) := by
    have hcount := F.eightLines.1 (u : G) v x hl he
    by_contra hcon
    rw [twoBCount_eq_ite, ite_eq_right hnotB, ite_eq_left hxuB, ite_eq_left hxvB,
      ite_eq_right hcon] at hcount
    omega
  have hcfg : Cfg a z₀ (u : G) (v : G) (x : G) false true true true :=
    Cfg.of_two u.2 ((S57.adj_iff_mem_twoANbr ha u v).1 huv)
      ⟨x.2, by rw [← hxu]; exact hxuB⟩
      ⟨by rw [← hxv]; exact hxvB, by
        have e : (u : G) * (v * x) = x * u * v := by rw [← hxv, ← mul_assoc, ← hxu]
        rw [e]
        exact hxuvB⟩
  obtain ⟨φ, hφ⟩ := F.a12
  obtain ⟨b₀, t₀, t₀', c₀, hcfg₀, hc₀⟩ := config85 hφ
  obtain ⟨g, hgb, hgt, hgt'⟩ := exists_conj_of_odd F.eightLines ha hz hnc (by decide) hcfg₀ hcfg
  have h1 := conj_mem_twoANbr g hc₀.1.1
  have h2 := conj_mem_twoANbr g hc₀.1.2
  have h3 := conj_mem_twoANbr g hc₀.2
  rw [hgb] at h1
  rw [hgt] at h2
  rw [hgt'] at h3
  refine ⟨⟨g * c₀ * g⁻¹, h1.1⟩, ?_, ?_, ?_⟩
  · exact ((S57.adj_iff_mem_twoANbr ha x ⟨g * c₀ * g⁻¹, h1.1⟩).2 h3).symm
  · exact ((S57.adj_iff_mem_twoANbr ha u ⟨g * c₀ * g⁻¹, h1.1⟩).2 h1).symm
  · exact ((S57.adj_iff_mem_twoANbr ha v ⟨g * c₀ * g⁻¹, h1.1⟩).2 h2).symm

end Eight5

end CFSG.Monster.Tri
