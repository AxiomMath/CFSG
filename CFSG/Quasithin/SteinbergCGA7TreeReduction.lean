module

public import CFSG.Quasithin.SteinbergCGA7TreeReductionSupport
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

namespace CFSG.Quasithin.SteinbergCG

open SteinbergBN

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}
  (hβ : β.IsAlt) {I : Type*} [DecidableEq I]

theorem invariants_of_reflTransGen {a b : I → V}
    (h : Relation.ReflTransGen (IsIndexMove hβ) a b) :
    ((∀ i, a i ≠ 0) → ∀ i, b i ≠ 0) ∧
      ((pairGraph hβ a).Connected → (pairGraph hβ b).Connected) ∧
      Submodule.span (ZMod 2) (Set.range b) = Submodule.span (ZMod 2) (Set.range a) ∧
      Subgroup.closure (Set.range fun i => transv hβ (b i)) =
        Subgroup.closure (Set.range fun i => transv hβ (a i)) := by
  induction h with
  | refl => exact ⟨id, id, rfl, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨p, q, hpq, rfl⟩ := hstep
    obtain ⟨h0, hc, hs, hcl⟩ := ih
    exact ⟨fun ha i => indexMove_ne_zero hβ _ (h0 ha) p q i,
      fun ha => connected_indexMove hβ _ hpq (hc ha), (span_indexMove hβ _ hpq).trans hs,
      (closure_indexMove hβ _ hpq).trans hcl⟩

omit [DecidableEq I] in
theorem list_prod_apply_eq {l : List (LinearMap.GeneralLinearGroup (ZMod 2) V)} {v : V}
    (h : ∀ g ∈ l, (g : V →ₗ[ZMod 2] V) v = v) : (l.prod : V →ₗ[ZMod 2] V) v = v := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [List.prod_cons, Units.val_mul, Module.End.mul_apply,
      ih fun g' hg' => h g' (List.mem_cons_of_mem _ hg'), h g List.mem_cons_self]

theorem applyAt_congr {S T : Finset I} {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    {b : I → V} (h : ∀ j, (j ∈ S ↔ j ∈ T) ∨ (g : V →ₗ[ZMod 2] V) (b j) = b j) :
    applyAt S g b = applyAt T g b := by
  funext j
  unfold applyAt
  rcases h j with h | h
  · by_cases hS : j ∈ S
    · rw [ite_eq_left hS, ite_eq_left (h.mp hS)]
    · rw [ite_eq_right hS, ite_eq_right fun hT => hS (h.mpr hT)]
  · by_cases hS : j ∈ S <;> by_cases hT : j ∈ T
    · rw [ite_eq_left hS, ite_eq_left hT]
    · rw [ite_eq_left hS, ite_eq_right hT, h]
    · rw [ite_eq_right hS, ite_eq_left hT, h]
    · rw [ite_eq_right hS, ite_eq_right hT]

theorem exists_cycle_step [FiniteDimensional (ZMod 2) V] [Fintype I] {C : Finset I} {w : I}
    (hwC : w ∈ C) {b : I → V} (hb0 : ∀ i, b i ≠ 0)
    (hout : ∀ x ∈ C, x ≠ w → ∀ y ∉ C, ¬ (pairGraph hβ b).Adj x y)
    (hear : ∃ m x, IsEar (pairGraph hβ b) C w m x) :
    ∃ b', Relation.ReflTransGen (IsIndexMove hβ) b b' ∧
      (∀ x y, (x ∉ C ∨ y ∉ C) → ((pairGraph hβ b').Adj x y ↔ (pairGraph hβ b).Adj x y)) ∧
      (pairGraph hβ b').degree w + 1 = (pairGraph hβ b).degree w := by
  classical
  obtain ⟨x, hx⟩ := Nat.find_spec hear
  have hmin : ∀ m' < Nat.find hear, ∀ x', ¬ IsEar (pairGraph hβ b) C w m' x' :=
    fun m' hm' x' hx' => Nat.find_min hear hm' ⟨x', hx'⟩
  obtain ⟨n, c, hn, hc, hcyc, hc0, hcC⟩ := exists_cycle_of_isEar_min hx hmin
  have : Nonempty I := ⟨w⟩
  have hw0 : c ⟨0, by omega⟩ = w := hc0 _ rfl
  have hall : ∀ k, c k ∈ C := fun k => by
    by_cases hk : (k : ℕ) = 0
    · rw [hc0 k hk]
      exact hwC
    · exact (hcC k hk).1
  have horth : ∀ k : Fin n, (k : ℕ) ≠ 0 → ∀ j ∉ C, β (b (c k)) (b j) = 0 := fun k hk j hj =>
    (pairGraph_not_adj hβ b).mp (hout _ (hcC k hk).1 (hcC k hk).2 j hj)
  obtain ⟨-, -, -, -, hdeg, hJ⟩ := (indexed_transvection_cycle_move hβ b hb0).2 n hn c hc hcyc
  obtain ⟨hrt, hedge⟩ := hJ C hall fun k hk1 _ j hj => horth k (by omega) j hj
  have hP : ∀ j ∉ C, ((List.ofFn fun k : Fin (n - 2) =>
      transv hβ (b (c ⟨n - 2 - k, by omega⟩))).prod : V →ₗ[ZMod 2] V) (b j) = b j := by
    intro j hj
    apply list_prod_apply_eq
    intro g hg
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    have hk := k.isLt
    exact transv_apply_of_orth hβ (horth _ (by simp only; omega) j hj)
  have heq := applyAt_congr (S := insert (c ⟨0, by omega⟩) (Finset.univ \ Finset.univ.image c))
    (T := insert (c ⟨0, by omega⟩) (C \ Finset.univ.image c)) (b := b)
    (g := (List.ofFn fun k : Fin (n - 2) => transv hβ (b (c ⟨n - 2 - k, by omega⟩))).prod)
    fun j => by
      by_cases hj : j ∈ C
      · left
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and, hj]
      · right
        exact hP j hj
  refine ⟨_, hrt, hedge, ?_⟩
  rw [← heq, ← hw0]
  exact hdeg

theorem exists_reduction [FiniteDimensional (ZMod 2) V] [Fintype I] (C : Finset I) :
    ∀ (w : I) (b : I → V), w ∈ C → (∀ i, b i ≠ 0) → (pairGraph hβ b).Connected →
      (∀ x ∈ C, x ≠ w → ∀ y ∉ C, ¬ (pairGraph hβ b).Adj x y) →
      ∃ b', Relation.ReflTransGen (IsIndexMove hβ) b b' ∧
        (∀ x y, (x ∉ C ∨ y ∉ C) → ((pairGraph hβ b').Adj x y ↔ (pairGraph hβ b).Adj x y)) ∧
        adjCount (pairGraph hβ b') C + 2 = 2 * C.card := by
  induction C using Finset.strongInduction with
  | H C ih =>
  intro w b hwC hb0 hconn hout
  suffices key : ∀ d (b : I → V), (pairGraph hβ b).degree w = d → (∀ i, b i ≠ 0) →
      (pairGraph hβ b).Connected → (∀ x ∈ C, x ≠ w → ∀ y ∉ C, ¬ (pairGraph hβ b).Adj x y) →
      ∃ b', Relation.ReflTransGen (IsIndexMove hβ) b b' ∧
        (∀ x y, (x ∉ C ∨ y ∉ C) → ((pairGraph hβ b').Adj x y ↔ (pairGraph hβ b).Adj x y)) ∧
        adjCount (pairGraph hβ b') C + 2 = 2 * C.card from key _ b rfl hb0 hconn hout
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro b hd hb0 hconn hout
  classical
  by_cases hear : ∃ m x, IsEar (pairGraph hβ b) C w m x
  ·
    obtain ⟨b₁, hrt₁, hedge₁, hdeg₁⟩ := exists_cycle_step hβ hwC hb0 hout hear
    obtain ⟨h0₁, hc₁, -, -⟩ := invariants_of_reflTransGen hβ hrt₁
    have hout₁ : ∀ x ∈ C, x ≠ w → ∀ y ∉ C, ¬ (pairGraph hβ b₁).Adj x y :=
      fun x hx hxw y hy h => hout x hx hxw y hy ((hedge₁ x y (Or.inr hy)).mp h)
    obtain ⟨b', hrt', hedge', hcount⟩ := ihd _ (by omega) b₁ rfl (h0₁ hb0) (hc₁ hconn) hout₁
    exact ⟨b', hrt₁.trans hrt', fun x y hxy => (hedge' x y hxy).trans (hedge₁ x y hxy), hcount⟩
  by_cases hnb : ∃ u ∈ C, (pairGraph hβ b).Adj w u
  ·
    obtain ⟨u, huC, hwu⟩ := hnb
    have huw : u ≠ w := hwu.ne.symm
    have huS : u ∈ C.erase w := Finset.mem_erase.mpr ⟨huw, huC⟩
    let D := (C.erase w).filter (ReachIn (pairGraph hβ b) (C.erase w) u)
    have hDsub : D ⊆ C.erase w := Finset.filter_subset _ _
    have hDC : D ⊆ C := hDsub.trans (Finset.erase_subset _ _)
    have huD : u ∈ D := Finset.mem_filter.mpr ⟨huS, ReachIn.refl huS⟩
    have hwD : w ∉ D := fun h => (Finset.mem_erase.mp (hDsub h)).1 rfl
    have hclos : ∀ y ∈ D, ∀ z ∈ C, z ≠ w → (pairGraph hβ b).Adj y z → z ∈ D := by
      intro y hy z hz hzw hyz
      have hzS : z ∈ C.erase w := Finset.mem_erase.mpr ⟨hzw, hz⟩
      exact Finset.mem_filter.mpr ⟨hzS, (Finset.mem_filter.mp hy).2.tail hzS hyz⟩
    have honly : ∀ y ∈ D, (pairGraph hβ b).Adj y w → y = u := by
      intro y hy hyw
      by_contra hyu
      exact hear ((Finset.mem_filter.mp hy).2.exists_isEar hwu hyw.symm (Ne.symm hyu))
    have houtD : ∀ x ∈ D, x ≠ u → ∀ y ∉ D, ¬ (pairGraph hβ b).Adj x y := by
      intro x hx hxu y hy hxy
      have hxw : x ≠ w := fun h => hwD (h ▸ hx)
      by_cases hyC : y ∈ C
      · by_cases hyw : y = w
        · rw [hyw] at hxy
          exact hxu (honly x hx hxy)
        · exact hy (hclos x hx y hyC hyw hxy)
      · exact hout x (hDC hx) hxw y hyC hxy
    have hDC' : D ⊂ C := Finset.ssubset_iff_subset_ne.mpr ⟨hDC, fun h => hwD (by rw [h]; exact hwC)⟩
    obtain ⟨b₁, hrt₁, hedge₁, hcount₁⟩ := ih D hDC' u b huD hb0 hconn houtD
    obtain ⟨h0₁, hc₁, -, -⟩ := invariants_of_reflTransGen hβ hrt₁
    have hwC' : w ∈ C \ D := Finset.mem_sdiff.mpr ⟨hwC, hwD⟩
    have hC'C : C \ D ⊂ C := Finset.sdiff_ssubset hDC ⟨u, huD⟩
    have hout₁ : ∀ x ∈ C \ D, x ≠ w → ∀ y ∉ C \ D, ¬ (pairGraph hβ b₁).Adj x y := by
      intro x hx hxw y hy hxy
      obtain ⟨hxC, hxD⟩ := Finset.mem_sdiff.mp hx
      have hxy' : (pairGraph hβ b).Adj x y := (hedge₁ x y (Or.inl hxD)).mp hxy
      by_cases hyC : y ∈ C
      · have hyD : y ∈ D := by
          by_contra hyD
          exact hy (Finset.mem_sdiff.mpr ⟨hyC, hyD⟩)
        exact hxD (hclos y hyD x hxC hxw hxy'.symm)
      · exact hout x hxC hxw y hyC hxy'
    obtain ⟨b₂, hrt₂, hedge₂, hcount₂⟩ := ih (C \ D) hC'C w b₁ hwC' (h0₁ hb0) (hc₁ hconn) hout₁
    refine ⟨b₂, hrt₁.trans hrt₂, fun x y hxy => ?_, ?_⟩
    · have h1 : x ∉ C \ D ∨ y ∉ C \ D :=
        hxy.imp (fun h h' => h (Finset.mem_sdiff.mp h').1)
          (fun h h' => h (Finset.mem_sdiff.mp h').1)
      have h2 : x ∉ D ∨ y ∉ D := hxy.imp (fun h h' => h (hDC h')) (fun h h' => h (hDC h'))
      exact (hedge₂ x y h1).trans (hedge₁ x y h2)
    · have hunion : D ∪ C \ D = C := Finset.union_sdiff_of_subset hDC
      have hdisj : Disjoint D (C \ D) := Finset.disjoint_sdiff
      have hcross : ∀ y ∈ D, ∀ z ∈ C \ D, ((pairGraph hβ b₂).Adj y z ↔ y = u ∧ z = w) := by
        intro y hy z hz
        have hyC' : y ∉ C \ D := fun h => (Finset.mem_sdiff.mp h).2 hy
        have hzD : z ∉ D := (Finset.mem_sdiff.mp hz).2
        rw [hedge₂ y z (Or.inl hyC'), hedge₁ y z (Or.inr hzD)]
        constructor
        · intro hyz
          have hzw : z = w := by
            by_contra hzw
            exact hzD (hclos y hy z (Finset.mem_sdiff.mp hz).1 hzw hyz)
          rw [hzw] at hyz
          exact ⟨honly y hy hyz, hzw⟩
        · rintro ⟨h1, h2⟩
          rw [h1, h2]
          exact hwu.symm
      have hcD : adjCount (pairGraph hβ b₂) D = adjCount (pairGraph hβ b₁) D :=
        adjCount_congr fun x hx y _ => hedge₂ x y (Or.inl fun h => (Finset.mem_sdiff.mp h).2 hx)
      have hsum := adjCount_union hdisj huD hwC' hcross
      rw [hunion] at hsum
      have hcard : D.card + (C \ D).card = C.card := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      omega
  ·
    have hCw : C = {w} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hwC, fun y hy => ?_⟩
      by_contra hyw
      obtain ⟨p⟩ := hconn.preconnected y w
      obtain ⟨z, z', hz, hz', hzz'⟩ := exists_adj_of_walk p (S := ((C.erase w : Finset I) : Set I))
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hyw, hy⟩))
        (fun h => (Finset.mem_erase.mp (Finset.mem_coe.mp h)).1 rfl)
      have hz1 := Finset.mem_erase.mp (Finset.mem_coe.mp hz)
      by_cases hz'w : z' = w
      · rw [hz'w] at hzz'
        exact hnb ⟨z, hz1.2, hzz'.symm⟩
      · exact hout z hz1.2 hz1.1 z'
          (fun h => hz' (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hz'w, h⟩))) hzz'
    refine ⟨b, Relation.ReflTransGen.refl, fun _ _ _ => Iff.rfl, ?_⟩
    rw [hCw, adjCount_singleton, Finset.card_singleton]

omit [DecidableEq I] in
theorem exists_fin_chain_of_reflTransGen {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    ∃ (k : ℕ) (l : Fin (k + 1) → α), l 0 = a ∧ (∀ j : Fin k, r (l j.castSucc) (l j.succ)) ∧
      l (Fin.last k) = b := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, fun j => j.elim0, rfl⟩
  | @tail b' c _ hbc ih =>
    obtain ⟨k, l, h0, hstep, hlast⟩ := ih
    refine ⟨k + 1, Fin.snoc (α := fun _ => α) l c, ?_, fun j => ?_, Fin.snoc_last _ _⟩
    · show Fin.snoc (α := fun _ => α) l c (Fin.castSucc 0) = a
      rw [Fin.snoc_castSucc]
      exact h0
    · induction j using Fin.lastCases with
      | last =>
        rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hlast]
        exact hbc
      | cast j =>
        rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
        exact hstep j

theorem connected_indexed_transvection_graph_reduces_to_tree [FiniteDimensional (ZMod 2) V]
    [Fintype I] [Nonempty I] (a : I → V) (ha0 : ∀ i, a i ≠ 0)
    (hconn : (pairGraph hβ a).Connected) :
    ∃ (k : ℕ) (l : Fin (k + 1) → I → V), l 0 = a ∧
      (∀ j : Fin k, IsIndexMove hβ (l j.castSucc) (l j.succ)) ∧
      (pairGraph hβ (l (Fin.last k))).IsTree ∧
      ∀ j, (∀ i, l j i ≠ 0) ∧
        Submodule.span (ZMod 2) (Set.range (l j)) = Submodule.span (ZMod 2) (Set.range a) ∧
        Subgroup.closure (Set.range fun i => transv hβ (l j i)) =
          Subgroup.closure (Set.range fun i => transv hβ (a i)) := by
  obtain ⟨w⟩ := ‹Nonempty I›
  obtain ⟨b, hrt, -, hcount⟩ := exists_reduction hβ Finset.univ w a (Finset.mem_univ w) ha0
    hconn fun _ _ _ y hy => absurd (Finset.mem_univ y) hy
  obtain ⟨-, hc, -, -⟩ := invariants_of_reflTransGen hβ hrt
  have htree : (pairGraph hβ b).IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨hc hconn, ?_⟩
    rw [adjCount_univ, Finset.card_univ, ← Nat.card_eq_fintype_card] at hcount
    omega
  obtain ⟨k, l, hl0, hstep, hlast⟩ := exists_fin_chain_of_reflTransGen hrt
  have hreach : ∀ j, Relation.ReflTransGen (IsIndexMove hβ) a (l j) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      rw [hl0]
    | succ j ih => exact ih.tail (hstep j)
  refine ⟨k, l, hl0, hstep, hlast ▸ htree, fun j => ?_⟩
  obtain ⟨h0', -, hs, hcl⟩ := invariants_of_reflTransGen hβ (hreach j)
  exact ⟨h0' ha0, hs, hcl⟩

end CFSG.Quasithin.SteinbergCG
