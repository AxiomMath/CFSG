module

public import CFSG.Monster.Tri.ASegFactsLocal
public import CFSG.Monster.GMS.Coxeter

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

section Algebra

variable {G : Type*} [Group G]

theorem s4_identities {x u v : G} (hx : x * x = 1) (hu : u * u = 1) (hv : v * v = 1)
    (hxu : (x * u) ^ 3 = 1) (hxv : (x * v) ^ 3 = 1) (huv : u * v = v * u) :
    (u * v) * (u * v) = 1 ∧ x * (x * (u * v)) ^ 2 = (u * v) * x * (u * v) ∧
    (x * (u * v)) ^ 2 * (u * v) = x * (u * v) * x ∧
    (x * (u * v)) ^ 2 = (x * u * x) * (u * v) * (x * u * x) ∧
    (x * u * x) * (x * u * x) = 1 := by
  have bu := braid_of_cube hx hu hxu
  have bv := braid_of_cube hx hv hxv
  have hvu : v * u = u * v := huv.symm
  have huvu : u * v * u = v := by rw [huv, mul_assoc, hu, mul_one]
  have e0 : x * (u * v) * x * (u * v) = x * u * (v * x * v) * u := by
    calc x * (u * v) * x * (u * v) = x * u * (v * x) * (v * u) := by
          rw [hvu]; group
      _ = x * u * (v * x * v) * u := by group
  have e1 : x * (u * v) * x * (u * v) = (u * v) * x * (u * v) * x := by
    calc x * (u * v) * x * (u * v) = x * u * (v * x * v) * u := e0
      _ = x * u * (x * v * x) * u := by rw [← bv]
      _ = (x * u * x) * v * x * u := by group
      _ = (u * x * u) * v * x * u := by rw [bu]
      _ = u * x * (u * v) * x * u := by group
      _ = u * x * (v * u) * x * u := by rw [huv]
      _ = u * x * v * (u * x * u) := by group
      _ = u * x * v * (x * u * x) := by rw [bu]
      _ = u * (x * v * x) * u * x := by group
      _ = u * (v * x * v) * u * x := by rw [bv]
      _ = (u * v) * x * (v * u) * x := by group
      _ = (u * v) * x * (u * v) * x := by rw [hvu]
  have hc : (x * (u * v)) ^ 2 = x * (u * v) * x * (u * v) := by
    rw [pow_two]; simp only [mul_assoc]
  have hww : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [hvu]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu, hv, mul_one]
  refine ⟨hww, ?_, ?_, ?_, ?_⟩
  · rw [hc]
    calc x * (x * (u * v) * x * (u * v)) = (x * x) * (u * v) * x * (u * v) := by group
      _ = (u * v) * x * (u * v) := by rw [hx, one_mul]
  · rw [hc]
    calc x * (u * v) * x * (u * v) * (u * v) = x * (u * v) * x * ((u * v) * (u * v)) := by group
      _ = x * (u * v) * x := by rw [hww, mul_one]
  · rw [hc]
    symm
    calc (x * u * x) * (u * v) * (x * u * x) = (x * u * x) * (u * v) * (u * x * u) := by
          rw [← bu]
      _ = x * u * x * (u * v * u) * x * u := by group
      _ = x * u * x * v * x * u := by rw [huvu]
      _ = x * u * (x * v * x) * u := by group
      _ = x * u * (v * x * v) * u := by rw [bv]
      _ = x * (u * v) * x * (v * u) := by group
      _ = x * (u * v) * x * (u * v) := by rw [hvu]
  · calc (x * u * x) * (x * u * x) = x * u * (x * x) * u * x := by group
      _ = x * (u * u) * x := by rw [hx]; group
      _ = 1 := by rw [hu, mul_one, hx]

end Algebra

section Vertices

variable {G : Type*} [Group G] {a : G}

theorem exists_adj_of_s4 (ha : orderOf a = 2) {x u v m : ConjVert a}
    (hxu : ((x : G) * u) ^ 3 = 1) (hxv : ((x : G) * v) ^ 3 = 1) (huv : (u : G) * v = v * u)
    (hm : (m : G) = (u : G) * v) :
    ∃ c : ConjVert a, (twoAGraph a).Adj x c ∧ (twoAGraph a).Adj c m := by
  have hxx := S36Lines.sq_eq_one_of_isConj ha x.2
  have huu := S36Lines.sq_eq_one_of_isConj ha u.2
  have hvv := S36Lines.sq_eq_one_of_isConj ha v.2
  obtain ⟨hww, h2, h3, h4, hpp⟩ := s4_identities hxx huu hvv hxu hxv huv
  have hwa : IsConj a ((u : G) * v) := by rw [← hm]; exact m.2
  have hxi := inv_eq_self_of_mul_self' hxx
  have hwi := inv_eq_self_of_mul_self' hww
  have hpi := inv_eq_self_of_mul_self' hpp
  have hca : IsConj a (((x : G) * ((u : G) * v)) ^ 2) := by
    rw [h4]
    have := isConj_conj hwa ((x : G) * u * x)
    rwa [hpi] at this
  refine ⟨⟨_, hca⟩, ?_, ?_⟩
  · have hxc : IsConj a ((x : G) * ((x : G) * ((u : G) * v)) ^ 2) := by
      rw [h2]
      have := isConj_conj x.2 ((u : G) * v)
      rwa [hwi] at this
    refine adj_of_conj (p := x) (q := ⟨_, hca⟩) (fun e => ?_) hxc
    have e' : (x : G) = ((x : G) * ((u : G) * v)) ^ 2 := e
    exact S36Lines.ne_one_of_isConj ha hxc (by rw [← e']; exact hxx)
  · have hcm : IsConj a (((x : G) * ((u : G) * v)) ^ 2 * (m : G)) := by
      rw [hm, h3]
      have := isConj_conj hwa x
      rwa [hxi] at this
    refine adj_of_conj (p := ⟨_, hca⟩) (q := m) (fun e => ?_) hcm
    have e' : ((x : G) * ((u : G) * v)) ^ 2 = (m : G) := e
    refine S36Lines.ne_one_of_isConj ha hcm ?_
    rw [e', hm]
    exact hww

end Vertices


section Types

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem exists_common_of_ncard_ne_zero (ha : orderOf a = 2) {x u : ConjVert a}
    (h : (twoANbr a (x : G) ∩ twoANbr a (u : G)).ncard ≠ 0) :
    ∃ w : ConjVert a, (twoAGraph a).Adj x w ∧ (twoAGraph a).Adj w u := by
  obtain ⟨w, hw₁, hw₂⟩ := Set.nonempty_of_ncard_ne_zero h
  exact ⟨⟨w, hw₁.1⟩, (S57.adj_iff_mem_twoANbr ha x ⟨w, hw₁.1⟩).2 hw₁,
    ((S57.adj_iff_mem_twoANbr ha u ⟨w, hw₁.1⟩).2 hw₂).symm⟩

theorem mem_typeSet_threeC_of_far
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (F : ASegFacts a z₀) (h3A : ThreeACommonNbrs a z₀) {x y : ConjVert a}
    (hxy : ¬(x = y ∨ (twoAGraph a).Adj x y))
    (hcn : ¬∃ w : ConjVert a, (twoAGraph a).Adj x w ∧ (twoAGraph a).Adj w y)
    (hno : ¬∃ b : ConjVert a, (x : G) * b = b * x ∧ (y : G) * b = b * y) :
    (y : G) ∈ typeSet a z₀ x .threeC := by
  have ha : orderOf a = 2 := hG.1.1
  have hyx : (y : G) ≠ x := fun h => hxy (Or.inl (Subtype.ext h.symm))
  obtain ⟨K, hK⟩ := S36Lines.exists_typeSet_of_gammaCover F.gammaCover x.2 y.2 hyx
  have key : (twoANbr a (x : G) ∩ twoANbr a (y : G)).ncard = 0 := by
    by_contra h
    exact hcn (exists_common_of_ncard_ne_zero ha h)
  cases K with
  | twoA => exact absurd (Or.inr ((S57.adj_iff_mem_twoANbr ha x y).2 hK)) hxy
  | twoB =>
    have hK' : (y : G) ∈ twoBNbr a z₀ (x : G) := hK
    rw [ncard_commonNbr_twoB I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG x.2 hK'] at key
    exact absurd key (by norm_num)
  | fourA =>
    have hK' : (y : G) ∈ fourANbr a z₀ (x : G) := hK
    rw [ncard_commonNbr_fourA I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG x.2 hK'] at key
    exact absurd key (by norm_num)
  | threeA =>
    have hcard := (h3A x y hK).1
    rw [ncard_commonNeighbors_eq ha] at hcard
    omega
  | fourB =>
    have hK' : (y : G) ∈ fourBNbr a (x : G) := hK
    rw [ncard_commonNbr_fourB I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG x.2 hK'] at key
    exact absurd key (by norm_num)
  | sixA =>
    have hK' : (y : G) ∈ sixANbr a (x : G) := hK
    rw [ncard_commonNbr_sixA I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG x.2 hK'] at key
    exact absurd key (by norm_num)
  | fiveA =>
    obtain ⟨t, ht, hta⟩ := F.fiveA.fiveATwoA (x : G) (y : G) x.2 hK
    obtain ⟨htx, hty⟩ := Subgroup.mem_inf.1 ht
    exact absurd ⟨⟨t, hta⟩, (Subgroup.mem_centralizer_singleton_iff.1 htx).symm,
      (Subgroup.mem_centralizer_singleton_iff.1 hty).symm⟩ hno
  | threeC => exact hK

omit [Finite G] in
theorem mem_typeSet_threeC_of_order (hG : GMSF1Type d₀ a z₀)
    (F : ASegFacts a z₀) (h3A : ThreeACommonNbrs a z₀) {x y : ConjVert a}
    (hord : orderOf ((x : G) * y) = 3)
    (hno : ¬∃ b : ConjVert a, (x : G) * b = b * x ∧ (y : G) * b = b * y) :
    (y : G) ∈ typeSet a z₀ x .threeC := by
  have ha : orderOf a = 2 := hG.1.1
  have hyx : (y : G) ≠ x := by
    intro h
    have : orderOf ((x : G) * y) = 1 := by rw [h, mul_self_of_vertex ha x, orderOf_one]
    omega
  obtain ⟨K, hK⟩ := S36Lines.exists_typeSet_of_gammaCover F.gammaCover x.2 y.2 hyx
  have hKo := S36Lines.orderOf_mul_of_mem_typeSet ha hG.2.1 hK
  rw [hord] at hKo
  cases K with
  | threeC => exact hK
  | threeA =>
    exfalso
    have hcard := (h3A x y hK).1
    obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero
      (by omega : ((twoAGraph a).commonNeighbors x y).ncard ≠ 0)
    obtain ⟨hw₁, hw₂⟩ := (SimpleGraph.mem_commonNeighbors _).1 hw
    exact hno ⟨w, commute_of_adj' ha hw₁, commute_of_adj' ha hw₂⟩
  | twoA => exact absurd hKo (by decide)
  | twoB => exact absurd hKo (by decide)
  | fourA => exact absurd hKo (by decide)
  | fourB => exact absurd hKo (by decide)
  | fiveA => exact absurd hKo (by decide)
  | sixA => exact absurd hKo (by decide)

end Types

section S4

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem aseg_hS4_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (F : ASegFacts a z₀)
    (h3A : ThreeACommonNbrs a z₀) :
    ∀ x u v : ConjVert a, orderOf ((x : G) * u) = 3 → (twoAGraph a).Adj u v →
      ¬(x = v ∨ (twoAGraph a).Adj x v) →
      (¬∃ w : ConjVert a, (twoAGraph a).Adj x w ∧ (twoAGraph a).Adj w v) →
      (¬∃ b : ConjVert a, (x : G) * b = b * x ∧ (v : G) * b = b * v) →
      ∀ m : ConjVert a, (m : G) = (u : G) * v →
        ∃ c : ConjVert a, (twoAGraph a).Adj x c ∧ (twoAGraph a).Adj c m := by
  intro x u v hxu huv hxv hcn hno m hm
  have ha : orderOf a = 2 := hG.1.1
  have hv3 : orderOf ((x : G) * v) = 3 :=
    S36Lines.orderOf_mul_of_mem_typeSet ha hG.2.1 (K := .threeC)
      (mem_typeSet_threeC_of_far I hG F h3A hxv hcn hno)
  exact exists_adj_of_s4 ha (by rw [← hxu]; exact pow_orderOf_eq_one _)
    (by rw [← hv3]; exact pow_orderOf_eq_one _) (commute_of_adj' ha huv) hm

end S4

end CFSG.Monster.Tri
