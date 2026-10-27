module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem lr7dl_coroot_indep (D : GGQ2Lin 3)
    (hR : ∀ d : D.ι → ZMod 3,
      (∀ i, ∑ j, (D.cartan i j : ZMod 3) * d j = 0) → d D.a = 0 → d = 0) :
    LinearIndependent (ZMod 3) (fun k : {k : D.ι // k ≠ D.a} => D.coroot k) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro d hd k
  let d' : D.ι → ZMod 3 := fun i => if h : i ≠ D.a then d ⟨i, h⟩ else 0
  have hd'a : d' D.a = 0 := by
    show (if h : D.a ≠ D.a then d ⟨D.a, h⟩ else 0) = 0
    rw [dif_neg (fun h => h rfl)]
  have hd'eq : ∀ (i : D.ι) (h : i ≠ D.a), d' i = d ⟨i, h⟩ := fun i h => by
    show (if h' : i ≠ D.a then d ⟨i, h'⟩ else 0) = d ⟨i, h⟩
    rw [dif_pos h]
  have hker : ∀ i, ∑ j, (D.cartan i j : ZMod 3) * d' j = 0 := by
    intro i
    have hev : D.root i (∑ k : {k : D.ι // k ≠ D.a}, d k • D.coroot k) = 0 := by
      rw [hd, map_zero]
    rw [map_sum] at hev
    simp only [map_smul, smul_eq_mul, D.pairing] at hev
    have h1 : (∑ j, (D.cartan i j : ZMod 3) * d' j)
        = ∑ j ∈ Finset.univ.filter (fun j => j ≠ D.a),
            (D.cartan i j : ZMod 3) * d' j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = D.a
      · subst hj
        rw [hd'a, mul_zero, if_neg (by simp)]
      · rw [if_pos hj]
    rw [h1]
    have h2a : (∑ j ∈ Finset.univ.filter (fun j => j ≠ D.a),
          (D.cartan i j : ZMod 3) * d' j)
        = ∑ a : {j : D.ι // j ≠ D.a}, (D.cartan i a : ZMod 3) * d' a :=
      Finset.sum_subtype (p := fun j => j ≠ D.a)
        (Finset.univ.filter (fun j => j ≠ D.a)) (by simp)
        (fun j => (D.cartan i j : ZMod 3) * d' j)
    have h2b : (∑ a : {j : D.ι // j ≠ D.a}, (D.cartan i a : ZMod 3) * d' a)
        = ∑ k : {k : D.ι // k ≠ D.a}, d k * (D.cartan i k : ZMod 3) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hd'eq a.1 a.2]
      exact mul_comm _ _
    rw [h2a, h2b]
    exact hev
  have h0 : d' k.1 = 0 := congrFun (hR d' hker hd'a) k.1
  rwa [hd'eq k.1 k.2] at h0

private theorem lr7dl_root_indep (D : GGQ2Lin 3)
    (hL : ∀ d : D.ι → ZMod 3,
      (∀ j, ∑ i, d i * (D.cartan i j : ZMod 3) = 0) → d D.a = 0 → d = 0) :
    LinearIndependent (ZMod 3) (fun k : {k : D.ι // k ≠ D.a} => D.root k) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro d hd k
  let d' : D.ι → ZMod 3 := fun i => if h : i ≠ D.a then d ⟨i, h⟩ else 0
  have hd'a : d' D.a = 0 := by
    show (if h : D.a ≠ D.a then d ⟨D.a, h⟩ else 0) = 0
    rw [dif_neg (fun h => h rfl)]
  have hd'eq : ∀ (i : D.ι) (h : i ≠ D.a), d' i = d ⟨i, h⟩ := fun i h => by
    show (if h' : i ≠ D.a then d ⟨i, h'⟩ else 0) = d ⟨i, h⟩
    rw [dif_pos h]
  have hker : ∀ j, ∑ i, d' i * (D.cartan i j : ZMod 3) = 0 := by
    intro j
    have hev : (∑ k : {k : D.ι // k ≠ D.a}, d k • D.root k) (D.coroot j) = 0 := by
      have h := congrArg (fun φ : Dual (ZMod 3) D.V => φ (D.coroot j)) hd
      simpa using h
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, D.pairing] at hev
    have h1 : (∑ i, d' i * (D.cartan i j : ZMod 3))
        = ∑ i ∈ Finset.univ.filter (fun i => i ≠ D.a),
            d' i * (D.cartan i j : ZMod 3) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = D.a
      · subst hi
        rw [hd'a, zero_mul, if_neg (by simp)]
      · rw [if_pos hi]
    rw [h1]
    have h2a : (∑ i ∈ Finset.univ.filter (fun i => i ≠ D.a),
          d' i * (D.cartan i j : ZMod 3))
        = ∑ a : {i : D.ι // i ≠ D.a}, d' a * (D.cartan a j : ZMod 3) :=
      Finset.sum_subtype (p := fun i => i ≠ D.a)
        (Finset.univ.filter (fun i => i ≠ D.a)) (by simp)
        (fun i => d' i * (D.cartan i j : ZMod 3))
    have h2b : (∑ a : {i : D.ι // i ≠ D.a}, d' a * (D.cartan a j : ZMod 3))
        = ∑ k : {k : D.ι // k ≠ D.a}, d k * (D.cartan k j : ZMod 3) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [hd'eq a.1 a.2]
    rw [h2a, h2b]
    exact hev
  have h0 : d' k.1 = 0 := congrFun (hL d' hker hd'a) k.1
  rwa [hd'eq k.1 k.2] at h0

theorem ggQ2_dep_basis_or_caseII (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V] (x : D.V)
    (hx0 : x ≠ 0)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hR : ∀ d : D.ι → ZMod 3, (∀ i, ∑ j, (D.cartan i j : ZMod 3) * d j = 0) → d D.a = 0 → d = 0)
    (hL : ∀ d : D.ι → ZMod 3, (∀ j, ∑ i, d i * (D.cartan i j : ZMod 3) = 0) → d D.a = 0 →
      d = 0) :
    D.Basis ∨ D.CaseII := by
  classical
  have hLIcoroot := lr7dl_coroot_indep D hR
  have hLIroot := lr7dl_root_indep D hL
  have hdim : Module.finrank (ZMod 3) D.V = Fintype.card {k : D.ι // k ≠ D.a} + 1 := by
    rw [ggQ2_dep_finrank_eq D x hx0 hx, finrank_span_eq_card hLIroot]
  have hcard : Fintype.card D.ι = Module.finrank (ZMod 3) D.V := by
    have hc : Fintype.card {k : D.ι // k ≠ D.a} + 1 = Fintype.card D.ι := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      have : 0 < Fintype.card D.ι := Fintype.card_pos_iff.mpr ⟨D.a⟩
      omega
    omega
  by_cases hmem : D.coroot D.a ∈ Submodule.span (ZMod 3)
      (Set.range (fun k : {k : D.ι // k ≠ D.a} => D.coroot k))
  · right
    refine ⟨hcard, hLIcoroot, ?_⟩
    intro hli
    have hsub : Set.range (fun k : {k : D.ι // k ≠ D.a} => D.coroot k)
        ⊆ D.coroot '' ({D.a}ᶜ : Set D.ι) := by
      rintro y ⟨k, rfl⟩
      exact ⟨k.1, by simpa using k.2, rfl⟩
    exact (hli.notMem_span D.a) (Submodule.span_mono hsub hmem)
  · left
    refine ⟨?_, hcard⟩
    have hw : LinearIndependent (ZMod 3) (D.coroot ∘ (Equiv.optionSubtypeNe D.a)) := by
      rw [linearIndependent_option]
      constructor
      · have hfun : ((D.coroot ∘ (Equiv.optionSubtypeNe D.a)) ∘
            (some : {k : D.ι // k ≠ D.a} → Option {k : D.ι // k ≠ D.a}))
            = fun k : {k : D.ι // k ≠ D.a} => D.coroot k := by
          funext k
          simp
        rw [hfun]
        exact hLIcoroot
      · have hnone : (D.coroot ∘ (Equiv.optionSubtypeNe D.a)) none = D.coroot D.a := by
          simp
        have hrange : Set.range (((D.coroot ∘ (Equiv.optionSubtypeNe D.a)) ∘
            (some : {k : D.ι // k ≠ D.a} → Option {k : D.ι // k ≠ D.a})))
            = Set.range (fun k : {k : D.ι // k ≠ D.a} => D.coroot k) := by
          rw [show ((D.coroot ∘ (Equiv.optionSubtypeNe D.a)) ∘
              (some : {k : D.ι // k ≠ D.a} → Option {k : D.ι // k ≠ D.a}))
              = fun k : {k : D.ι // k ≠ D.a} => D.coroot k from by
            funext k
            simp]
        rw [hnone, hrange]
        exact hmem
    exact (linearIndependent_equiv (Equiv.optionSubtypeNe D.a)).mp hw

end CFSG.StandardType

end
