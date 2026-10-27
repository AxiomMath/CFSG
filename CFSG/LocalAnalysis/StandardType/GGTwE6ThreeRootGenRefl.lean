module

public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenRoot
public import CFSG.LocalAnalysis.StandardType.GGKGWeylRootFacts

public section

namespace CFSG.StandardType.TwE6ThreeRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private def rootPairLinear (γ : Fin Tag.E6.rank → ℤ) :
    (Fin Tag.E6.rank → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun := KGL.rootPair γ
  map_add' x y := by
    simp only [KGL.rootPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [KGL.rootPair, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      simp only [RingHom.id_apply]
      ring

private theorem rootPairLinear_apply (γ : Fin Tag.E6.rank → ℤ)
    (x : Fin Tag.E6.rank → ZMod 3) :
    rootPairLinear γ x = KGL.rootPair γ x := rfl

private def kDotPLinear : (Fin Tag.E6.rank → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun := NoOffRest.kDotP 3
  map_add' x y := NoOffRest.kDotP_add x y
  map_smul' c x := by
    simpa using NoOffRest.kDotP_smul (p := 3) c x

private theorem ker_kDotPLinear :
    kDotPLinear.toAddMonoidHom.ker = NoOffRest.hypE6 := by
  ext x
  rfl

private theorem surjective_kDotPLinear :
    Function.Surjective kDotPLinear.toAddMonoidHom := by
  intro y
  refine ⟨y • (Pi.single 0 1 : Fin Tag.E6.rank → ZMod 3), ?_⟩
  change NoOffRest.kDotP 3 (y • (Pi.single 0 1 : Fin Tag.E6.rank → ZMod 3)) = y
  rw [NoOffRest.kDotP_smul]
  have h1 : NoOffRest.kDotP 3 (Pi.single 0 1 : Fin Tag.E6.rank → ZMod 3) = 1 := by
    rw [NoOffRest.kDotP, Finset.sum_eq_single (0 : Fin Tag.E6.rank)]
    · simp [NoOffRest.kE6]
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h1, mul_one]

private theorem card_hypE6 :
    Nat.card (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) = 3 ^ 5 := by
  have hmul := AddSubgroup.card_ker_mul_card_of_surjective
    (f := kDotPLinear.toAddMonoidHom) surjective_kDotPLinear
  rw [ker_kDotPLinear, Nat.card_zmod] at hmul
  have hdom : Nat.card (Fin Tag.E6.rank → ZMod 3) = 3 ^ 6 := by
    rw [Nat.card_pi]
    simp only [Nat.card_zmod, Finset.prod_const]
    rw [Finset.card_univ, Fintype.card_fin]
    rfl
  rw [hdom] at hmul
  have h3 : (3 : ℕ) ^ 6 = 3 ^ 5 * 3 := by norm_num
  rw [h3] at hmul
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) hmul

private theorem exists_coeff_of_forall_hypE6 {γ δ : Fin Tag.E6.rank → ℤ}
    (h : ∀ x : Fin Tag.E6.rank → ZMod 3,
      NoOffRest.kDotP 3 x = 0 → KGL.rootPair γ x = 0 → KGL.rootPair δ x = 0) :
    ∃ a b : ZMod 3, ∀ j, ((δ j : ℤ) : ZMod 3) =
      a * ((γ j : ℤ) : ZMod 3) + b * ((NoOffRest.kE6 j : ℤ) : ZMod 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let L : Fin 2 → (Fin Tag.E6.rank → ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
    ![rootPairLinear γ, rootPairLinear NoOffRest.kE6]
  have hle : ⨅ i, LinearMap.ker (L i) ≤ LinearMap.ker (rootPairLinear δ) := by
    intro x hx
    rw [Submodule.mem_iInf] at hx
    have hx0 : x ∈ LinearMap.ker (rootPairLinear γ) := by
      simpa [L] using hx 0
    have hx1 : x ∈ LinearMap.ker (rootPairLinear NoOffRest.kE6) := by
      simpa [L] using hx 1
    have hxγ : KGL.rootPair γ x = 0 := LinearMap.mem_ker.mp hx0
    have hx1' : rootPairLinear NoOffRest.kE6 x = 0 := LinearMap.mem_ker.mp hx1
    rw [rootPairLinear_apply] at hx1'
    have hxk : NoOffRest.kDotP 3 x = 0 := by
      simpa [KGL.rootPair, NoOffRest.kDotP] using hx1'
    exact LinearMap.mem_ker.mpr (h x hxk hxγ)
  have hspan : rootPairLinear δ ∈ Submodule.span (ZMod 3) (Set.range L) :=
    @mem_span_of_iInf_ker_le_ker (Fin 2) (ZMod 3) (Fin Tag.E6.rank → ZMod 3)
      (ZMod.instField (p := 3)) (inferInstance)
      (Pi.Function.module (Fin Tag.E6.rank) (ZMod 3) (ZMod 3))
      (inferInstance) L (rootPairLinear δ) hle
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hspan
  refine ⟨c 0, c 1, fun j => ?_⟩
  have hjeval : (∑ i, c i • L i : (Fin Tag.E6.rank → ZMod 3) →ₗ[ZMod 3] ZMod 3)
      (Pi.single j 1) = (rootPairLinear δ) (Pi.single j 1) := by
    rw [hc]
  simpa [L, rootPairLinear_apply, KGL.rootPair, NoOffRest.kDotP, Fin.sum_univ_two,
    Pi.single_apply, smul_eq_mul] using hjeval.symm

private theorem kgExpVec_eq_mul_of_coeff {γ δ : Fin Tag.E6.rank → ℤ} {a b : ZMod 3}
    (hab : ∀ j, ((δ j : ℤ) : ZMod 3) =
      a * ((γ j : ℤ) : ZMod 3) + b * ((NoOffRest.kE6 j : ℤ) : ZMod 3)) :
    ∀ i, KGL.kgExpVec δ i = a * KGL.kgExpVec γ i := by
  intro i
  have hCk : (∑ j, ((Tag.E6.cartan i j : ℤ) : ZMod 3) *
      ((NoOffRest.kE6 j : ℤ) : ZMod 3)) = 0 := by
    have h := NoOffRest.kDot_cartan i
    simp only [NoOffRest.kDotP] at h
    simpa [mul_comm] using h
  simp only [KGL.kgExpVec, Matrix.mulVec, dotProduct]
  push_cast
  calc
    (∑ j, (Tag.E6.cartan i j : ZMod 3) * (δ j : ZMod 3))
        = ∑ j, (Tag.E6.cartan i j : ZMod 3) *
            (a * (γ j : ZMod 3) + b * (NoOffRest.kE6 j : ZMod 3)) := by
          exact Finset.sum_congr rfl fun j _ => by rw [hab j]
    _ = ∑ j, (a * ((Tag.E6.cartan i j : ZMod 3) * (γ j : ZMod 3)) +
              b * ((Tag.E6.cartan i j : ZMod 3) * (NoOffRest.kE6 j : ZMod 3))) := by
          exact Finset.sum_congr rfl fun j _ => by ring
    _ = a * (∑ j, (Tag.E6.cartan i j : ZMod 3) * (γ j : ZMod 3)) +
          b * (∑ j, (Tag.E6.cartan i j : ZMod 3) * (NoOffRest.kE6 j : ZMod 3)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = a * (∑ j, (Tag.E6.cartan i j : ZMod 3) * (γ j : ZMod 3)) := by
          rw [hCk, mul_zero, add_zero]

private theorem eq_or_eq_neg_of_forall_coeff
    {γ δ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (hδ : IsRoot Tag.E6 δ) {a b : ZMod 3}
    (hab : ∀ j, ((δ j : ℤ) : ZMod 3) =
      a * ((γ j : ℤ) : ZMod 3) + b * ((NoOffRest.kE6 j : ℤ) : ZMod 3)) :
    δ = γ ∨ δ = -γ := by
  have hkg : ∀ i, KGL.kgExpVec δ i = a * KGL.kgExpVec γ i :=
    kgExpVec_eq_mul_of_coeff hab
  have ha0 : a ≠ 0 := by
    intro h0
    apply KGL.kgExpVec_ne_zero hδ
    funext i
    rw [hkg i, h0, zero_mul]
    rfl
  have ha : a = 1 ∨ a = -1 := by
    have hsmall : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide
    exact hsmall a ha0
  rcases ha with rfl | rfl
  · left
    apply KGL.kgExpVec_injective_of_isRoot hδ hγ
    funext i
    rw [hkg i, one_mul]
  · right
    apply KGL.kgExpVec_injective_of_isRoot hδ (IsRoot.neg hγ)
    rw [KGL.kgExpVec_neg]
    funext i
    rw [hkg i, Pi.neg_apply]
    have hneg : ∀ x : ZMod 3, (-1 : ZMod 3) * x = -x := by decide
    exact hneg _

private theorem eq_or_eq_neg_of_forall_mem_sum_eq_zero_H
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hδ : IsRoot Tag.E6 δ)
    (h : ∀ x : Fin Tag.E6.rank → ZMod 3,
      x ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) →
      (∑ j, ((γ j : ℤ) : ZMod 3) * x j) = 0 →
      (∑ j, ((δ j : ℤ) : ZMod 3) * x j) = 0) :
    δ = γ ∨ δ = -γ := by
  have h' : ∀ x : Fin Tag.E6.rank → ZMod 3,
      NoOffRest.kDotP 3 x = 0 → KGL.rootPair γ x = 0 → KGL.rootPair δ x = 0 := by
    intro x hx hγx
    have hxH : x ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
      NoOffRest.mem_hypE6.mpr hx
    have hγx' : (∑ j, ((γ j : ℤ) : ZMod 3) * x j) = 0 := by
      simpa [KGL.rootPair] using hγx
    have hδx' : (∑ j, ((δ j : ℤ) : ZMod 3) * x j) = 0 := h x hxH hγx'
    simpa [KGL.rootPair] using hδx'
  obtain ⟨a, b, hab⟩ := exists_coeff_of_forall_hypE6 h'
  exact eq_or_eq_neg_of_forall_coeff hγ hδ hab

theorem card_fix_excRefl_mul_three
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        x ∈ V ∧ ExcSplitRootGen.excRefl (p := 3) γ x = x} * 3 = Nat.card V := by
  rcases hV with rfl | rfl
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hcard : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        x ∈ (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)) ∧
          ExcSplitRootGen.excRefl (p := 3) γ x = x} =
        Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
          ExcSplitRootGen.excRefl (p := 3) γ x = x} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp)
    rw [hcard, ExcSplitRootGen.card_fix_excRefl (τ := Tag.E6) (p := 3)
      (by norm_num : (3 : ℕ) ≠ 2) hγ]
    rw [Nat.card_univ, Nat.card_pi]
    simp only [Nat.card_zmod, Finset.prod_const]
    rw [Finset.card_univ, Fintype.card_fin]
  · have hcard : Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
        x ∈ (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) ∧
          ExcSplitRootGen.excRefl (p := 3) γ x = x} =
        Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
          x ∈ NoOffRest.hypE6 ∧ KGL.rootRefl γ x = x} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => by
        have h : ExcSplitRootGen.excRefl (p := 3) γ x = KGL.rootRefl γ x :=
          KGL.adAct_rootReflection_eq_rootRefl hγ x
        simp [h])
    rw [hcard, KGL.card_fix_rootRefl hγ, card_hypE6]
    norm_num

theorem eq_or_eq_neg_of_eqOn_excRefl
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hδ : IsRoot Tag.E6 δ)
    (h : ∀ x ∈ V, ExcSplitRootGen.excRefl (p := 3) γ x = ExcSplitRootGen.excRefl δ x) :
    δ = γ ∨ δ = -γ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hsum : ∀ x ∈ V, (∑ j, ((γ j : ℤ) : ZMod 3) * x j) = 0 →
      (∑ j, ((δ j : ℤ) : ZMod 3) * x j) = 0 := by
    intro x hx hγx
    have hγfix : ExcSplitRootGen.excRefl (p := 3) γ x = x :=
      (ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num : (3 : ℕ) ≠ 2) hγ x).mpr
        hγx
    have hδfix : ExcSplitRootGen.excRefl (p := 3) δ x = x := by
      rw [← h x hx]
      exact hγfix
    exact (ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num : (3 : ℕ) ≠ 2)
      hδ x).mp hδfix
  rcases hV with rfl | rfl
  · exact ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero (τ := Tag.E6) (p := 3)
      (Or.inl rfl) (by norm_num : (3 : ℕ) ≠ 2) hγ hδ
      (fun x hx => hsum x (Set.mem_univ x) hx)
  · exact eq_or_eq_neg_of_forall_mem_sum_eq_zero_H hγ hδ hsum

theorem eq_or_eq_neg_of_forall_mem_sum_eq_zero
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {γ δ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hδ : IsRoot Tag.E6 δ)
    (h : ∀ x ∈ V, ∑ j, (γ j : ZMod 3) * x j = 0 → ∑ j, (δ j : ZMod 3) * x j = 0) :
    δ = γ ∨ δ = -γ := by
  rcases hV with rfl | rfl
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero (τ := Tag.E6) (p := 3)
      (Or.inl rfl) (by norm_num : (3 : ℕ) ≠ 2) hγ hδ
      (fun x hx => h x (Set.mem_univ x) hx)
  · exact eq_or_eq_neg_of_forall_mem_sum_eq_zero_H hγ hδ h

end CFSG.StandardType.TwE6ThreeRootGen

end
