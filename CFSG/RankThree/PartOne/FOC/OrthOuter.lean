module

public import CFSG.RankThree.PartOne.FOC.CompEquiv
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalDescent
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

theorem mem_of_fixed_clause {P : Type} [Group P] [Finite P] {a : MulAut P} {N J : Subgroup P}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hfix : ∀ t, a t = t ↔ t ∈ N) (hJN : J ≤ N)
    (hJn : (J.subgroupOf N).Normal) [IsSimpleGroup ↥J] (hnab : ∃ x y : ↥J, x * y ≠ y * x)
    (hquot : IsPGroup 2 (↥N ⧸ J.subgroupOf N)) :
    ∀ y ∈ fixSub a, y ^ p = 1 → ∀ F : Subgroup P, IsComponentOf (fixSub a) F → y ∈ F := by
  intro y hy hyp F hF
  have hfN : fixSub a = N := Subgroup.ext fun t => hfix t
  rw [hfN] at hF
  exact mem_of_isComponentOf_of_normal_simple hJN hJn hnab hquot hF (hfN ▸ hy) hp hp2 hyp


section Clauses

theorem fixed_clause_odd {n ℓ f p : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n ℓ (f / p))
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hpf : p ∣ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hcard : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p))
    (g : similarityPairs (coordinateQuadOdd n K)) (hl : g.val.left = 1) (hr : g.val.right = σ) :
    ∀ y ∈ fixSub (matrixProjectiveConjugationHom _ g), y ^ p = 1 →
      ∀ F : Subgroup (matrixProjectiveDerived (coordinateQuadOdd n K)),
        IsComponentOf (fixSub (matrixProjectiveConjugationHom _ g)) F → y ∈ F := by
  obtain ⟨e, rfl⟩ := hpf
  have hdiv : p * e / p = e := Nat.mul_div_cancel_left e hp.pos
  rw [hdiv] at hadm hcard
  have hK' : Nat.card K = ℓ ^ (e * p) := by
    rw [mul_comm]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have key := orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
    .POmegaOdd (Or.inl rfl) n ℓ e p hadm hp hp3 hpℓ
  obtain ⟨-, hconc⟩ := key K (semilinearFixedSubfield σ) hcard hK' σ hσ hσk
  have hg : g = fieldPair (coordinateQuadOdd n K) σ (coordinateQuadOdd_fieldAut n σ) :=
    Subtype.ext (SemidirectProduct.ext hl hr)
  subst hg
  obtain ⟨⟨-, hsimple, hnab⟩, -, hfixiff, hJN, hJn, hquot, -⟩ := hconc
  have := hsimple
  exact mem_of_fixed_clause hp (by omega) hfixiff hJN hJn hnab (@hquot hJn)


theorem fixed_clause_plus {n ℓ f p : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n ℓ (f / p))
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hpf : p ∣ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hcard : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p))
    (g : similarityPairs (coordinateQuadPlus n K)) (hl : g.val.left = 1) (hr : g.val.right = σ) :
    ∀ y ∈ fixSub (matrixProjectiveConjugationHom _ g), y ^ p = 1 →
      ∀ F : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)),
        IsComponentOf (fixSub (matrixProjectiveConjugationHom _ g)) F → y ∈ F := by
  obtain ⟨e, rfl⟩ := hpf
  have hdiv : p * e / p = e := Nat.mul_div_cancel_left e hp.pos
  rw [hdiv] at hadm hcard
  have hK' : Nat.card K = ℓ ^ (e * p) := by
    rw [mul_comm]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have key := orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
    .POmegaPlus (Or.inr (Or.inl rfl)) n ℓ e p hadm hp hp3 hpℓ
  obtain ⟨-, hconc⟩ := key K (semilinearFixedSubfield σ) hcard hK' σ hσ hσk
  have hg : g = fieldPair (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) :=
    Subtype.ext (SemidirectProduct.ext hl hr)
  subst hg
  obtain ⟨⟨-, hsimple, hnab⟩, -, hfixiff, hJN, hJn, hquot, -⟩ := hconc
  have := hsimple
  exact mem_of_fixed_clause hp (by omega) hfixiff hJN hJn hnab (@hquot hJn)

theorem fixed_clause_minus {n ℓ f p : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n ℓ (f / p))
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hpf : p ∣ f) (hn : 1 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hcard : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p))
    (b c' : semilinearFixedSubfield σ) (hirr : ∀ s : semilinearFixedSubfield σ, s ^ 2 + b * s + c' ≠ 0)
    (g : similarityPairs (coordinateQuadMinus n K hn (b : K) (c' : K))) (hl : g.val.left = 1)
    (hr : g.val.right = σ) :
    ∀ y ∈ fixSub (matrixProjectiveConjugationHom _ g), y ^ p = 1 →
      ∀ F : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn (b : K) (c' : K))),
        IsComponentOf (fixSub (matrixProjectiveConjugationHom _ g)) F → y ∈ F := by
  obtain ⟨e, rfl⟩ := hpf
  have hdiv : p * e / p = e := Nat.mul_div_cancel_left e hp.pos
  rw [hdiv] at hadm hcard
  have hK' : Nat.card K = ℓ ^ (e * p) := by
    rw [mul_comm]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have key := orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
    .POmegaMinus (Or.inr (Or.inr rfl)) n ℓ e p hadm hp hp3 hpℓ
  obtain ⟨-, hconc⟩ := key hn K (semilinearFixedSubfield σ) hcard hK' σ hσ hσk b c' hirr
  have hg : g = fieldPair (coordinateQuadMinus n K hn (b : K) (c' : K)) σ
      (coordinateQuadMinus_fieldAut (semilinearFixedSubfield σ) n hn hσk b c') :=
    Subtype.ext (SemidirectProduct.ext hl hr)
  subst hg
  obtain ⟨⟨-, hsimple, hnab⟩, -, hfixiff, hJN, hJn, hquot, -⟩ := hconc
  have := hsimple
  exact mem_of_fixed_clause hp (by omega) hfixiff hJN hJn hnab (@hquot hJn)

end Clauses

section Outer

theorem mem_E_of_pow_eq_one {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f p : ℕ}
    (hg : OrthogonalGates Q f) (hp : p.Prime) (hp3 : 3 < p)
    {β : MulAut (matrixProjectiveDerived Q)} (hβp : β ^ p = 1) : β ∈ matrixProjectiveImage Q := by
  have hpg : IsPGroup p (Subgroup.zpowers β) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hβp, one_zpow]
    rfl
  have hK0 := hg.2.2.2.2.2.2.1 p hp hp3 _ hpg
  have h1 : β ∈ projectivePointFamilyAut Q := hg.2.2.2.2.1 (hK0 (Subgroup.mem_zpowers β))
  rw [hg.2.2.2.2.2.1] at h1
  exact h1

theorem mem_inner_of_mem_D {K : Type} [Field K] [Finite K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {f p : ℕ} (hg : OrthogonalGates Q f) (hp : p.Prime)
    (hp3 : 3 < p) {β : MulAut (matrixProjectiveDerived Q)} (hβD : β ∈ (linearConjugationHom Q).range)
    (hβp : β ^ p = 1) : β ∈ innerAut (matrixProjectiveDerived Q) := by
  obtain ⟨-, k, hk⟩ := hg.2.2.1
  have : (ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)).Normal :=
    ComponentClassification.OuterAutomorphisms.inner_normal _
  exact KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp (by omega) hβD hβp


theorem outerComp_matrix_odd {G : Type} [Group G] {n ℓ f p : ℕ}
    (h : StatedClassicalModel G .POmegaOdd n ℓ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    [Finite (matrixProjectiveDerived (coordinateQuadOdd n K))] :
    OuterComp p (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd (Or.inl rfl)
    n ℓ f h K hK e
  refine outerComp_of_descent hp (matrixProjectiveImage (coordinateQuadOdd n K))
    (linearConjugationHom (coordinateQuadOdd n K)).range
    (fun β hβp => mem_E_of_pow_eq_one hg hp hp3 hβp)
    (fun β hβD hβp => mem_inner_of_mem_D hg hp hp3 hβD hβp) ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaOdd (Or.inl rfl)
    n ℓ f p h hp hp3 hpℓ K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  refine ⟨_, inferInstance, Θ, matrixProjectiveConjugationHom _ g', ?_,
    fixed_clause_odd hCM.1 hp hp3 hpℓ hpf K hK U.val.right hord' hcard' g' hg'l hg'r⟩
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

theorem outerComp_matrix_plus {G : Type} [Group G] {n ℓ f p : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n ℓ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    [Finite (matrixProjectiveDerived (coordinateQuadPlus n K))] :
    OuterComp p (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f h K hK e
  refine outerComp_of_descent hp (matrixProjectiveImage (coordinateQuadPlus n K))
    (linearConjugationHom (coordinateQuadPlus n K)).range
    (fun β hβp => mem_E_of_pow_eq_one hg hp hp3 hβp)
    (fun β hβD hβp => mem_inner_of_mem_D hg hp hp3 hβD hβp) ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p h hp hp3 hpℓ K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  refine ⟨_, inferInstance, Θ, matrixProjectiveConjugationHom _ g', ?_,
    fixed_clause_plus hCM.1 hp hp3 hpℓ hpf K hK U.val.right hord' hcard' g' hg'l hg'r⟩
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

theorem outerComp_matrix_minus {G : Type} [Group G] {n ℓ f p : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n ℓ f) (hn : 1 ≤ n) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    [Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))] :
    OuterComp p (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) := by
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f h hn K hK b c hirr e
  refine outerComp_of_descent hp (matrixProjectiveImage (coordinateQuadMinus n K hn b c))
    (linearConjugationHom (coordinateQuadMinus n K hn b c)).range
    (fun β hβp => mem_E_of_pow_eq_one hg hp hp3 hβp)
    (fun β hβD hβp => mem_inner_of_mem_D hg hp hp3 hβD hβp) ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p h hp hp3 hpℓ hn K hK b c hirr e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  refine ⟨_, inferInstance, Θ, matrixProjectiveConjugationHom _ g', ?_,
    fixed_clause_minus hCM.1 hp hp3 hpℓ hpf hn K hK U.val.right hord' hcard' b' c' hirr' g' hg'l
      hg'r⟩
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

end Outer

end CFSG.RankThree.PartOne.FOC
