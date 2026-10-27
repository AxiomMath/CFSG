module

public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.LocalRank CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem noninner_core_odd (hsub : OrthogonalSubfieldCoreClause) {G : Type} [Group G]
    {n ℓ f p : ℕ} (h : StatedClassicalModel G .POmegaOdd n ℓ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    (B : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))))
    (hB : (MulAut.conj : matrixProjectiveDerived (coordinateQuadOdd n K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))).range ≤ B)
    (a : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)))
    (haE : a ∈ matrixProjectiveImage (coordinateQuadOdd n K))
    (haD : a ∉ (linearConjugationHom (coordinateQuadOdd n K)).range) (hap : orderOf a = p)
    (haB : a ∈ B) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaOdd (Or.inl rfl)
    n ℓ f p h hp hp3 hpℓ K hK e a haE haD hap
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hclause := hsub .POmegaOdd n ℓ f p (Or.inl rfl) hCM.1 hp hp3 hpℓ hpf K hK U.val.right hord'
    hcard'
  exact core_eq_bot_of_conj hp Θ (a := a) (a' := matrixProjectiveConjugationHom _ g')
    (fun x => by rw [← hUκ]; exact hΘ x)
    (fun B' hB' hgB => hclause g' hg'l hg'r B' hB' hgB) B hB haB

theorem noninner_core_plus (hsub : OrthogonalSubfieldCoreClause) {G : Type} [Group G]
    {n ℓ f p : ℕ} (h : StatedClassicalModel G .POmegaPlus n ℓ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    (B : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))))
    (hB : (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))).range ≤ B)
    (a : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (haE : a ∈ matrixProjectiveImage (coordinateQuadPlus n K))
    (haD : a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range) (hap : orderOf a = p)
    (haB : a ∈ B) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p h hp hp3 hpℓ K hK e a haE haD hap
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hclause := hsub .POmegaPlus n ℓ f p (Or.inr (Or.inl rfl)) hCM.1 hp hp3 hpℓ hpf K hK
    U.val.right hord' hcard'
  exact core_eq_bot_of_conj hp Θ (a := a) (a' := matrixProjectiveConjugationHom _ g')
    (fun x => by rw [← hUκ]; exact hΘ x)
    (fun B' hB' hgB => hclause g' hg'l hg'r B' hB' hgB) B hB haB

theorem noninner_core_minus (hsub : OrthogonalSubfieldCoreClause) {G : Type} [Group G]
    {n ℓ f p : ℕ} (h : StatedClassicalModel G .POmegaMinus n ℓ f) (hn : 1 ≤ n) (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    (B : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))))
    (hB : (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus n K hn b c) →*
      MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))).range ≤ B)
    (a : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)))
    (haE : a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn b c))
    (haD : a ∉ (linearConjugationHom (coordinateQuadMinus n K hn b c)).range)
    (hap : orderOf a = p) (haB : a ∈ B) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p h hp hp3 hpℓ hn K hK b c hirr e a haE haD hap
  obtain ⟨g, hg⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hclause := hsub .POmegaMinus n ℓ f p (Or.inr (Or.inr rfl)) hCM.1 hp hp3 hpℓ hpf K hK
    U.val.right hord' hcard' hn b' c' hirr'
  exact core_eq_bot_of_conj hp Θ (a := a) (a' := matrixProjectiveConjugationHom _ g')
    (fun x => by rw [← hUκ]; exact hΘ x)
    (fun B' hB' hgB => hclause g' hg'l hg'r B' hB' hgB) B hB haB

end CFSG.RankThree.PartOne
