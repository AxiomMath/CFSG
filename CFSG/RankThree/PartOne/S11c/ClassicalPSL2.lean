module

public import CFSG.RankThree.PartOne.S11.CatalogLeaves
public import CFSG.RankThree.Classical.SteinbergCFProjectiveTwoAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L4Core

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def restrictAutSub {T : Type*} [Group T] (E : Subgroup (MulAut T)) (U : Subgroup T)
    (hEU : ∀ e ∈ E, ∀ u ∈ U, e u ∈ U) : E →* MulAut U where
  toFun e :=
    { toFun := fun u => ⟨(e : MulAut T) u, hEU e e.2 u u.2⟩
      invFun := fun u => ⟨(e : MulAut T)⁻¹ u, hEU _ (E.inv_mem e.2) u u.2⟩
      left_inv := fun u => Subtype.ext (MulAut.inv_apply_self T (e : MulAut T) u)
      right_inv := fun u => Subtype.ext (MulAut.apply_inv_self T (e : MulAut T) u)
      map_mul' := fun a b => Subtype.ext (map_mul (e : MulAut T) (a : T) (b : T)) }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' := fun _ _ => MulEquiv.ext fun _ => rfl

theorem planeCentralizes_of_embedding_pgl2 {T : Type} [Group T] [Finite T] {K : Type}
    [Field K] (hK : ringChar K ≠ 2) (ψ : T →* PGL(2, K)) (hψ : Function.Injective ψ) {p : ℕ}
    {E : Subgroup (MulAut T)} {U : Subgroup T} (hplane : PlaneOn p E U) :
    PlaneCentralizes E U := by
  classical
  have hEU : ∀ e ∈ E, ∀ u ∈ U, e u ∈ U := hplane.normalized
  let Q : Subgroup PGL(2, K) := U.map ψ
  let eUQ : U ≃* Q := Subgroup.equivMapOfInjective U ψ hψ
  have hQ2 : IsPGroup 2 Q := hplane.two_group.map ψ
  have : Finite Q := Finite.of_equiv U eUQ.toEquiv
  have : IsElementaryAbelian p E := hplane.elementary
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  let φ : E →* MulAut Q := (MulAut.congr eUQ).toMonoidHom.comp (restrictAutSub E U hEU)
  have hφ := (odd_projective_linear_two_subgroup_automorphisms_no_large_primes K hK Q hQ2).2 p
    hplane.prime hplane.three_lt E hEp φ
  intro e he u hu
  have h0 : (MulAut.congr eUQ) (restrictAutSub E U hEU ⟨e, he⟩) = 1 := hφ ⟨e, he⟩
  have h1 : restrictAutSub E U hEU ⟨e, he⟩ = 1 :=
    (MulAut.congr eUQ).injective (h0.trans (map_one _).symm)
  have h2 := congrArg (fun a : MulAut U => ((a ⟨u, hu⟩ : U) : T)) h1
  exact h2

theorem planeCentralizes_psl_two {T : Type} [Group T] [Finite T] {K : Type} [Field K]
    (hK : ringChar K ≠ 2) (e : T ≃* StatedProj (StatedSL 2 K)) {p : ℕ} {E : Subgroup (MulAut T)}
    {U : Subgroup T} (hplane : PlaneOn p E U) : PlaneCentralizes E U :=
  planeCentralizes_of_embedding_pgl2 hK
    ((CFSG.ComponentClassification.CatFactsL4U4.projToPGL 2 K).comp e.toMonoidHom)
    ((CFSG.ComponentClassification.CatFactsL4U4.projToPGL_injective 2).comp e.injective) hplane

end CFSG.RankThree.PartOne
