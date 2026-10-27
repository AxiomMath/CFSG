module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.Assembly CFSG.RankThree.Classical CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal
open scoped IsMulCommutative

open _root_.Classical in
structure KernelLineData {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p : ℕ) (Ã : Subgroup (orthDerived Q)) : Prop where
  comm : ∀ x y : Ã, x * y = y * x
  card : Nat.card Ã = p ^ 2
  exp : ∀ x : Ã, x ^ p = 1
  internal : DirectSum.IsInternal (innerSummand p Ã)
  orth : ∀ i j, i ≠ j → ∀ u ∈ innerSummand p Ã i, ∀ v ∈ innerSummand p Ã j, polarBilin Q u v = 0
  regular : ∀ i, (LinearMap.BilinForm.restrict (polarBilin Q) (innerSummand p Ã i)).Nondegenerate
  two_active : ∃ M₁ M₂ : Subgroup Ã, Nat.card M₁ = p ∧ Nat.card M₂ = p ∧ M₁ ≠ M₂ ∧
    lineSpace M₁ ≠ ⊥ ∧ lineSpace M₂ ≠ ⊥
  lines : ∀ ζ : AlgebraicClosure K, IsPrimitiveRoot ζ p → ∀ M : Subgroup Ã, Nat.card M = p →
    (lineSpace M).baseChange (AlgebraicClosure K) =
      ⨆ (χ : Additive Ã →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M),
        charSpace (bcRep (AlgebraicClosure K) Ã) ζ χ

theorem kernelLineData {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpl : p ≠ ringChar K) (A : Subgroup (ProjOrthDerived Q)) (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (Ã : Subgroup (orthDerived Q))
    (hÃ : Ã ≤ A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ∧
      ∀ P : Sylow p (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))),
        (P : Subgroup (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))).map
          (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).subtype = Ã) :
    KernelLineData Q p Ã := by
  classical
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨Ã', hle', hsyl', e, he, huniq, hint, horth, hnd, hline, hex2, hact, hlcm, hrank, hζ⟩ :=
    orthogonal_inner_plane_kernel_line_quadratic_decomposition hℓ hp hp2 hpl Q hQ A hA hAc
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    DFunLike.coe_injective
  have hEq : Ã' = Ã := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p (A.comap
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))))
    exact (hsyl' P).symm.trans (hÃ.2 P)
  subst hEq
  have : IsMulCommutative A := hA.1
  refine ⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm]), ?_, fun x => e.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (hA.2 _ (e x).2)), hint, horth, hnd, hex2, fun ζ hζ' => (hζ ζ hζ').2⟩
  exact (Nat.card_congr e.toEquiv).trans hAc

end CFSG.RankThree.PartOne.KCOrthogonal
