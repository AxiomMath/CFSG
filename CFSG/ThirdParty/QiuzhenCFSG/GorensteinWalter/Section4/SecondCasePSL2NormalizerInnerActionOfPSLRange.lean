module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerInnerActionOfQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-! ## Semilinear transport for the normalizer layer -/

/-- A semilinear action on the central quotient of the actual normalizer
layer produces the Fact 1.10(ii) inner-action package once the image of
`F(U) ⊓ N_G(X)` lies in the canonical PSL range.

Unlike `secondCase_psl2_fitting_innerAction_of_actionData`, this statement
does not assume that the normalizer lies in the original maximal subgroup:
the action is supplied on `C_{N_G(X)}(t)`, the subgroup in which the Fitting
package lives. -/
public theorem secondCase_psl2_normalizer_innerAction_of_pslRange
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (X : Subgroup G)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (f :
      let N : Subgroup G := Subgroup.normalizer (X : Set G)
      let C : Subgroup G := N ⊓ c.H
      C →* PGammaL2 K)
    (e :
      let N : Subgroup G := Subgroup.normalizer (X : Set G)
      let L : Subgroup G := componentLayerOf N
      Nonempty ((L ⧸ Subgroup.center L) ≃* PSL2 K))
    (haction :
      let N : Subgroup G := Subgroup.normalizer (X : Set G)
      let L : Subgroup G := componentLayerOf N
      let C : Subgroup G := N ⊓ c.H
      ∀ (m : C) (x : L),
        pGammaL2ToMulAutPSL2 K hK hcard (f m)
            (e.some (QuotientGroup.mk' (Subgroup.center L) x)) =
          e.some (QuotientGroup.mk' (Subgroup.center L)
            ⟨(m : G) * (x : G) * (m : G)⁻¹,
              (componentLayerOf_isNormalIn N).2 (m : G) m.2.1
                (x : G) x.2⟩))
    (himage :
      let N : Subgroup G := Subgroup.normalizer (X : Set G)
      ∀ p, (hp : p ∈ c.FU ⊓ N) →
        f ⟨p, hp.2, (centralizerSetup_FU_isNormalIn_H c).1 hp.1⟩ ∈
          pGammaL2PSLRange K) :
    secondCase_psl2_normalizer_innerAction c X := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let L : Subgroup G := componentLayerOf N
  let C : Subgroup G := N ⊓ c.H
  let q : L →* L ⧸ Subgroup.center L :=
    QuotientGroup.mk' (Subgroup.center L)
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
  refine secondCase_psl2_normalizer_innerAction_of_quotientInner c X ?_
  dsimp only
  intro p hp
  let pC : C :=
    ⟨p, hp.2, (centralizerSetup_FU_isNormalIn_H c).1 hp.1⟩
  rcases (mem_pGammaL2PSLRange_iff K (f pC)).mp (himage p hp) with ⟨a, ha⟩
  obtain ⟨ℓ, hℓ⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) (e.some.symm a)
  refine ⟨ℓ, ?_⟩
  intro x
  apply e.some.injective
  have hact := haction pC x
  have hinl : pGammaL2ToMulAutPSL2 K hK hcard
      (SemidirectProduct.inl (toPGL a)) = MulAut.conj a := by
    rw [pGammaL2ToMulAutPSL2_inl]
    exact pgl2InnerAutPSL2_toPGL K hK hcard a
  rw [← ha] at hact
  rw [hinl] at hact
  have hea : e.some (q ℓ) = a := by
    calc
      e.some (q ℓ) = e.some (e.some.symm a) := congrArg e.some hℓ
      _ = a := e.some.apply_symm_apply a
  change e.some
      (q ⟨p * (x : G) * p⁻¹,
        (componentLayerOf_isNormalIn N).2 p hp.2 (x : G) x.2⟩) =
    e.some (q (ℓ * x * ℓ⁻¹))
  rw [map_mul, map_mul, map_inv]
  rw [map_mul, map_mul, map_inv, hea]
  exact hact.symm

end CFSG.GorensteinWalter
