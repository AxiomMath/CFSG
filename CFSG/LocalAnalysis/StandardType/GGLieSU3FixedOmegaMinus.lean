module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode
import CFSG.GroupTheory.PerfectImageRange

import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedOrthCore
import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedSkeleton

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggLieSU3Fixed_omegaMinus_hinn {X R G : Type} [Group X] [Group R] [Group G]
    (θ : X ⧸ Subgroup.center X ≃* R) (Φ' : R ≃* G) {A : Subgroup (MulAut X)}
    (hInn : GGInducedInn A θ (LargeEvenInnSet R)) :
    ∀ a ∈ A, ∃ s : G, ∀ x : X,
      (Φ'.toMonoidHom.comp
          (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))) (a x) =
        s * (Φ'.toMonoidHom.comp
          (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))) x * s⁻¹ := by
  intro a ha
  obtain ⟨p, hp⟩ := hInn a ha
  refine ⟨Φ' p, fun x => ?_⟩
  have h1 : θ ((a x : X) : X ⧸ Subgroup.center X) =
      ggInducedAut θ a (θ (x : X ⧸ Subgroup.center X)) :=
    (ggInducedAut_apply θ a x).symm
  calc (Φ'.toMonoidHom.comp
          (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))) (a x)
      = Φ' (θ ((a x : X) : X ⧸ Subgroup.center X)) := by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    _ = Φ' (ggInducedAut θ a (θ (x : X ⧸ Subgroup.center X))) := by rw [h1]
    _ = Φ' ((MulAut.conj p) (θ (x : X ⧸ Subgroup.center X))) := by rw [← hp]
    _ = Φ' (p * θ (x : X ⧸ Subgroup.center X) * p⁻¹) := by rw [MulAut.conj_apply]
    _ = Φ' p * Φ' (θ (x : X ⧸ Subgroup.center X)) * (Φ' p)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
    _ = Φ' p * (Φ'.toMonoidHom.comp
          (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))) x * (Φ' p)⁻¹ := by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]

theorem ggLieSU3Fixed_of_omegaMinus {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X} (hl : GGAutLocal A δ J)
    (hZJ : Subgroup.center ↥J ≠ ⊥) (hJ3 : Nat.card (Subgroup.center ↥J) ∣ 3)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center X))
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {m : ℕ} (hm : 3 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
    (hInn : GGInducedInn A θ
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))) :
    ¬ GGAutsFixedInCenter A J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  let QF : QuadraticForm K (LargeEvenMinusIdx m → K) := TableBOrth.qMinusForm K m b c
  let Φ' : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived QF) :=
    (TableBOrth.projMkEquiv (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot b c)).symm.trans
      ((MulEquiv.subgroupCongr
        (congrArg LargeEvenOmega (TableBOrth.coe_qMinusForm m b c)).symm).trans
        (TableBOrth.omegaEquivOrthDerived QF))
  let ψ : X →* ↥(CFSG.RankThree.Classical2.orthDerived QF) :=
    Φ'.toMonoidHom.comp (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)))
  have hψ : Function.Surjective ψ :=
    Φ'.surjective.comp (θ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.ker = Subgroup.center X := by
    rw [MonoidHom.ker_comp_of_injective
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) Φ'.toMonoidHom Φ'.injective,
      MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center X)) θ.toMonoidHom
        θ.injective,
      QuotientGroup.ker_mk']
  have hG : Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived QF) = ⊥ :=
    CFSG.GroupTheory.center_eq_bot_of_ker_eq_center hX ψ hψ hker
  have hinn := ggLieSU3Fixed_omegaMinus_hinn θ Φ' hInn
  refine ggLieSU3Fixed_of_lift (G := ↥(CFSG.RankThree.Classical2.orthDerived QF))
    hX hl hZJ hJ3 hG ψ hψ hker h3 hinn ?_
  intro E hEc hE3 d hdE _ Jh hJ z hzJ hzc hz3 hz1 hzE
  exact ggLieSU3Fixed_orth_core (Q := QF)
    (TableBOrth.nondegenerate_qMinusForm (K := K) m hbc)
    E hEc hE3 hdE Jh hJ hzJ hzc hz3 hz1 hzE

end CFSG.StandardType
