module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.ChevalleyG2F4
public import CFSG.LieType.Ree.ShortRepresentation

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.SignalizerFunctorTheorem.NonLocal CFSG.SignalizerFunctorTheorem.CatalogBridge

variable (t : ReeTag) (K F : Type) [Field K] [Field F] [Algebra K F]
  [Fintype t.shortLabels] [DecidableEq t.shortLabels]

@[expose] noncomputable def shortAdjRep
    (hp : (t.prime : K) = 0) :
    ↥(adjointGroup t.tag K) →* Module.End F (t.shortLabels → F) :=
  (extendScalars K F t.shortLabels).toMonoidHom.comp
    ((LinearMap.toMatrixAlgEquiv (t.shortBasis K)).toAlgHom.toMonoidHom.comp
      (shortRestrictHom t K hp))

variable {t K F}

theorem shortAdjRep_injective
    [Finite K] [CharP K t.prime] :
    Function.Injective (shortAdjRep t K F (CharP.cast_eq_zero K t.prime)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hp := CharP.cast_eq_zero K t.prime
  have h1 : shortRestrictHom t K hp g = 1 := by
    apply (LinearMap.toMatrixAlgEquiv (t.shortBasis K)).injective
    apply extendScalars_injective K F t.shortLabels
    have h2 : (extendScalars K F t.shortLabels) ((LinearMap.toMatrixAlgEquiv (t.shortBasis K))
        (shortRestrictHom t K hp g)) = 1 := hg
    rw [h2, map_one, map_one]
  refine Subtype.ext (exceptional_short_faithful t K g.2 fun v hv => ?_)
  exact congrArg (fun f : Module.End K (t.shortModule K) => (f ⟨v, hv⟩ : RootModule t.tag K)) h1

omit [DecidableEq t.shortLabels] in
variable (t F) in
theorem finrank_short_pi
    : Module.finrank F (t.shortLabels → F) = t.shortDim := by
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, card_shortLabels]

theorem not_pow_two_dvd_factorial_26 {e : ℕ} (he : 1 ≤ e) : ¬ 2 ^ (24 * e) ∣ (26).factorial := by
  intro h
  have h24 : 2 ^ 24 ∣ (26).factorial := (pow_dvd_pow 2 (by omega : 24 ≤ 24 * e)).trans h
  revert h24
  decide

variable [Finite K]

theorem nonLocalized_F4_of_two
    (σ : K ≃+* K) [CharP K 2] :
    NonLocalized ((fixedFieldImage .F4 σ).subgroupOf (adjointGroup .F4 K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he, hke⟩ := exists_card_fixSubfield σ 2
  let F := AlgebraicClosure K
  have hF : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  have : Fintype (ReeTag.F4.shortLabels) := Fintype.ofFinite _
  have hsimple : IsSimpleGroup ↥(adjointGroup .F4 (fixSubfield σ)) :=
    isSimpleGroup_adjointGroup_of_quasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 _)
  have hp : ((ReeTag.F4.prime : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
  have hKp : CharP K ReeTag.F4.prime := ‹CharP K 2›
  refine nonLocalized_fixedFieldImage_of_rep σ 2 hsimple (F := F)
    (shortAdjRep ReeTag.F4 K F hp) (shortAdjRep_injective (t := ReeTag.F4) (F := F)) ?_
  rw [hke, CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4, ← pow_mul',
    finrank_short_pi ReeTag.F4 F]
  exact not_pow_two_dvd_factorial_26 he

theorem nonLocalized_F4
    (σ : K ≃+* K) :
    NonLocalized ((fixedFieldImage .F4 σ).subgroupOf (adjointGroup .F4 K)) := by
  obtain ⟨r, hrK⟩ := CharP.exists K
  have : Fact r.Prime := ⟨CharP.char_is_prime K r⟩
  by_cases hr2 : r = 2
  · subst hr2
    exact nonLocalized_F4_of_two σ
  · exact nonLocalized_F4_of_ne_two σ r hr2

end CFSG.SignalizerFunctorTheorem.NonLocalExc
