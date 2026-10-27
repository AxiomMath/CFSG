module

public import CFSG.LieType.Ree.RelationGraph

public section

namespace CFSG.HardMathSupport.C14ExcRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem relationExponent_add
    {t : ReeTag} (a b : ℕ) (i : Fin t.tag.rank) :
    t.relationExponent (a + b) i = t.prime ^ b * t.relationExponent a i := by
  rw [ReeTag.relationExponent, ReeTag.relationExponent, ReeTag.relationExponent_eq,
    ReeTag.relationExponent_eq, pow_add]
  ring

theorem reeEndo_comp_comp
    {t : ReeTag} {K : Type} [Field K] [CharP K t.prime]
    (hf : t.ShortFaithful K) (a b : ℕ) :
    (t.reeEndo K hf b).comp ((t.reeEndo K hf a).comp (t.reeEndo K hf a)) =
      t.reeEndo K hf (b + (2 * a + 1)) := by
  refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ReeTag.reeEndo_xElement,
      ReeTag.reeEndo_xElement, ReeTag.reeEndo_xElement, ReeTag.reeEndo_xElement, ReeTag.perm_perm,
      ← pow_mul, ← pow_mul, ← mul_assoc, ReeTag.relationExponent_mul_relationExponent_perm,
      ReeTag.perm_perm, relationExponent_add, mul_comm]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ReeTag.reeEndo_yElement,
      ReeTag.reeEndo_yElement, ReeTag.reeEndo_yElement, ReeTag.reeEndo_yElement, ReeTag.perm_perm,
      ← pow_mul, ← pow_mul, ← mul_assoc, ReeTag.relationExponent_mul_relationExponent_perm,
      ReeTag.perm_perm, relationExponent_add, mul_comm]

theorem reeEndo_comp_self
    {t : ReeTag} {K : Type} [Field K] [CharP K t.prime]
    (hf : t.ShortFaithful K) (a : ℕ) :
    (t.reeEndo K hf a).comp (t.reeEndo K hf a) =
      frobeniusTwist t.tag K (iterateFrobenius K t.prime (2 * a + 1)) := by
  refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
  · rw [MonoidHom.comp_apply, ReeTag.reeEndo_xElement, ReeTag.reeEndo_xElement, ReeTag.perm_perm,
      ← pow_mul, ReeTag.relationExponent_mul_relationExponent_perm, frobeniusTwist_xElement,
      iterateFrobenius_def]
  · rw [MonoidHom.comp_apply, ReeTag.reeEndo_yElement, ReeTag.reeEndo_yElement, ReeTag.perm_perm,
      ← pow_mul, ReeTag.relationExponent_mul_relationExponent_perm, frobeniusTwist_yElement,
      iterateFrobenius_def]

theorem reeEndo_iterate_odd
    {t : ReeTag} {K : Type} [Field K] [CharP K t.prime]
    (hf : t.ShortFaithful K) (a₀ k : ℕ) (g : adjointGroup t.tag K) :
    (t.reeEndo K hf a₀)^[2 * k + 1] g = t.reeEndo K hf (a₀ + k * (2 * a₀ + 1)) g := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, Function.iterate_add_apply, ih]
    have h := congrArg (fun φ : adjointGroup t.tag K →* adjointGroup t.tag K => φ g)
      (reeEndo_comp_comp hf a₀ (a₀ + k * (2 * a₀ + 1)))
    simp only [MonoidHom.comp_apply] at h
    rw [show a₀ + (k + 1) * (2 * a₀ + 1) = a₀ + k * (2 * a₀ + 1) + (2 * a₀ + 1) by ring, ← h]
    rfl

end CFSG.HardMathSupport.C14ExcRee
