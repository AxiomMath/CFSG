module

public import CFSG.LieType.Ree.Endo
public import CFSG.LieType.Chevalley.LangG2ClosureExceptional
public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived

public section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

section Formulas

variable (t : ReeTag) (L : Type) [Field L]

@[expose] def IsReeExceptional (Φ : MulAut (adjointGroup t.tag L)) : Prop :=
  ∀ (i : Fin t.tag.rank) (c : L), Φ (xElement i c) = xElement (t.perm i) (c ^ t.exponent i) ∧
    Φ (yElement i c) = yElement (t.perm i) (c ^ t.exponent i)

variable {t L}

theorem IsReeExceptional.comp_self [CharP L t.prime] {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) :
    Φ.toMonoidHom.comp Φ.toMonoidHom = frobeniusTwist t.tag L (iterateFrobenius L t.prime 1) := by
  refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
  · show Φ (Φ (xElement i c)) = frobeniusTwist t.tag L (iterateFrobenius L t.prime 1)
      (xElement i c)
    rw [(hΦ i c).1, (hΦ (t.perm i) (c ^ t.exponent i)).1, ReeTag.perm_perm, ← pow_mul,
      ReeTag.exponent_mul_exponent_perm, frobeniusTwist_xElement, iterateFrobenius_def, pow_one]
  · show Φ (Φ (yElement i c)) = frobeniusTwist t.tag L (iterateFrobenius L t.prime 1)
      (yElement i c)
    rw [(hΦ i c).2, (hΦ (t.perm i) (c ^ t.exponent i)).2, ReeTag.perm_perm, ← pow_mul,
      ReeTag.exponent_mul_exponent_perm, frobeniusTwist_yElement, iterateFrobenius_def, pow_one]

theorem IsReeExceptional.comm_frobenius [CharP L t.prime] {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) :
    Φ.toMonoidHom.comp (frobeniusTwist t.tag L (iterateFrobenius L t.prime 1)) =
      (frobeniusTwist t.tag L (iterateFrobenius L t.prime 1)).comp Φ.toMonoidHom := by
  refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
  · show Φ (frobeniusTwist t.tag L (iterateFrobenius L t.prime 1) (xElement i c)) =
      frobeniusTwist t.tag L (iterateFrobenius L t.prime 1) (Φ (xElement i c))
    rw [frobeniusTwist_xElement, (hΦ i _).1, (hΦ i c).1, frobeniusTwist_xElement,
      iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_mul, mul_comm]
  · show Φ (frobeniusTwist t.tag L (iterateFrobenius L t.prime 1) (yElement i c)) =
      frobeniusTwist t.tag L (iterateFrobenius L t.prime 1) (Φ (yElement i c))
    rw [frobeniusTwist_yElement, (hΦ i _).2, (hΦ i c).2, frobeniusTwist_yElement,
      iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_mul, mul_comm]

theorem isReeExceptional_finiteExceptionalAut {K : Type} [Field K] [Finite K] [CharP K t.prime] :
    IsReeExceptional t K (t.finiteExceptionalAut K) := fun i c =>
  ⟨ReeTag.finiteExceptionalAut_xElement i c, ReeTag.finiteExceptionalAut_yElement i c⟩

end Formulas

end CFSG.RankThree.PartOne.RF4
