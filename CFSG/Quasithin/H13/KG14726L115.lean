module

public import CFSG.Quasithin.H13.KG14726C27
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.H13.KG14726Elim

public noncomputable section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open Subgroup KG14726

@[expose] def KG14726SporadicInput (s : TauCeti.SporadicName) : Prop :=
  TwoCentralConstrained (NativeSporadic.Carrier s)

namespace KG14726

variable {L S : Type*} [Group L] [Group S]

theorem surjective_comp_mk' {N : Subgroup L} [N.Normal] (e : L ⧸ N ≃* S) :
    Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' N)) :=
  e.surjective.comp (QuotientGroup.mk'_surjective N)

theorem center_eq_bot_of_quotient (hqs : CFSG.IsQuasisimple L) {N : Subgroup L} [N.Normal]
    [IsSimpleGroup S] (e : L ⧸ N ≃* S) : center S = ⊥ := by
  set E := quotientCenterEquivOfSurjective hqs _ (surjective_comp_mk' e)
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hqs.2.2
    apply hab
    apply E.injective
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (E a)
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (E b)
    rw [map_mul, map_mul, ← hx, ← hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have hyc : y ∈ center S := h ▸ mem_top y
    rw [mem_center_iff.mp hyc x]

@[expose] def quotientCenterEquivOfQuotient (hqs : CFSG.IsQuasisimple L) {N : Subgroup L}
    [N.Normal] [IsSimpleGroup S] (e : L ⧸ N ≃* S) : L ⧸ center L ≃* S :=
  (quotientCenterEquivOfSurjective hqs _ (surjective_comp_mk' e)).trans
    (quotientCenterEquivSelf (center_eq_bot_of_quotient hqs e))

end KG14726

open KG14726

end CFSG.Quasithin.H13

end
