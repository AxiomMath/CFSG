module

public import CFSG.RankThree.PartOne.KLR.TwistPerm
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4

variable {L : Type} [Field L] [CharP L 2] {F : MulAut (adjointGroup ReeTag.F4.tag L)}
  (u : WeylGroup ReeTag.F4.tag) {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}

@[expose] noncomputable def conjTwist (F : MulAut (adjointGroup ReeTag.F4.tag L))
    (u : WeylGroup ReeTag.F4.tag) (n : ModGL ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L :=
  canonicalRep (coxeterSystem ReeTag.F4.tag) L u * n *
    (Fext F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹

omit [CharP L 2] in
theorem transport_iso (hS : ∀ γ ∈ S, IsRoot ReeTag.F4.tag γ) (n : ModGL ReeTag.F4.tag L)
    {G : Type} [Group G]
    (e : G ≃* ↥(rootSpan ReeTag.F4.tag L ((fun γ => u • γ) '' S) ⊓
      twistedFixed F (conjTwist F u n))) :
    Nonempty (G ≃* ↥(rootSpan ReeTag.F4.tag L S ⊓ twistedFixed F n)) := by
  have hmap := map_conj_rootSpan_inf_twistedFixed (F := F) u hS n
  refine ⟨e.trans ((MulEquiv.subgroupCongr hmap.symm).trans
    (Subgroup.equivMapOfInjective _ (MulAut.conj
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).toMonoidHom
      (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L u)).injective).symm)⟩

omit [CharP L 2] in
theorem transport_cent (hS : ∀ γ ∈ S, IsRoot ReeTag.F4.tag γ) (n : ModGL ReeTag.F4.tag L)
    (h : ∀ q ∈ rootSpan ReeTag.F4.tag L ((fun γ => u • γ) '' S),
      (∀ w ∈ rootSpan ReeTag.F4.tag L ((fun γ => u • γ) '' S) ⊓
        twistedFixed F (conjTwist F u n), q * w = w * q) → q = 1) :
    ∀ q ∈ rootSpan ReeTag.F4.tag L S,
      (∀ w ∈ rootSpan ReeTag.F4.tag L S ⊓ twistedFixed F n, q * w = w * q) → q = 1 := by
  intro q hq hcomm
  set nu := canonicalRep (coxeterSystem ReeTag.F4.tag) L u with hnu
  have hmapQ := map_conj_rootSpan (L := L) u hS
  have hq' : nu * q * nu⁻¹ ∈ rootSpan ReeTag.F4.tag L ((fun γ => u • γ) '' S) := by
    rw [← hmapQ]
    exact ⟨q, hq, by simp [hnu, MulAut.conj_apply]⟩
  have hmap := map_conj_rootSpan_inf_twistedFixed (F := F) u hS n
  have h1 : nu * q * nu⁻¹ = 1 := by
    refine h _ hq' fun w hw => ?_
    have hw' := hw
    change w ∈ rootSpan ReeTag.F4.tag L ((fun γ => u • γ) '' S) ⊓ twistedFixed F
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L u * n *
        (Fext F (canonicalRep (coxeterSystem ReeTag.F4.tag) L u))⁻¹) at hw'
    rw [← hmap] at hw'
    obtain ⟨w₀, hw₀, rfl⟩ := hw'
    have hc := hcomm w₀ hw₀
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc nu * q * nu⁻¹ * (nu * w₀ * nu⁻¹) = nu * (q * w₀) * nu⁻¹ := by group
      _ = nu * (w₀ * q) * nu⁻¹ := by rw [hc]
      _ = nu * w₀ * nu⁻¹ * (nu * q * nu⁻¹) := by group
  have h2 : q = nu⁻¹ * (nu * q * nu⁻¹) * nu := by group
  rw [h2, h1]
  group

end CFSG.RankThree.PartOne.TCX.Ree
