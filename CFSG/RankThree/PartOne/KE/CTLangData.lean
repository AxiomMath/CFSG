module

public import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

theorem frobenius_canonicalRep {τ : Tag} {L : Type} [Field L] (Fr : L →+* L) (w : WeylGroup τ) :
    Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem τ) L w) =
      canonicalRep (coxeterSystem τ) L w := by
  have h : Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem τ) L w) =
      baseChangeGL Fr (canonicalRep (coxeterSystem τ) L w) := Units.ext rfl
  rw [h]
  exact baseChangeGL_canonicalRep Fr w

theorem lang_conjugator (τ : Tag) (K : Type) [Field K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (w : WeylGroup τ) :
    ∃ g0 : ModGL τ L, g0 ∈ adjointGroup τ L ∧
      Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 =
        g0 * canonicalRep (coxeterSystem τ) L w := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity ℓ L f hf).1 τ
  obtain ⟨g, hg⟩ := hLang ⟨canonicalRep (coxeterSystem τ) L w,
    canonicalRep_mem_adjointGroup (coxeterSystem τ) L w⟩
  refine ⟨(g : ModGL τ L), g.2, ?_⟩
  rw [← hS g]
  have h1 : S g = g * ⟨canonicalRep (coxeterSystem τ) L w,
      canonicalRep_mem_adjointGroup (coxeterSystem τ) L w⟩ := by
    rw [hg, mul_inv_cancel_left]
  rw [h1]
  rfl

theorem lang_conjugator_twisted (K : Type) [Field K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (w : WeylGroup TwistTag.E6.tag) :
    ∃ g0 : ModGL TwistTag.E6.tag L, g0 ∈ adjointGroup TwistTag.E6.tag L ∧
      twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity ℓ L f hf).2
    TwistTag.E6 1
  obtain ⟨g, hg⟩ := hLang ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) L w,
    canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.E6.tag) L w⟩
  refine ⟨(g : ModGL TwistTag.E6.tag L), g.2, ?_⟩
  have h1 : S g = g * ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) L w,
      canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.E6.tag) L w⟩ := by
    rw [hg, mul_inv_cancel_left]
  have h2 := hS g
  rw [h1, zpow_one] at h2
  exact h2.symm.trans (by rfl)

end CFSG.RankThree.PartOne.KE
