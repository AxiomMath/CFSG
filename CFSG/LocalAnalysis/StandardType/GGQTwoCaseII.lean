module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIITypes
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIIDual
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIIA
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIIE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2_caseII_lin {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (hII : D.CaseII)
    (h4 : 4 ≤ Fintype.card D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod p] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod p) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod p] D.V))) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod p) {φ x} = Submodule.span (ZMod p) {r x} := by
  subst hp
  have hsym := ggQ2_caseII_cartan_symm D hII h4
  refine ggQ2_P3_of_dual_pm D hsym A hW x ?_
  rcases ggQ2_caseII_types D hII h4 with ⟨m, e, hm, h3, hA, ha⟩ | ⟨e, hE, ha⟩
  · exact ggQ2_caseII_A_pm D hsym hII hm h3 e hA ha x hx A hW hTF hHL
  · exact ggQ2_caseII_E6_pm D hsym hII e hE ha x hx A hW hTF hHL

end CFSG.StandardType

end
