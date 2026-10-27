module

public import CFSG.RankThree.PartTwo.Sec13.KF135FamOddGL2
import CFSG.RankThree.PartTwo.KFacts.K71bOutAbelian

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

open CFSG Subgroup
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace FamOdd

theorem psl2_hyp_false {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)}
    {x u : MulAut S} {V : Subgroup (MulAut S)} {r e : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    (φ : S ≃* projSL 2 (GaloisField r e)) (h : KF135Hyp S p P x u V) : False := by
  have hc : ∀ σ τ : MulAut S, σ * τ * σ⁻¹ * τ⁻¹ ∈ inner S := fun σ τ =>
    KFacts.isInnerAut_commutator_of_mulEquiv_psl2_all (φ.trans (Sec4.projSLEquivPSL _)) σ τ
  have hk : ringChar (GaloisField r e) ≠ 2 := by
    rw [ringChar.eq (GaloisField r e) r]
    exact hr
  refine false_of_noTwoAut h (V_le_inner_of_comm h hc) ?_
  exact NoTwoAut.of_injective ((projSL 2 (GaloisField r e)).subtype.comp φ.toMonoidHom)
    (Subtype.val_injective.comp φ.injective)
    (noTwoAut_pgl2 (GaloisField r e) hk h.prime (by linarith [h.seven_le]))

end FamOdd

theorem kF135At_fam1 : KF135At Fam1 := by
  intro S _ _ p P x u V hF h
  obtain ⟨r, e, hr, hr2, -, ⟨φ⟩⟩ := hF
  exact (FamOdd.psl2_hyp_false hr2 φ h).elim

end CFSG.RankThree.PartTwo.Sec13.KF135Proof
