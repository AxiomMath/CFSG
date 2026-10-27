module

public import CFSG.RankThree.GF2n.QuotPair
public import CFSG.RankThree.GF2n.BenderFixInner
public import CFSG.RankThree.GF2n.BenderTwoTrans
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender
open CFSG.RankThree.GF2n (QuotPair pairConj)
open scoped MatrixGroups

variable {Y : Type} [Group Y] [Finite Y]

section Certified


theorem exists_inner_of_fix {A B : Subgroup Y} (P : QuotPair A B) (h4 : 4 ≤ Nat.card A)
    {C : Subgroup Y} (hC : C ∈ pairConj A B) (σ : MulAut Y) (hσ2 : ∀ k, σ (σ k) = k)
    (hfix : ∀ c ∈ C, σ c = c) : ∃ t ∈ C, ∀ k, σ k = t * k * t⁻¹ := by
  have hCA : ∃ c : Y, C = conjSubgroup c A := by
    obtain ⟨g, hg | hg⟩ := hC
    · exact ⟨g, hg⟩
    · obtain ⟨x, hx⟩ := P.exists_conj_eq
      exact ⟨g * x, by rw [hg, hx, CFSG.RankThree.GF2n.conjSubgroup_mul]⟩
  obtain ⟨c, rfl⟩ := hCA
  have hS : StrongWC (conjSubgroup c A) :=
    CFSG.RankThree.GF2n.StrongWC.conj P.strongWC c
  have hC1 : conjSubgroup c A ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (conjSubgroup c A) = Nat.card A :=
      CFSG.RankThree.GF2n.card_conjSubgroup c A
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨-, hmod⟩ := P.models CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  rcases hmod with ⟨f, hf, -, ⟨e⟩⟩ | ⟨a, ha, -, ⟨e⟩⟩ | ⟨m, hm, hm3, hcard2, -⟩
  · exact CFSG.RankThree.GF2n.exists_conj_of_fix_linear (.linear f hf e) hS hC1 σ hfix
  · exact CFSG.RankThree.GF2n.exists_conj_of_fix_suzuki
      (.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))
      hS hC1 σ hσ2 hfix
  ·
    exfalso
    omega

end Certified

end CFSG.LocalAnalysis.WeakClosure81
