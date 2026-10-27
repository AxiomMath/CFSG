module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerCore
public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggGamma_range_hypsSC_K {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    IsElemAbelian p (ggGamma K hBsN).range ∧
      (∀ a ∈ (ggGamma K hBsN).range, ∃ φ ∈ I, ∀ l : K,
        φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      p ^ 3 ≤ Nat.card (ggGamma K hBsN).range ∧ GGTorusSelfCent p (ggGamma K hBsN).range := by
  obtain ⟨hp, hBs, -, -, -⟩ := hH.1.tableB_facts
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  refine ⟨isElemAbelian_range hBc hBp _, ?_, ?_,
    ggTorusSelfCent_ggGamma hBsN hH.1.2.1.2.2.2⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hBsN b, ggBeta_mem K θ hBsN hBs3 b,
      fun l => ggBeta_ggQuotHom K hBsN θ b l⟩
  · have hS : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
    have hBBs : B ≤ Bs := hH.1.2.1.1
    have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hBsN
    have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
    have hle : Nat.card (ggGamma K hBN).range ≤ Nat.card (ggGamma K hBsN).range := by
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨b, rfl⟩
      exact ⟨⟨b, hBBs b.2⟩, rfl⟩
    have h4 := pow_four_le_card_of_bmax hp hS.1 hH.1.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact (Nat.le_of_mul_le_mul_right h4 hp.pos).trans hle

end CFSG.StandardType
