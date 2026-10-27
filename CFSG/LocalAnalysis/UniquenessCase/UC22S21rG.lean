module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rC
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Quasithin (IsSylowIn)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s21rg_pieces_le_or_le {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {M T H₁ H₂ : Subgroup G}
    (hTM : IsSylowIn 2 T M) (hT₁ : T ≤ H₁) (hT₂ : T ≤ H₂)
    (hH : ∀ X : Subgroup G, X ≤ M → T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {P : Subgroup (Bar2 M)} (hP : IsPGroup q ↥P)
    (hTP : barImage M T ≤ normalizer (P : Set (Bar2 M))) :
    ∃ 𝓡 : Set (Subgroup (Bar2 M)), sSup 𝓡 = P ∧ ∀ R ∈ 𝓡, R ≤ P ∧ IsPiece q (barImage M T) R ∧
      (barPreimage M (R ⊔ barImage M T) ≤ H₁ ∨ barPreimage M (R ⊔ barImage M T) ≤ H₂) := by
  have hS : IsPGroup 2 ↥(barImage M T) :=
    isPGroup_map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
      (uc22s21rd_isSylowIn_subgroupOf hTM).isPGroup
  refine ⟨{R | R ≤ P ∧ IsPiece q (barImage M T) R}, uc22s21rc_sSup_pieces hq hq2 hS hP hTP, ?_⟩
  rintro R ⟨hRP, hR⟩
  exact ⟨hRP, hR, uc22s21re_le_or_le hq hq2 hTM hT₁ hT₂ hH hR⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
