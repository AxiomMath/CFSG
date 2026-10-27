module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AltLocal17
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASMaster
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASShape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81 (InFSqAS calNIn CFShape)

@[expose] def K_SporadicNoncentralThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y) (s : TauCeti.SporadicName),
    KYForm Y K S → IsSpor (↥K ⧸ Subgroup.center ↥K) s →
    (s = .J1 ∨ s = .M12 ∨ s = .M22 ∨ s = .HS ∨ s = .Ru ∨ s = .ONan) →
      ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
        ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S

@[expose] def K_ONanLattice : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    IsSpor (↥K ⧸ Subgroup.center ↥K) .ONan →
      ∃ H₁ H₂ M₁ M₂ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ H₁ ⊔ H₂ = ⊤ ∧
        3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂ ∧
        calNIn H₁ S = {M₁} ∧ Group.IsSolvable ↥H₁ ∧
        calNIn H₂ S = {M₂} ∧ CFShape ↥H₂ (fun X _ => IsL3 X 2)

@[expose] def K_ONanDeltaAS : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y),
    K.Normal →
    CFSG.Open.IsQuasisimple ↥K →
    Odd (Nat.card (Subgroup.center ↥K)) →
    IsSpor (↥K ⧸ Subgroup.center ↥K) .ONan →
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
    (∃ n : ℕ, K.index = 2 ^ n) →
    CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      ∃ H₁ H₂ : Subgroup Y,
        S ≤ H₁ ∧ S ≤ H₂ ∧ H₁ ⊔ H₂ = ⊤ ∧
          3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂ ∧ InFSqAS 2 H₁ ∧ InFSqAS 2 H₂

theorem k_ONanDeltaAS_of_lattice (h : K_ONanLattice) :
    K_ONanDeltaAS := by
  intro Y _ _ K S hKn hKq hKo hON hC hidx hS
  obtain ⟨H₁, H₂, M₁, M₂, hS₁, hS₂, hsup, h3₁, h3₂, hU₁, hsol, hU₂, hCF⟩ :=
    h Y K S ⟨hKn, hKq, hKo, hC, hidx, hS⟩ hON
  have hT₁ : CFSG.Quasithin.IsSylowIn 2 S H₁ :=
    CFSG.LocalAnalysis.WeakClosure81.isSylowIn_of_le_of_le hS hS₁ le_top
  have hT₂ : CFSG.Quasithin.IsSylowIn 2 S H₂ :=
    CFSG.LocalAnalysis.WeakClosure81.isSylowIn_of_le_of_le hS hS₂ le_top
  refine ⟨H₁, H₂, hS₁, hS₂, hsup, h3₁, h3₂, ?_, ?_⟩
  · have := hsol
    exact CFSG.LocalAnalysis.WeakClosure81.inFSqAS_of_cfShape (by norm_num) hT₁ hU₁
      (CFSG.LocalAnalysis.WeakClosure81.cfShape_of_isSolvable _)
      CFSG.LocalAnalysis.WeakClosure81.shapeInEAS_l3sp4_four
  · exact CFSG.LocalAnalysis.WeakClosure81.inFSqAS_of_cfShape (by norm_num) hT₂ hU₂
      (fun L _ hL hnc => Or.inl (hCF L hL hnc))
      CFSG.LocalAnalysis.WeakClosure81.shapeInEAS_l3sp4_four

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
