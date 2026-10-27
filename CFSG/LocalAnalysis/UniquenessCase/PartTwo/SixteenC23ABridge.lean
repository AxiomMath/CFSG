module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ABridgeO
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ABridgeR
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23APair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem c23a_pair_of_modPair {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G))
    {L₁ L₂ : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV))}
    {E₁ E₂ Z₁ Z₂ : Subgroup (Vtil (⊥ : Subgroup G) V hV)}
    (hP : C23AModPair (barSub (⊥ : Subgroup G) V hV M) L₁ L₂ E₁ E₂ Z₁ Z₂)
    (hcent : ∀ w ∈ (preTil (⊥ : Subgroup G) V hV E₁ : Set G) ∪
      (preTil (⊥ : Subgroup G) V hV E₂ : Set G), w ≠ 1 → centralizer ({w} : Set G) ≤ M) :
    C23APair M V (preTil (⊥ : Subgroup G) V hV E₁) (preTil (⊥ : Subgroup G) V hV E₂) where
  elem := hV
  norm := hM
  le := preTil_le _ V hV _
  le' := preTil_le _ V hV _
  sup := c23a_bridge_sup hV hP.sup
  three := by
    have h1 := c23a_bridge_mSub hV E₁
    have h2 := c23a_block_rk_eq hP.blk₁
    omega
  three' := by
    have h1 := c23a_bridge_mSub hV E₂
    have h2 := c23a_block_rk_eq hP.blk₂
    omega
  perm := c23a_bridge_perm hV hM fun φ hφ =>
    (hP.perm φ hφ).imp (fun ⟨_, _, a, b⟩ => ⟨a, b⟩) id
  cent := hcent
  oneSided := c23a_bridge_oneSided hV hM hP
  rankLe := c23a_bridge_rankLe hV hM hP
  rankLe' := c23a_bridge_rankLe hV hM hP.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
