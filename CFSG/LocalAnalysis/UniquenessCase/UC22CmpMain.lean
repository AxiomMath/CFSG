module

public import CFSG.LocalAnalysis.UniquenessCase.UC22CmpSeed
public import CFSG.LocalAnalysis.UniquenessCase.UC22CmpX
import CFSG.LocalAnalysis.UniquenessCase.UC22K339Z
import CFSG.LocalAnalysis.UniquenessCase.UC22SeedMain
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sa

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (InClassG tripleE InClassX oResidualTwo omegaOneCenterIn)
open CFSG.QuasithinUnique.Setup.Campbell (Fcore)
open P22s

variable {G : Type} [Group G] [Finite G]

namespace P22k

theorem campbell_seed (D : Data G) {X H₀ : Subgroup G}
    (hSX : proofS D ≤ X) (hSH : proofS D ≤ H₀)
    (hX : InClassG ↥(proofS D) ↥X (Subgroup.inclusion hSX))
    (hH : InClassG ↥(proofS D) ↥H₀ (Subgroup.inclusion hSH))
    (hZX : ¬ X ≤ centralizer (omegaOneCenterIn (proofS D) : Set G))
    (hZ : ¬ H₀ ≤ centralizer (omegaOneCenterIn (proofS D) : Set G)) :
    (∀ g ∈ normalizer (proofS D : Set G), ∀ e ∈ omegaZJ22 (pCoreOf 2 H₀), g * e * g⁻¹ ∈ pCoreOf 2 X) ∨
      InClassX ↥(oResidualTwo ↥H₀) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := proofS D with hSdef
  have hS2 : IsPGroup 2 ↥S := D.sylowM.isPGroup.to_le inf_le_left
  have hSJ := centralizer_elemThompsonCenterTorsion_proofS D
  set ι : ↥S →* ↥X := Subgroup.inclusion hSX with hι
  set ι₀ : ↥S →* ↥H₀ := Subgroup.inclusion hSH with hι₀
  obtain ⟨k₁, _, _, P₁, ρ₁, ψ₁, hP₁, h₁⟩ :=
    k339SeedBridge ↥S hS2 hSJ ↥H₀ ι₀ hH (commutator_omegaOne_ne_bot hSH hZ)
  obtain ⟨k₂, _, _, P₂, ρ₂, ψ₂, hP₂, h₂⟩ :=
    k339SeedBridge ↥S hS2 hSJ ↥X ι hX (commutator_omegaOne_ne_bot hSX hZX)
  by_cases hB : (K339.seedOf hH.injective hP₁ h₁).BlockType
  ·
    right
    obtain ⟨V', hV'S, hV'n, hV'e, hSV', hsup⟩ := hB
    exact inClassX_oResidualTwo_of_supplement hH.fitting_eq h₁ hV'S hV'n hV'e hSV' hsup
  ·
    left
    intro g hg e he
    rw [← map_tripleE H₀] at he
    obtain ⟨y, hy, rfl⟩ := he
    obtain ⟨s, hs⟩ := tripleE_le_range hH hy
    set α : MulAut ↥S := S.normalizerMonoidHom ⟨g, hg⟩ with hα
    have hαs : ((α s : ↥S) : G) = g * (s : G) * g⁻¹ := Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
    have hle := ((K339.seedOf hH.injective hP₁ h₁).fh_map_le_core_or_blockType
      (K339.seedOf hX.injective hP₂ h₂) α).resolve_right hB
    have hsF : s ∈ (K339.seedOf hH.injective hP₁ h₁).Fh := by
      show (K339.seedOf hH.injective hP₁ h₁).f s ∈ Fcore ↥H₀
      rw [K339.seedOf_f_apply, ← K339.tripleE_eq_Fcore]
      change ι₀ s ∈ tripleE ↥H₀
      rw [hs]
      exact hy
    have hcore : ι (α s) ∈ CFSG.pCore 2 ↥X :=
      hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hsF))
    rw [← map_pCore X]
    refine ⟨ι (α s), hcore, ?_⟩
    change ((α s : ↥S) : G) = g * ((y : ↥H₀) : G) * g⁻¹
    rw [hαs, ← hs]
    rfl

end P22k

end CFSG.LocalAnalysis.UniquenessCase.UC22
