module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import Mathlib.GroupTheory.Perm.ViaEmbedding
import CFSG.LocalAnalysis.StandardType.GGOrthAnchorTransition
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorRecal
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Charts
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.TorusExtension
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.ComponentInitial

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  {E : QuadExt F K (unitaryInvolution K 2 f)}

theorem GGSecFiveBPermOmKFrame.exists_overlap_calibration_of_dvd {G : Type} [Group G]
    {Bs X₁ X₂ : Subgroup G} {n k p : ℕ} [Fact p.Prime] (hk : 1 ≤ k) (hpq : p ∣ 2 ^ f + 1)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {χ : Multiplicative (ZMod p) →* Kˣ} {π₁ π₂ : Fin (k + 4) ≃ Fin n}
    {κ₁ κ₂ : normOmega E (k + 3) →* G}
    (h₁ : GGSecFiveBPermOmKFrame E Bs X₁ eta π₁ κ₁ χ)
    (h₂ : GGSecFiveBPermOmKFrame E Bs X₂ eta π₂ κ₂ χ)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hX₁ : ∀ b : Bs, (b : G) ∈ X₁ → eta b (π₁ (Fin.last (k + 3))) = 1)
    (hX₂ : ∀ b : Bs, (b : G) ∈ X₂ → eta b (π₂ (Fin.last (k + 3))) = 1)
    (hne : π₁ (Fin.last (k + 3)) ≠ π₂ (Fin.last (k + 3)))
    (hpair : ∀ P₁ P₂ : Finset (Fin (k + 3)), P₁.card = 2 → P₂.card = 2 →
      (fun i => π₁ i.castSucc) '' (P₁ : Set (Fin (k + 3))) =
        (fun j => π₂ j.castSucc) '' (P₂ : Set (Fin (k + 3))) →
      (normBlock E (k + 3) P₁).map κ₁ = (normBlock E (k + 3) P₂).map κ₂) :
    ∃ (π₁' π₂' : Fin (k + 4) ≃ Fin n) (κ₁' κ₂' : normOmega E (k + 3) →* G),
      GGSecFiveBPermOmKFrame E Bs X₁ eta π₁' κ₁' χ ∧
      GGSecFiveBPermOmKFrame E Bs X₂ eta π₂' κ₂' χ ∧
      π₁' (Fin.last (k + 3)) = π₁ (Fin.last (k + 3)) ∧
      π₂' (Fin.last (k + 3)) = π₂ (Fin.last (k + 3)) ∧
      π₂' = (finRotate (k + 4)).trans π₁' ∧
      (∀ y : normOmega E (k + 2),
        κ₁' (normPerm E (by omega) (finRotate (k + 3)) *
            normOmegaCast E (by omega : k + 2 ≤ k + 3) y *
            (normPerm E (by omega) (finRotate (k + 3)))⁻¹) =
          κ₂' (normOmegaCast E (by omega : k + 2 ≤ k + 3) y)) ∧
      (κ₁'.comp (normPerm E (by omega : 3 ≤ k + 3))).comp
          (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 2))) =
        (κ₂'.comp (normPerm E (by omega : 3 ≤ k + 3))).comp
          (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) := by
  obtain ⟨π₁', π₂', κ₁', κ₂', α, h₁', h₂', hl₁, hl₂, hrot, hα, hfix⟩ :=
    h₁.exists_overlap_transition_of_dvd hpq h₂ hSC hX₁ hX₂ hne hpair
  obtain ⟨β, hβcast, hβτ, -⟩ := exists_extension_of_fixes_normPlaneTorus E (m := k + 2)
    (by omega : 3 ≤ k + 2) hpq h₁.2.2.1 α hfix
  let κ₂'' : normOmega E (k + 3) →* G := κ₂'.comp β.toMonoidHom
  have h₂'' : GGSecFiveBPermOmKFrame E Bs X₂ eta π₂' κ₂'' χ :=
    h₂'.comp_mulAut_of_fixes_normPlaneTorus (by omega : 2 ≤ k + 3) hpq β hβτ
  let Pρ : normOmega E (k + 3) := normPerm E (by omega : 3 ≤ k + 3) (finRotate (k + 3))
  have hpoint : ∀ y : normOmega E (k + 2),
      κ₁' (Pρ * normOmegaCast E (by omega : k + 2 ≤ k + 3) y * Pρ⁻¹) =
        κ₂'' (normOmegaCast E (by omega : k + 2 ≤ k + 3) y) := by
    intro y
    have hβy := hβcast y
    calc κ₁' (Pρ * normOmegaCast E (by omega : k + 2 ≤ k + 3) y * Pρ⁻¹)
        = κ₂' (normOmegaCast E (by omega : k + 2 ≤ k + 3) (α y)) := by
          simpa only [Pρ] using (hα y).symm
      _ = κ₂' (β (normOmegaCast E (by omega : k + 2 ≤ k + 3) y)) := by rw [hβy]
      _ = κ₂'' (normOmegaCast E (by omega : k + 2 ≤ k + 3) y) := rfl
  have hperm : (κ₁'.comp (normPerm E (by omega : 3 ≤ k + 3))).comp
      (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 2))) =
      (κ₂''.comp (normPerm E (by omega : 3 ≤ k + 3))).comp
        (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) := by
    apply MonoidHom.ext
    intro σ'
    change κ₁' ((normPerm E (by omega : 3 ≤ k + 3))
        ((Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 2))) σ')) =
      κ₂'' ((normPerm E (by omega : 3 ≤ k + 3))
        ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) σ'))
    have hconj := congrArg (normPerm E (by omega : 3 ≤ k + 3))
      (viaEmbeddingHom_succEmb_eq_conj (k + 2) σ')
    have hconj' : normPerm E (by omega : 3 ≤ k + 3)
        ((Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 2))) σ') =
        Pρ * normPerm E (by omega : 3 ≤ k + 3)
          ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) σ') *
          Pρ⁻¹ := by
      rw [hconj]
      simp only [map_mul, map_inv]
      rfl
    rw [hconj']
    let y : normOmega E (k + 2) := normPerm E (by omega : 3 ≤ k + 2) σ'
    have hX : normPerm E (by omega : 3 ≤ k + 3)
        ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) σ') =
        normOmegaCast E (by omega : k + 2 ≤ k + 3) y := by
      have hσ : ∀ i : Fin (k + 2),
          (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) σ'
            (Fin.castSucc i) = Fin.castSucc (σ' i) := by
        intro i
        rw [Equiv.Perm.viaEmbeddingHom_apply, ← Fin.castSuccEmb_apply i,
          Equiv.Perm.viaEmbedding_apply, Fin.castSuccEmb_apply]
      have h := normPerm_eq_normOmegaCast_normPerm E (by omega : 3 ≤ k + 2) σ'
        ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) σ') hσ
      simpa [y] using h
    rw [hX]
    exact hpoint y
  exact ⟨π₁', π₂', κ₁', κ₂'', h₁', h₂'', hl₁, hl₂, hrot, hpoint, hperm⟩

theorem GGSecFiveBPermOmKFrame.exists_overlap_calibration_of_component_of_dvd {G : Type}
    [Group G] [Finite G] {Bs X₁ X₂ : Subgroup G} {y₁ y₂ : G} {n k p : ℕ} [Fact p.Prime]
    (hk : 1 ≤ k) (hpq : p ∣ 2 ^ f + 1)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {χ : Multiplicative (ZMod p) →* Kˣ}
    {π₁ π₂ : Fin (k + 4) ≃ Fin n} {κ₁ κ₂ : normOmega E (k + 3) →* G}
    (h₁ : GGSecFiveBPermOmKFrame E Bs X₁ eta π₁ κ₁ χ)
    (h₂ : GGSecFiveBPermOmKFrame E Bs X₂ eta π₂ κ₂ χ)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hy₁ : y₁ ∈ Bs) (hX₁c : CFSG.Open.IsComponentOf X₁ (Subgroup.centralizer ({y₁} : Set G)))
    (hy₂ : y₂ ∈ Bs) (hX₂c : CFSG.Open.IsComponentOf X₂ (Subgroup.centralizer ({y₂} : Set G)))
    (hX₁ : ∀ b : Bs, (b : G) ∈ X₁ → eta b (π₁ (Fin.last (k + 3))) = 1)
    (hX₂ : ∀ b : Bs, (b : G) ∈ X₂ → eta b (π₂ (Fin.last (k + 3))) = 1)
    (hne : π₁ (Fin.last (k + 3)) ≠ π₂ (Fin.last (k + 3))) :
    ∃ (π₁' π₂' : Fin (k + 4) ≃ Fin n) (κ₁' κ₂' : normOmega E (k + 3) →* G),
      GGSecFiveBPermOmKFrame E Bs X₁ eta π₁' κ₁' χ ∧
      GGSecFiveBPermOmKFrame E Bs X₂ eta π₂' κ₂' χ ∧
      π₁' (Fin.last (k + 3)) = π₁ (Fin.last (k + 3)) ∧
      π₂' (Fin.last (k + 3)) = π₂ (Fin.last (k + 3)) ∧
      π₂' = (finRotate (k + 4)).trans π₁' ∧
      (∀ y : normOmega E (k + 2),
        κ₁' (normPerm E (by omega) (finRotate (k + 3)) *
            normOmegaCast E (by omega : k + 2 ≤ k + 3) y *
            (normPerm E (by omega) (finRotate (k + 3)))⁻¹) =
          κ₂' (normOmegaCast E (by omega : k + 2 ≤ k + 3) y)) ∧
      (κ₁'.comp (normPerm E (by omega : 3 ≤ k + 3))).comp
          (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 2))) =
        (κ₂'.comp (normPerm E (by omega : 3 ≤ k + 3))).comp
          (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) := by
  refine h₁.exists_overlap_calibration_of_dvd hk hpq h₂ hSC hX₁ hX₂ hne
    fun P₁ P₂ hP₁ hP₂ himg => ?_
  rw [← h₁.blockComm_eq_map_normBlock hSC hy₁ hX₁c (by omega) (by omega),
    ← h₂.blockComm_eq_map_normBlock hSC hy₂ hX₂c (by omega) (by omega), himg]

end CFSG.StandardType

end
