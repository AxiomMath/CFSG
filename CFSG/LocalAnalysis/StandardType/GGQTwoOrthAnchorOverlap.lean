module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import Mathlib.GroupTheory.Perm.ViaEmbedding
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorAut
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorRecal
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorTorus
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockGeneration
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
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

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
  {E : QuadExt F K (unitaryInvolution K 2 1)}

private theorem oaK_viaEmbedding_castSucc {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin m ↪ Fin (m + 1)) σ) (Fin.castSucc i) =
      Fin.castSucc (σ i) := by
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  exact Equiv.Perm.viaEmbedding_apply σ Fin.castSuccEmb i

private theorem oaK_finRotate_castSucc {k : ℕ} {j : Fin (k + 3)}
    (hj : j ≠ Fin.last (k + 2)) :
    finRotate (k + 4) (Fin.castSucc j) = Fin.castSucc (finRotate (k + 3) j) := by
  apply Fin.ext
  rw [coe_finRotate (i := Fin.castSucc j)]
  simp only [Fin.val_castSucc]
  rw [coe_finRotate (i := j)]
  rw [if_neg (Fin.castSucc_ne_last j), if_neg hj]

private theorem oaK_finRotate_castSucc_last {k : ℕ} :
    finRotate (k + 4) (Fin.castSucc (Fin.last (k + 2))) = Fin.last (k + 3) := by
  exact finRotate_of_lt (n := k + 3) (k := k + 2) (by omega : k + 2 < k + 3)

private theorem oaK_pi₂'_castSucc_of_ne_last {k n : ℕ} {π₁' π₂' : Fin (k + 4) ≃ Fin n}
    (hπ₂' : π₂' = (finRotate (k + 4)).trans π₁') {j : Fin (k + 3)}
    (hj : j ≠ Fin.last (k + 2)) :
    π₂' (Fin.castSucc j) = π₁' (Fin.castSucc (finRotate (k + 3) j)) := by
  rw [hπ₂', Equiv.trans_apply, oaK_finRotate_castSucc hj]

private theorem oaK_pi₂'_castSucc_last {k n : ℕ} {π₁' π₂' : Fin (k + 4) ≃ Fin n}
    (hπ₂' : π₂' = (finRotate (k + 4)).trans π₁') :
    π₂' (Fin.castSucc (Fin.last (k + 2))) = π₁' (Fin.last (k + 3)) := by
  rw [hπ₂', Equiv.trans_apply, oaK_finRotate_castSucc_last]

private theorem oaK_image_via {k n : ℕ} {π π' : Fin (k + 4) ≃ Fin n}
    {σ : Equiv.Perm (Fin (k + 3))}
    (hπ : π' =
      (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ).trans π)
    (P : Finset (Fin (k + 3))) :
    (fun i => π i.castSucc) '' ((P.image σ : Finset (Fin (k + 3))) : Set (Fin (k + 3))) =
      (fun i => π' i.castSucc) '' (P : Set (Fin (k + 3))) := by
  rw [Finset.coe_image, Set.image_image]
  congr 1
  funext i
  rw [hπ]
  change π (Fin.castSucc (σ i)) =
    π ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ)
      (Fin.castSucc i))
  rw [show (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ)
      (Fin.castSucc i) = Fin.castSucc (σ i) from by
    rw [Equiv.Perm.viaEmbeddingHom_apply, ← Fin.castSuccEmb_apply i,
      Equiv.Perm.viaEmbedding_apply, Fin.castSuccEmb_apply]]

private theorem oaK_image_rot {k n : ℕ} {π₁' π₂' : Fin (k + 4) ≃ Fin n}
    (hπ₂' : π₂' = (finRotate (k + 4)).trans π₁') {P : Finset (Fin (k + 3))}
    (hP : P ⊆ Finset.univ.erase (0 : Fin (k + 3))) :
    (fun i => π₁' i.castSucc) '' (P : Set (Fin (k + 3))) =
      (fun j => π₂' j.castSucc) ''
        ((P.image (finRotate (k + 3)).symm : Finset (Fin (k + 3))) : Set (Fin (k + 3))) := by
  have hsymm_ne : ∀ i : Fin (k + 3), i ≠ 0 →
      (finRotate (k + 3)).symm i ≠ Fin.last (k + 2) := by
    intro i hi hlast
    apply hi
    calc i = (finRotate (k + 3)) ((finRotate (k + 3)).symm i) :=
          (Equiv.apply_symm_apply _ i).symm
      _ = (finRotate (k + 3)) (Fin.last (k + 2)) := by rw [hlast]
      _ = 0 := finRotate_last
  have hi0_of_mem : ∀ {i : Fin (k + 3)}, i ∈ P → i ≠ 0 := by
    intro i hi
    have h := hP (by simpa using hi)
    simpa using h
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨(finRotate (k + 3)).symm i, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨i, by simpa using hi, rfl⟩
    · change π₂' (Fin.castSucc ((finRotate (k + 3)).symm i)) = π₁' (Fin.castSucc i)
      rw [oaK_pi₂'_castSucc_of_ne_last hπ₂' (hsymm_ne i (hi0_of_mem hi)),
        Equiv.apply_symm_apply]
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_coe, Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    refine ⟨i, by simpa using hi, ?_⟩
    change π₁' (Fin.castSucc i) = π₂' (Fin.castSucc ((finRotate (k + 3)).symm i))
    rw [oaK_pi₂'_castSucc_of_ne_last hπ₂' (hsymm_ne i (hi0_of_mem hi)),
      Equiv.apply_symm_apply]

private theorem oaK_image_rot' {k n : ℕ} {π₁' π₂' : Fin (k + 4) ≃ Fin n}
    (hπ₂' : π₂' = (finRotate (k + 4)).trans π₁') {P : Finset (Fin (k + 3))}
    (hP : P ⊆ Finset.univ.erase (Fin.last (k + 2))) :
    (fun j => π₂' j.castSucc) '' (P : Set (Fin (k + 3))) =
      (fun i => π₁' i.castSucc) ''
        ((P.image (finRotate (k + 3)) : Finset (Fin (k + 3))) : Set (Fin (k + 3))) := by
  have hjne_of_mem : ∀ {j : Fin (k + 3)}, j ∈ P → j ≠ Fin.last (k + 2) := by
    intro j hj
    have h := hP (by simpa using hj)
    simpa using h
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨finRotate (k + 3) j, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨j, by simpa using hj, rfl⟩
    · change π₁' (Fin.castSucc (finRotate (k + 3) j)) = π₂' (Fin.castSucc j)
      rw [oaK_pi₂'_castSucc_of_ne_last hπ₂' (hjne_of_mem hj)]
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_coe, Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    refine ⟨j, by simpa using hj, ?_⟩
    change π₂' (Fin.castSucc j) = π₁' (Fin.castSucc (finRotate (k + 3) j))
    rw [oaK_pi₂'_castSucc_of_ne_last hπ₂' (hjne_of_mem hj)]

private theorem oaK_map_normBlock_conj {F K : Type} [Field F] [Field K] [Algebra F K]
    [Finite K] [CharP K 2] {f : ℕ} (E : QuadExt F K (unitaryInvolution K 2 f))
    {G : Type} [Group G] {n : ℕ} (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n))
    (P : Finset (Fin n)) (κ : normOmega E n →* G) :
    (normBlock E n P).map (κ.comp (MulAut.conj (normPerm E hn σ)).toMonoidHom) =
      (normBlock E n (P.image σ)).map κ := by
  rw [← Subgroup.map_map]
  rw [map_normBlock_normPerm]

private theorem oaK_image_erase_finRotate {k : ℕ} :
    (Finset.univ.erase (Fin.last (k + 2))).image (finRotate (k + 3)) =
      Finset.univ.erase (0 : Fin (k + 3)) := by
  rw [Finset.image_erase (Equiv.injective (finRotate (k + 3)))]
  rw [Finset.image_univ_equiv]
  rw [finRotate_last]

theorem GGSecFiveBPermOmKFrame.exists_overlap_calibration {G : Type} [Group G]
    {Bs X₁ X₂ : Subgroup G} {n k : ℕ} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {χ : Multiplicative (ZMod 3) →* Kˣ} {π₁ π₂ : Fin (k + 4) ≃ Fin n}
    {κ₁ κ₂ : normOmega E (k + 3) →* G}
    (h₁ : GGSecFiveBPermOmKFrame E Bs X₁ eta π₁ κ₁ χ)
    (h₂ : GGSecFiveBPermOmKFrame E Bs X₂ eta π₂ κ₂ χ)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
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
  let i0 : Fin n := π₁ (Fin.last (k + 3))
  let i1 : Fin n := π₂ (Fin.last (k + 3))
  have hsymm : π₁.symm i1 ≠ Fin.last (k + 3) := by
    intro h
    apply hne
    have h' : i1 = π₁ (Fin.last (k + 3)) := by
      rw [← h, Equiv.apply_symm_apply]
    exact h'.symm
  obtain ⟨j₁, hj₁⟩ := Fin.exists_castSucc_eq.mpr hsymm
  have hπ₁j₁ : π₁ (Fin.castSucc j₁) = i1 := by
    rw [hj₁, Equiv.apply_symm_apply]
  let σ₁ : Equiv.Perm (Fin (k + 3)) := Equiv.swap 0 j₁
  let π₁' : Fin (k + 4) ≃ Fin n :=
    (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ₁).trans π₁
  let κ₁' : normOmega E (k + 3) →* G :=
    κ₁.comp (MulAut.conj (normPerm E (by omega : 3 ≤ k + 3) σ₁)).toMonoidHom
  have h₁' : GGSecFiveBPermOmKFrame E Bs X₁ eta π₁' κ₁' χ :=
    h₁.comp_normPerm (by omega) (oaK_viaEmbedding_castSucc σ₁)
  have hvE₁ : (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))
      σ₁) (0 : Fin (k + 4)) = Fin.castSucc j₁ := by
    rw [Equiv.Perm.viaEmbeddingHom_apply]
    have h := Equiv.Perm.viaEmbedding_apply σ₁
      (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) (0 : Fin (k + 3))
    simpa [σ₁, Equiv.swap_apply_left] using h
  have hπ₁'_zero : π₁' 0 = i1 := by
    change π₁ ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))
      σ₁) 0) = i1
    rw [hvE₁, hπ₁j₁]
  have hlast_notMem : (Fin.last (k + 3) : Fin (k + 4)) ∉
      Set.range (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) := by
    rintro ⟨i, hi⟩
    have hval := congrArg Fin.val hi
    rw [Fin.castSuccEmb_apply, Fin.val_castSucc, Fin.val_last] at hval
    omega
  have hπ₁'_last : π₁' (Fin.last (k + 3)) = i0 := by
    change π₁ ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))
      σ₁) (Fin.last (k + 3))) = i0
    rw [Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem σ₁
        (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) (Fin.last (k + 3)) hlast_notMem]
  let π₂' : Fin (k + 4) ≃ Fin n := (finRotate (k + 4)).trans π₁'
  have hπ₂'_last : π₂' (Fin.last (k + 3)) = i1 := by
    change π₁' (finRotate (k + 4) (Fin.last (k + 3))) = i1
    rw [finRotate_last, hπ₁'_zero]
  have hτfix : (π₂'.trans π₂.symm) (Fin.last (k + 3)) = Fin.last (k + 3) := by
    change π₂.symm (π₂' (Fin.last (k + 3))) = Fin.last (k + 3)
    rw [hπ₂'_last]
    exact Equiv.symm_apply_apply π₂ _
  obtain ⟨σ₂, hσ₂⟩ := exists_perm_castSucc (π₂'.trans π₂.symm) hτfix
  have hπ₂eq : π₂' =
      (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ₂).trans π₂ := by
    apply Equiv.ext
    intro x
    rcases Fin.eq_castSucc_or_eq_last x with ⟨y, rfl⟩ | hlast
    · change π₂' (Fin.castSucc y) =
        π₂ ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ₂)
          (Fin.castSucc y))
      rw [show (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ₂)
          (Fin.castSucc y) = Fin.castSucc (σ₂ y) from by
        rw [Equiv.Perm.viaEmbeddingHom_apply, ← Fin.castSuccEmb_apply y,
          Equiv.Perm.viaEmbedding_apply, Fin.castSuccEmb_apply]]
      have h := congrArg π₂ (hσ₂ y)
      rw [Equiv.trans_apply, Equiv.apply_symm_apply] at h
      exact h
    · rw [hlast]
      rw [hπ₂'_last, Equiv.trans_apply, Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem σ₂
          (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) (Fin.last (k + 3)) hlast_notMem]
  let κ₂' : normOmega E (k + 3) →* G :=
    κ₂.comp (MulAut.conj (normPerm E (by omega : 3 ≤ k + 3) σ₂)).toMonoidHom
  have h₂' : GGSecFiveBPermOmKFrame E Bs X₂ eta π₂' κ₂' χ := by
    rw [hπ₂eq]
    exact h₂.comp_normPerm (by omega) (oaK_viaEmbedding_castSucc σ₂)
  let S₁ : Finset (Fin (k + 3)) := Finset.univ.erase 0
  let S₂ : Finset (Fin (k + 3)) := Finset.univ.erase (Fin.last (k + 2))
  have hcardS₁ : 2 ≤ S₁.card := by
    change 2 ≤ (Finset.univ.erase (0 : Fin (k + 3))).card
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hcardS₂ : 2 ≤ S₂.card := by
    change 2 ≤ (Finset.univ.erase (Fin.last (k + 2))).card
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hblock : (normBlock E (k + 3) S₁).map κ₁' =
      (normBlock E (k + 3) S₂).map κ₂' := by
    have hsymm0 : (finRotate (k + 3)).symm (0 : Fin (k + 3)) = Fin.last (k + 2) := by
      rw [Equiv.symm_apply_eq]
      exact finRotate_last.symm
    refine le_antisymm ?_ ?_
    · rw [normBlock_eq_iSup_pairs E (k + 3) S₁ hcardS₁, Subgroup.map_iSup]
      refine iSup_le fun P₁ => ?_
      obtain ⟨P, hPS, hPcard⟩ := P₁
      have hP0 : ∀ i ∈ P, i ≠ 0 := by
        intro i hi
        have h := hPS hi
        simp only [S₁, Finset.mem_erase] at h
        exact h.1
      let P₂ : Finset (Fin (k + 3)) := P.image (finRotate (k + 3)).symm
      have hP₂card : P₂.card = 2 := by
        change (P.image (finRotate (k + 3)).symm).card = 2
        rw [Finset.card_image_of_injective _ (Equiv.injective _), hPcard]
      have hP₂sub : P₂ ⊆ S₂ := by
        intro x hx
        simp only [P₂, Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simp only [S₂, Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro hlast
        apply hP0 y hy
        calc y = (finRotate (k + 3)) ((finRotate (k + 3)).symm y) :=
              (Equiv.apply_symm_apply _ y).symm
          _ = (finRotate (k + 3)) (Fin.last (k + 2)) := by rw [hlast]
          _ = 0 := finRotate_last
      have hQ₁card : (P.image σ₁).card = 2 := by
        rw [Finset.card_image_of_injective _ (Equiv.injective σ₁), hPcard]
      have hQ₂card : (P₂.image σ₂).card = 2 := by
        rw [Finset.card_image_of_injective _ (Equiv.injective σ₂), hP₂card]
      have himg : (fun i => π₁ i.castSucc) '' ((P.image σ₁ : Finset (Fin (k + 3))) :
            Set (Fin (k + 3))) =
          (fun j => π₂ j.castSucc) '' ((P₂.image σ₂ : Finset (Fin (k + 3))) :
            Set (Fin (k + 3))) := by
        rw [oaK_image_via (π := π₁) (π' := π₁') (σ := σ₁) rfl P,
          oaK_image_via (π := π₂) (π' := π₂') (σ := σ₂) hπ₂eq P₂]
        exact oaK_image_rot (π₁' := π₁') (π₂' := π₂') rfl (by simpa [S₁] using hPS)
      have hpairEq := hpair (P.image σ₁) (P₂.image σ₂) hQ₁card hQ₂card himg
      calc (normBlock E (k + 3) P).map κ₁'
          = (normBlock E (k + 3) (P.image σ₁)).map κ₁ :=
            oaK_map_normBlock_conj E (by omega : 3 ≤ k + 3) σ₁ P κ₁
        _ = (normBlock E (k + 3) (P₂.image σ₂)).map κ₂ := hpairEq
        _ = (normBlock E (k + 3) P₂).map κ₂' :=
            (oaK_map_normBlock_conj E (by omega : 3 ≤ k + 3) σ₂ P₂ κ₂).symm
        _ ≤ (normBlock E (k + 3) S₂).map κ₂' :=
            Subgroup.map_mono (normBlock_mono E (k + 3) hP₂sub)
    · rw [normBlock_eq_iSup_pairs E (k + 3) S₂ hcardS₂, Subgroup.map_iSup]
      refine iSup_le fun P₂ => ?_
      obtain ⟨P, hPS, hPcard⟩ := P₂
      have hPlast : ∀ j ∈ P, j ≠ Fin.last (k + 2) := by
        intro j hj
        have h := hPS hj
        simp only [S₂, Finset.mem_erase] at h
        exact h.1
      let P₁ : Finset (Fin (k + 3)) := P.image (finRotate (k + 3))
      have hP₁card : P₁.card = 2 := by
        change (P.image (finRotate (k + 3))).card = 2
        rw [Finset.card_image_of_injective _ (Equiv.injective _), hPcard]
      have hP₁sub : P₁ ⊆ S₁ := by
        intro x hx
        simp only [P₁, Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simp only [S₁, Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro hzero
        apply hPlast y hy
        have h := congrArg (finRotate (k + 3)).symm hzero
        rw [Equiv.symm_apply_apply, hsymm0] at h
        exact h
      have hQ₁card : (P₁.image σ₁).card = 2 := by
        rw [Finset.card_image_of_injective _ (Equiv.injective σ₁), hP₁card]
      have hQ₂card : (P.image σ₂).card = 2 := by
        rw [Finset.card_image_of_injective _ (Equiv.injective σ₂), hPcard]
      have himg : (fun i => π₁ i.castSucc) '' ((P₁.image σ₁ : Finset (Fin (k + 3))) :
            Set (Fin (k + 3))) =
          (fun j => π₂ j.castSucc) '' ((P.image σ₂ : Finset (Fin (k + 3))) :
            Set (Fin (k + 3))) := by
        rw [oaK_image_via (π := π₁) (π' := π₁') (σ := σ₁) rfl P₁,
          oaK_image_via (π := π₂) (π' := π₂') (σ := σ₂) hπ₂eq P]
        exact (oaK_image_rot' (π₁' := π₁') (π₂' := π₂') rfl (by simpa [S₂] using hPS)).symm
      have hpairEq := hpair (P₁.image σ₁) (P.image σ₂) hQ₁card hQ₂card himg
      calc (normBlock E (k + 3) P).map κ₂'
          = (normBlock E (k + 3) (P.image σ₂)).map κ₂ :=
            oaK_map_normBlock_conj E (by omega : 3 ≤ k + 3) σ₂ P κ₂
        _ = (normBlock E (k + 3) (P₁.image σ₁)).map κ₁ := hpairEq.symm
        _ = (normBlock E (k + 3) P₁).map κ₁' :=
            (oaK_map_normBlock_conj E (by omega : 3 ≤ k + 3) σ₁ P₁ κ₁).symm
        _ ≤ (normBlock E (k + 3) S₁).map κ₁' :=
            Subgroup.map_mono (normBlock_mono E (k + 3) hP₁sub)
  let ι₂ : normOmega E (k + 2) →* normOmega E (k + 3) := normOmegaCast E (by omega)
  let Pρ : normOmega E (k + 3) := normPerm E (by omega : 3 ≤ k + 3) (finRotate (k + 3))
  let ι₁ : normOmega E (k + 2) →* normOmega E (k + 3) :=
    (MulAut.conj Pρ).toMonoidHom.comp ι₂
  have hrange₂ : ι₂.range = normBlock E (k + 3) S₂ := by
    change (normOmegaCast E (by omega : k + 2 ≤ k + 3)).range = _
    simpa [S₂] using range_normOmegaCast_succ E (k + 2)
  have hrange₁ : ι₁.range = normBlock E (k + 3) S₁ := by
    change ((MulAut.conj Pρ).toMonoidHom.comp ι₂).range = _
    rw [MonoidHom.range_comp, hrange₂]
    change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj
      (normPerm E (by omega : 3 ≤ k + 3) (finRotate (k + 3)))) )
      (normBlock E (k + 3) S₂) = _
    rw [map_normBlock_normPerm, oaK_image_erase_finRotate]
  let φ₁ : normOmega E (k + 2) →* G := κ₁'.comp ι₁
  let φ₂ : normOmega E (k + 2) →* G := κ₂'.comp ι₂
  have hφ₁ : Function.Injective φ₁ :=
    h₁'.1.comp (MulEquiv.injective (MulAut.conj Pρ) |>.comp (normOmegaCast_injective E _))
  have hφ₂ : Function.Injective φ₂ := h₂'.1.comp (normOmegaCast_injective E _)
  have hrange₁' : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj Pρ)) ι₂.range =
      normBlock E (k + 3) S₁ := by
    rw [← MonoidHom.range_comp]
    exact hrange₁
  have hrangeφ : φ₁.range = φ₂.range := by
    calc φ₁.range = Subgroup.map κ₁' ι₁.range := MonoidHom.range_comp κ₁' ι₁
      _ = Subgroup.map κ₁'
          (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj Pρ)) ι₂.range) := by
          rw [show ι₁ = (MulEquiv.toMonoidHom (MulAut.conj Pρ)).comp ι₂ from rfl,
            MonoidHom.range_comp]
      _ = Subgroup.map κ₁' (normBlock E (k + 3) S₁) := by rw [hrange₁']
      _ = Subgroup.map κ₂' (normBlock E (k + 3) S₂) := hblock
      _ = Subgroup.map κ₂' ι₂.range := by rw [hrange₂]
      _ = φ₂.range := (MonoidHom.range_comp κ₂' ι₂).symm
  let α : MulAut (normOmega E (k + 2)) :=
    (MonoidHom.ofInjective hφ₁).trans
      ((MulEquiv.subgroupCongr hrangeφ).trans (MonoidHom.ofInjective hφ₂).symm)
  have hα : ∀ y, φ₂ (α y) = φ₁ y := by
    intro y
    have h := MonoidHom.apply_ofInjective_symm hφ₂
      ((MulEquiv.subgroupCongr hrangeφ) ((MonoidHom.ofInjective hφ₁) y))
    change φ₂ ((MonoidHom.ofInjective hφ₂).symm
      ((MulEquiv.subgroupCongr hrangeφ) ((MonoidHom.ofInjective hφ₁) y))) = φ₁ y
    rw [h, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  let τ₂ : (Fin (k + 2) → Multiplicative (ZMod 3)) →* normOmega E (k + 2) :=
    normPlaneTorus E (by omega : 2 ≤ k + 2) (by decide : 3 ∣ 2 ^ 1 + 1) χ
  let τ₃ : (Fin (k + 3) → Multiplicative (ZMod 3)) →* normOmega E (k + 3) :=
    normPlaneTorus E (by omega : 2 ≤ k + 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ
  have hfixτ : ∀ u : Fin (k + 2) → Multiplicative (ZMod 3), α (τ₂ u) = τ₂ u := by
    intro u
    let ũ : Fin (k + 3) → Multiplicative (ZMod 3) :=
      fun j => if hj : (j : ℕ) < k + 2 then u ⟨(j : ℕ), hj⟩ else 1
    have hι₂τ : ι₂ (τ₂ u) = τ₃ ũ := by
      change (normOmegaCast E (by omega : k + 2 ≤ k + 3))
        ((normPlaneTorus E (by omega : 2 ≤ k + 2) (by decide : 3 ∣ 2 ^ 1 + 1) χ) u) = _
      rw [normOmegaCast_normPlaneTorus]
    have hι₁τ : ι₁ (τ₂ u) = τ₃ (fun i => ũ ((finRotate (k + 3))⁻¹ i)) := by
      change (MulAut.conj Pρ) (ι₂ (τ₂ u)) = _
      rw [hι₂τ]
      change Pρ * τ₃ ũ * Pρ⁻¹ = _
      rw [normPerm_conj_normPlaneTorus]
    have hb : κ₁' (τ₃ (fun i => ũ ((finRotate (k + 3))⁻¹ i))) = κ₂' (τ₃ ũ) := by
      let b₁ : ↥Bs := ⟨κ₁' (τ₃ (fun i => ũ ((finRotate (k + 3))⁻¹ i))),
        h₁'.normPlaneTorus_mem_Bs (by omega : 2 ≤ k + 3) hSC
          (fun i => ũ ((finRotate (k + 3))⁻¹ i))⟩
      let b₂ : ↥Bs := ⟨κ₂' (τ₃ ũ),
        h₂'.normPlaneTorus_mem_Bs (by omega : 2 ≤ k + 3) hSC ũ⟩
      have hb_eq : b₁ = b₂ := by
        apply eta.injective
        funext c
        obtain ⟨x, rfl⟩ : ∃ x : Fin (k + 4), π₁' x = c :=
          ⟨π₁'.symm c, π₁'.apply_symm_apply c⟩
        rcases Fin.eq_castSucc_or_eq_last x with ⟨y, rfl⟩ | hlast
        · by_cases hy0 : y = 0
          · subst y
            have hc : π₁' (Fin.castSucc (0 : Fin (k + 3))) = i1 := by
              rw [show Fin.castSucc (0 : Fin (k + 3)) = (0 : Fin (k + 4)) from rfl,
                hπ₁'_zero]
            have hb₂coord : eta b₂ i1 = 1 := by
              have hb₂X : (b₂ : G) ∈ X₂ := by
                rw [← h₂'.2.1]
                exact ⟨τ₃ ũ, rfl⟩
              have h := hX₂ b₂ hb₂X
              simpa using h
            have hb₁coord : eta b₁ i1 = 1 := by
              have hcoord := h₁'.coords_normPlaneTorus (by omega : 2 ≤ k + 3) hSC
                (fun i => ũ ((finRotate (k + 3))⁻¹ i)) (0 : Fin (k + 3))
              rw [hc] at hcoord
              rw [hcoord]
              have hsymm0 : (finRotate (k + 3)).symm (0 : Fin (k + 3)) =
                  Fin.last (k + 2) := by
                rw [Equiv.symm_apply_eq]
                exact finRotate_last.symm
              change ũ ((finRotate (k + 3)).symm 0) = 1
              rw [hsymm0]
              simp [ũ]
            rw [hc, hb₁coord, hb₂coord]
          · have hyne : (finRotate (k + 3)).symm y ≠ Fin.last (k + 2) := by
              intro hlast'
              apply hy0
              calc y = (finRotate (k + 3)) ((finRotate (k + 3)).symm y) :=
                    (Equiv.apply_symm_apply _ y).symm
                _ = (finRotate (k + 3)) (Fin.last (k + 2)) := by rw [hlast']
                _ = 0 := finRotate_last
            have hb₁coord := h₁'.coords_normPlaneTorus (by omega : 2 ≤ k + 3) hSC
              (fun i => ũ ((finRotate (k + 3))⁻¹ i)) y
            have hb₂coord := h₂'.coords_normPlaneTorus (by omega : 2 ≤ k + 3) hSC
              ũ ((finRotate (k + 3)).symm y)
            calc eta b₁ (π₁' (Fin.castSucc y))
                = ũ ((finRotate (k + 3))⁻¹ y) := hb₁coord
              _ = eta b₂ (π₂' (Fin.castSucc ((finRotate (k + 3)).symm y))) :=
                    hb₂coord.symm
              _ = eta b₂ (π₁' (Fin.castSucc y)) := by
                  rw [oaK_pi₂'_castSucc_of_ne_last rfl hyne, Equiv.apply_symm_apply]
        · subst hlast
          have hb₁coord : eta b₁ i0 = 1 := by
            have hb₁X : (b₁ : G) ∈ X₁ := by
              rw [← h₁'.2.1]
              exact ⟨τ₃ (fun i => ũ ((finRotate (k + 3))⁻¹ i)), rfl⟩
            exact hX₁ b₁ hb₁X
          have hb₂coord : eta b₂ i0 = 1 := by
            have hc : i0 = π₂' (Fin.castSucc (Fin.last (k + 2))) := by
              rw [oaK_pi₂'_castSucc_last rfl]
              exact hπ₁'_last.symm
            rw [hc]
            have hcoord := h₂'.coords_normPlaneTorus (by omega : 2 ≤ k + 3) hSC ũ
              (Fin.last (k + 2))
            rw [hcoord]
            simp [ũ]
          rw [hπ₁'_last, hb₁coord, hb₂coord]
      exact congrArg Subtype.val hb_eq
    have hφeq : φ₁ (τ₂ u) = φ₂ (τ₂ u) := by
      change κ₁' (ι₁ (τ₂ u)) = κ₂' (ι₂ (τ₂ u))
      rw [hι₁τ, hι₂τ]
      exact hb
    exact hφ₂ ((hα (τ₂ u)).trans hφeq)
  obtain ⟨g, hg, hgα⟩ := OrthAnchor.exists_orthogonal_conj_of_mulAut E
    (OrthAnchor.card_eq_two_of_quadExt E) (by omega : 2 ≤ k + 2) α
  have hgcomm : ∀ u : Fin (k + 2) → Multiplicative (ZMod 3),
      g * (((τ₂ u : normOmega E (k + 2)) :
        ((F × F) × (Fin (k + 2) → K)) ≃ₗ[F] ((F × F) × (Fin (k + 2) → K)))) =
      (((τ₂ u : normOmega E (k + 2)) :
        ((F × F) × (Fin (k + 2) → K)) ≃ₗ[F] ((F × F) × (Fin (k + 2) → K)))) * g := by
    intro u
    have h := hgα (τ₂ u)
    rw [hfixτ u] at h
    calc g * ((τ₂ u : normOmega E (k + 2)) :
          ((F × F) × (Fin (k + 2) → K)) ≃ₗ[F] ((F × F) × (Fin (k + 2) → K))) =
        (g * ((τ₂ u : normOmega E (k + 2)) :
          ((F × F) × (Fin (k + 2) → K)) ≃ₗ[F] ((F × F) × (Fin (k + 2) → K))) * g⁻¹) * g := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = ((τ₂ u : normOmega E (k + 2)) :
          ((F × F) × (Fin (k + 2) → K)) ≃ₗ[F] ((F × F) × (Fin (k + 2) → K))) * g := by
          rw [← h]
  have hgT : ∀ (a : Fin (k + 2) → Multiplicative (ZMod 3))
      (v : (F × F) × (Fin (k + 2) → K)),
      g (v.1, fun i => (χ (a i) : K) * v.2 i) =
        ((g v).1, fun i => (χ (a i) : K) * (g v).2 i) := by
    intro a v
    have hcomm := hgcomm a
    have h1 : (((τ₂ a : normOmega E (k + 2)) :
        ((F × F) × (Fin (k + 2) → K)) ≃ₗ[F] ((F × F) × (Fin (k + 2) → K)))) v =
        (v.1, fun i => (χ (a i) : K) * v.2 i) :=
      normPlaneTorus_apply E (by omega : 2 ≤ k + 2) (by decide : 3 ∣ 2 ^ 1 + 1) χ a v
    have h2 : g ((((τ₂ a : normOmega E (k + 2)) :
        ((F × F) × (Fin (k + 2) → K)) ≃ₗ[F] ((F × F) × (Fin (k + 2) → K)))) v) =
        (((τ₂ a : normOmega E (k + 2)) :
        ((F × F) × (Fin (k + 2) → K)) ≃ₗ[F] ((F × F) × (Fin (k + 2) → K)))) (g v) := by
      have h := congrArg (fun e : ((F × F) × (Fin (k + 2) → K)) ≃ₗ[F]
          ((F × F) × (Fin (k + 2) → K)) => e v) hcomm
      simpa [LinearEquiv.mul_apply] using h
    rw [← h1, h2, normPlaneTorus_apply]
  let ĝ : ((F × F) × (Fin (k + 3) → K)) ≃ₗ[F] ((F × F) × (Fin (k + 3) → K)) :=
    castEquiv (by omega : k + 2 ≤ k + 3) g
  have hĝ : ĝ ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E (k + 3)) :=
    castEquiv_mem_orthogonalGroup E (by omega : k + 2 ≤ k + 3) hg
  have hĝT := castEquiv_planeDiag_comm (by omega : k + 2 ≤ k + 3) χ hgT
  let κ₂'' : normOmega E (k + 3) →* G := κ₂'.comp (normOmegaConj E hĝ).toMonoidHom
  have h₂'' : GGSecFiveBPermOmKFrame E Bs X₂ eta π₂' κ₂'' χ :=
    h₂'.comp_normOmegaConj hĝ hĝT
  have hpoint : ∀ y : normOmega E (k + 2), κ₁' (ι₁ y) = κ₂'' (ι₂ y) := by
    intro y
    have h₁eq : κ₂'' (ι₂ y) = κ₂' (ι₂ (normOmegaConj E hg y)) := by
      change κ₂' ((normOmegaConj E hĝ)
        ((normOmegaCast E (by omega : k + 2 ≤ k + 3)) y)) =
        κ₂' ((normOmegaCast E (by omega : k + 2 ≤ k + 3)) (normOmegaConj E hg y))
      rw [normOmegaConj_castEquiv_normOmegaCast]
    have h₂eq : normOmegaConj E hg y = α y := by
      apply Subtype.ext
      rw [normOmegaConj_apply E hg y, hgα y]
    calc κ₁' (ι₁ y) = φ₁ y := rfl
      _ = φ₂ (α y) := (hα y).symm
      _ = κ₂' (ι₂ (α y)) := rfl
      _ = κ₂' (ι₂ (normOmegaConj E hg y)) := by rw [h₂eq]
      _ = κ₂'' (ι₂ y) := h₁eq.symm
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
    have : FiniteDimensional F K := finiteDimensional_of_quadExt E
    have hKF : Nat.card K = Nat.card F ^ 2 := by
      rw [Module.natCard_eq_pow_finrank (K := F) (V := K), E.finrank_eq]
    have hKcard : Nat.card K = 2 ^ (2 * 1) := by
      rw [hKF, OrthAnchor.card_eq_two_of_quadExt E]
    let hUF : UnitaryFieldData 2 1 K := ⟨by norm_num, by norm_num, hKcard⟩
    let y : normOmega E (k + 2) :=
      uniEmb E hUF (k + 2) (CFSG.SeitzReduction.UnitaryPilot.permSUHom hUF σ')
    have hX : normPerm E (by omega : 3 ≤ k + 3)
        ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) σ') =
        ι₂ y := by
      have hσ : ∀ i : Fin (k + 2),
          (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) σ'
            (Fin.castSucc i) = Fin.castSucc (σ' i) := by
        intro i
        rw [Equiv.Perm.viaEmbeddingHom_apply, ← Fin.castSuccEmb_apply i,
          Equiv.Perm.viaEmbedding_apply, Fin.castSuccEmb_apply]
      have h := normPerm_eq_normOmegaCast E hUF (by omega : 2 ≤ k + 2) σ'
        ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3))) σ') hσ
      simpa [ι₂, y, hUF] using h
    rw [hX]
    exact hpoint y
  exact ⟨π₁', π₂', κ₁', κ₂'', h₁', h₂'', hπ₁'_last, hπ₂'_last, rfl, hpoint, hperm⟩

theorem GGSecFiveBPermOmKFrame.exists_overlap_calibration_of_component {G : Type} [Group G]
    [Finite G] {Bs X₁ X₂ : Subgroup G} {y₁ y₂ : G} {n k : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {χ : Multiplicative (ZMod 3) →* Kˣ}
    {π₁ π₂ : Fin (k + 4) ≃ Fin n} {κ₁ κ₂ : normOmega E (k + 3) →* G}
    (h₁ : GGSecFiveBPermOmKFrame E Bs X₁ eta π₁ κ₁ χ)
    (h₂ : GGSecFiveBPermOmKFrame E Bs X₂ eta π₂ κ₂ χ)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
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
  refine h₁.exists_overlap_calibration h₂ hSC hX₁ hX₂ hne fun P₁ P₂ hP₁ hP₂ himg => ?_
  rw [← h₁.blockComm_eq_map_normBlock hSC hy₁ hX₁c (by omega) (by omega),
    ← h₂.blockComm_eq_map_normBlock hSC hy₂ hX₂c (by omega) (by omega), himg]

end CFSG.StandardType

end
