module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XNonAbPiece
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_inf_sup_of_nonabelian_chief (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {X Y Z M U W : Subgroup G} (hKG : CFSG.Open.IsKGroup ↥(U ⊔ X)) (hZX : Z ≤ X)
    (hZ3 : Nat.card Z = 3) (hXY : X ≤ Y) (hYX : Y ≤ normalizer (X : Set G)) (hYM : Y ≤ M)
    (hCZ : centralizer (Z : Set G) ≤ M) (hXperf : ⁅X, X⁆ = X)
    (hXgen : ∀ B : Subgroup G, B ≤ X → X ≤ normalizer (B : Set G) → Z ≤ B → B = X)
    (hU3 : ¬ 3 ∣ Nat.card U) (hUY : Y ≤ normalizer (U : Set G)) (hWle : W ≤ U)
    (hWU : U ≤ normalizer (W : Set G)) (hWY : Y ≤ normalizer (W : Set G))
    (hWmax : ∀ X' : Subgroup G, W ≤ X' → X' ≤ U → U ≤ normalizer (X' : Set G) →
      Y ≤ normalizer (X' : Set G) → X' ≠ U → X' = W)
    (hcomm : ¬ ⁅U, U⁆ ≤ W) : U ≤ (U ⊓ M) ⊔ W := by
  classical
  obtain ⟨U₁, hWU₁, hU₁U, hUnU₁, hXnU₁, hcommU₁, hXmax, hgen⟩ :=
    exists_xInvariant_piece_of_nonabelian_chief hXY hYX hUY hWle hWU hWY hWmax hcomm
  have hKG' : CFSG.Open.IsKGroup ↥(U₁ ⊔ X) :=
    CFSG.Open.IsKGroup.of_le hKG (sup_le_sup_right hU₁U X)
  have hU3' : ¬ 3 ∣ Nat.card U₁ := fun h => hU3 (h.trans (Subgroup.card_dvd_of_le hU₁U))
  have hXW : X ≤ normalizer (W : Set G) := hXY.trans hWY
  have hmain : U₁ ≤ (U₁ ⊓ M) ⊔ W :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F09.le_inf_sup_of_not_commutator_le hSch
      hKG' hZX hZ3 (hXY.trans hYM) hCZ hXperf hXgen hU3' hXnU₁ hWU₁
      (hU₁U.trans hWU) hXW hXmax hcommU₁
  have hconj : ∀ y : ↥Y, U₁.map (MulAut.conj (y : G)).toMonoidHom ≤ (U ⊓ M) ⊔ W := by
    intro y
    have hyM : (y : G) ∈ M := hYM y.2
    have hyU : (y : G) ∈ normalizer (U : Set G) := hUY y.2
    have hyW : (y : G) ∈ normalizer (W : Set G) := hWY y.2
    have hmapU : (U₁ ⊓ M).map (MulAut.conj (y : G)).toMonoidHom ≤ U ⊓ M := by
      rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      obtain ⟨hxU₁, hxM⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_comap]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h := (Subgroup.mem_normalizer_iff.mp hyU x).mp (hU₁U hxU₁)
        simpa [MulAut.conj_apply] using h
      · have h : (y : G) * x * (y : G)⁻¹ ∈ M :=
          M.mul_mem (M.mul_mem hyM hxM) (M.inv_mem hyM)
        simpa [MulAut.conj_apply] using h
    have hmapW : W.map (MulAut.conj (y : G)).toMonoidHom ≤ (U ⊓ M) ⊔ W := by
      rw [Subgroup.map_le_iff_le_comap]
      intro w hw
      rw [Subgroup.mem_comap]
      have h : (y : G) * w * (y : G)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp hyW w).mp hw
      simpa [MulAut.conj_apply] using (le_sup_right : W ≤ (U ⊓ M) ⊔ W) h
    calc U₁.map (MulAut.conj (y : G)).toMonoidHom
        ≤ (((U₁ ⊓ M) ⊔ W).map (MulAut.conj (y : G)).toMonoidHom) :=
          Subgroup.map_mono hmain
      _ = ((U₁ ⊓ M).map (MulAut.conj (y : G)).toMonoidHom) ⊔
            (W.map (MulAut.conj (y : G)).toMonoidHom) :=
          Subgroup.map_sup (U₁ ⊓ M) W _
      _ ≤ (U ⊓ M) ⊔ W := sup_le (hmapU.trans le_sup_left) hmapW
  exact hgen.trans (iSup_le hconj)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
