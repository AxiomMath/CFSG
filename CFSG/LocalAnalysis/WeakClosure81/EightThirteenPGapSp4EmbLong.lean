module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4EmbDef
import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4Tis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.Assembly.LowTwoRank (StatedSp)
open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular mem_unitriangular)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent torus_le_borelSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (tau sym2 sym2_transpose coe_tau)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  (lam sl2Diag sl2DiagElt torusHom lam_sl2Diag lam_injective coe_lam pairMat statedSp_ext
    torusHom_mem_torus)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (normalizer_unipotent)

private def wcgapel_slUnitri {F : Type} [Field F] (b : F) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, b; 0, 1], by rw [Matrix.det_fin_two_of]; simp⟩

private lemma wcgapel_slUnitri_mem {F : Type} [Field F] (b : F) :
    wcgapel_slUnitri b ∈ unitriangular 2 F := by
  rw [mem_unitriangular]
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [wcgapel_slUnitri]
  · intro i
    fin_cases i <;> simp [wcgapel_slUnitri]

private lemma wcgapel_lam_slUnitri {F : Type} [Field F] (b : F) :
    lam (r := 2) (k := F) 0 (wcgapel_slUnitri b) = sp4Z b 0 := by
  apply statedSp_ext
  rw [coe_lam, sp4Z, coe_tau]
  ext i j
  rcases i with a | a <;> rcases j with c | c <;> fin_cases a <;> fin_cases c <;>
    simp [wcgapel_slUnitri, pairMat, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, sym2]

private lemma wcgapel_eq_slUnitri {F : Type} [Field F]
    {u : Matrix.SpecialLinearGroup (Fin 2) F} (hu : u ∈ unitriangular 2 F) :
    u = wcgapel_slUnitri ((u : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  obtain ⟨hlo, hdiag⟩ := mem_unitriangular.mp hu
  ext i j
  fin_cases i <;> fin_cases j
  · simp [wcgapel_slUnitri, hdiag]
  · rfl
  · simpa [wcgapel_slUnitri] using hlo 1 0 (by decide)
  · simp [wcgapel_slUnitri, hdiag]

private lemma wcgapel_lam_unitri {F : Type} [Field F]
    {u : Matrix.SpecialLinearGroup (Fin 2) F} (hu : u ∈ unitriangular 2 F) :
    lam (r := 2) (k := F) 0 u = sp4Z ((u : Matrix (Fin 2) (Fin 2) F) 0 1) 0 := by
  rw [wcgapel_eq_slUnitri hu]
  exact wcgapel_lam_slUnitri _

private lemma wcgapel_slTwoDiag_eq {F : Type} [Field F] (l : Fˣ) :
    slTwoDiag l = sl2Diag (k := F) l := by
  refine Subtype.ext ?_
  simp [slTwoDiag, sl2Diag, sl2DiagElt]

private lemma wcgapel_torus_mem_normalizer {F : Type} [Field F] (l : Fˣ) :
    lam (r := 2) (k := F) 0 (slTwoDiag l) ∈
      normalizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)) := by
  rw [wcgapel_slTwoDiag_eq l, lam_sl2Diag (r := 2) (k := F) 0 l,
    normalizer_unipotent (r := 2) (K := F)]
  exact torus_le_borelSubgroup (torusHom_mem_torus (Pi.mulSingle 0 l))

private lemma wcgapel_map_eq_of_hA {F : Type} [Field F] {A : Subgroup (StatedSp 2 F)}
    (hA : ∀ g, g ∈ A ↔ ∃ b : F, g = sp4Z b 0) :
    A = (unitriangular 2 F).map (lam (r := 2) (k := F) 0) := by
  ext g
  rw [hA g]
  constructor
  · rintro ⟨b, rfl⟩
    exact Subgroup.mem_map.mpr ⟨wcgapel_slUnitri b, wcgapel_slUnitri_mem b,
      wcgapel_lam_slUnitri b⟩
  · intro hg
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨(u : Matrix (Fin 2) (Fin 2) F) 0 1, wcgapel_lam_unitri hu⟩

theorem sp4_emb_long {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    {A : Subgroup (StatedSp 2 F)} (hA : ∀ g, g ∈ A ↔ ∃ b : F, g = sp4Z b 0) :
    Sp4Sl2Emb A := by
  refine ⟨lam (r := 2) (k := F) 0, lam_injective (r := 2) (k := F) 0,
    wcgapel_map_eq_of_hA hA, ?_⟩
  exact wcgapel_torus_mem_normalizer

end CFSG.LocalAnalysis.WeakClosure81

end
