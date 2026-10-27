module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23cNine.Generic

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLTorusForm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLFlagMat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine

open CFSG.Open CFSG.Quasithin
open Matrix
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
open CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

private theorem slU_mulVec_e0 {k : ℕ} [NeZero k] {K : Type} [Field K]
    {g : ↥(StatedSL k K)} (hg : g ∈ slU k K) :
    slMat g *ᵥ (Pi.single 0 (1 : K) : Fin k → K) = Pi.single 0 (1 : K) := by
  rw [mem_slU_iff] at hg
  ext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  by_cases hi : i = 0
  · subst hi
    rw [Pi.single_eq_same, hg.2 0]
  · rw [Pi.single_eq_of_ne hi]
    exact hg.1 i 0 ((Fin.pos_iff_ne_zero' i).mpr hi)

private theorem sl_conj_eq_one_of_mem_vecStab {k : ℕ} [NeZero k] {K : Type} [Field K] [Finite K]
    [CharP K 2] (hk : 2 ≤ k) {t : ↥(StatedSL k K)}
    (htα : t ∈ Hinf (slQAlpha k K))
    (ht0 : t ∈ KTabC.vecStab (StatedSL k K).subtype (Pi.single 0 1 : Fin k → K))
    (hodd : Odd (orderOf t)) : t = 1 := by
  have htQ0 : t ∈ slQZero k K :=
    KTabD.mem_lineStab.mpr ⟨1, by
      rw [one_smul]
      exact KTabC.mem_vecStab.mp ht0⟩
  obtain ⟨s, hsU, c, -, -, hdiag⟩ := exists_conj_slTorusDiag hk ⟨htα, htQ0⟩ hodd
  have hsV : s ∈ KTabC.vecStab (StatedSL k K).subtype (Pi.single 0 1 : Fin k → K) :=
    KTabC.mem_vecStab.mpr (slU_mulVec_e0 hsU)
  have hconjmem : s * t * s⁻¹ ∈
      KTabC.vecStab (StatedSL k K).subtype (Pi.single 0 1 : Fin k → K) :=
    mul_mem (mul_mem hsV ht0) (inv_mem hsV)
  have hfix : Matrix.diagonal (slTorusDiag k c) *ᵥ (Pi.single 0 1 : Fin k → K) =
      Pi.single 0 1 := by
    rw [← hdiag]
    exact KTabC.mem_vecStab.mp hconjmem
  have hc1 : c = 1 := by
    have h := congrFun hfix 0
    rw [Matrix.diagonal_mulVec_single] at h
    have h0 : slTorusDiag k c 0 = 1 := by simpa using h
    simpa [slTorusDiag] using h0
  have hdiag1 : slMat (s * t * s⁻¹) = 1 := by
    rw [hdiag, hc1]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      simp [slTorusDiag]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hconj1 : s * t * s⁻¹ = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa [slMat] using hdiag1
  calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
    _ = 1 := by rw [hconj1]; group

theorem sl_eq_one_of_mem_hinf_vecStab {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    [NeZero k] (hk : 2 ≤ k) {t : ↥(StatedSL k K)}
    (ht : t ∈ Hinf (slQAlpha k K) ⊓
      KTabC.vecStab (StatedSL k K).subtype (Pi.single 0 1 : Fin k → K))
    (hodd : Odd (orderOf t)) : t = 1 :=
  sl_conj_eq_one_of_mem_vecStab hk ht.1 ht.2 hodd

theorem kTab23cNineAt_of_realizes_sl {W : Type} [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) {k : ℕ} [NeZero k] (hk : 2 ≤ k) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hreal : (FFModel.nat (StatedSL k K)).Realizes H ⊤ ⊥) : KTab23cNineAt W H := by
  have hline : KTabC.SylowFixedLine (StatedSL k K) (Pi.single 0 1) :=
    KTabD.sylowFixedLine_statedSL (K := K) (d := k) hk
  have he0 : (Pi.single 0 1 : Fin k → K) ≠ 0 :=
    Pi.single_ne_zero_iff.mpr (one_ne_zero : (1 : K) ≠ 0)
  refine kTab23cNineAt_of_model H (slU k K) (slQAlpha k K) (slQZero k K)
    (KTabC.vecStab (StatedSL k K).subtype (Pi.single 0 1)) ?_
    (isParabolicTwo_slQAlpha (k := k) (K := K) (by omega)) (slU_le_slQAlpha k K)
    (not_slQAlpha_le_slQZero hk)
    (fun P hP hU hnot => slQAlpha_le_of_parabolic hk hP hU hnot) ?_
  · intro S
    obtain ⟨U, hU⟩ := exists_sylow_slU (k := k) (K := K) (by omega)
    obtain ⟨φ, h1, h2, h3⟩ := exists_mulEquiv_pointStab_fixSub_eq_map_sylow hreal he0 hline U
      (hU ▸ slU_le_slQZero) S
    exact ⟨φ, hU ▸ h1, h2, h3⟩
  · exact fun t ht hodd => sl_eq_one_of_mem_hinf_vecStab hk ht hodd

theorem kTab23cNineAt_sl {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W))
    {n k : ℕ} (hk : 2 ≤ k) (h : CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ k n) :
    KTab23cNineAt W H := by
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hn : 1 ≤ n := by
    have hcard : 1 < Nat.card K := Finite.one_lt_card
    rw [hKcard] at hcard
    by_contra hn
    have h0 : n = 0 := by omega
    subst h0
    norm_num at hcard
  haveI : CharP K 2 := uc22p22d_charP_two hn hKcard
  haveI : NeZero k := ⟨by omega⟩
  exact kTab23cNineAt_of_realizes_sl H (k := k) (K := K) hk hreal

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine
