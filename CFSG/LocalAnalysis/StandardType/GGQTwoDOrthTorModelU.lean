module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorModelUAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorSU

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open TauCeti.QuadraticMap CFSG.Assembly.LowTwoRank
open Matrix

section ModelU

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

theorem torStdM_P₁_le_win (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2)
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1) :
    torP₁ (Qn E (m + 1)) (torStdM ζ m a) ≤
      (qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range := by
  intro x hx
  have hxU : x ∈ (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)).range :=
    plh_commutator_le_range_suEndN E hF hζ m a ha hx
  have hxE1 : x ∈ torE₁ (Qn E (m + 1)) (torStdM ζ m a) :=
    Subgroup.commutator_le_self _ hx
  have hxfix : x ∈ torFix (torV₀ (torStdM ζ m a)) := hxE1.1.2
  have hV₀ : torV₀ (torStdM ζ m a) = torStdV₀ (F := F) m a := torV₀_torStdM hζ m a
  obtain ⟨s, rfl⟩ := hxU
  refine plh_suEndN_mem_win_of_fix m a ha (fun v hv => hxfix v (by rw [hV₀]; exact hv))

private theorem plh_window_le_torE₁ (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ)
    (ha : a ≤ m + 1) :
    (qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range ≤
      torE₁ (Qn E (m + 1)) (torStdM ζ m a) := by
  intro g hg
  obtain ⟨S, rfl⟩ := hg
  have hb' : a + (m + 1 - a) ≤ m + 1 := by omega
  have hV₀ : torV₀ (torStdM ζ m a) = torStdV₀ (F := F) m a := torV₀_torStdM hζ m a
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact suEndN_mem_orthogonalGroup E (m + 1) (blockEmb K 2 1 (m + 1) (m + 1 - a) a hb' S)
  · intro v hv
    rw [hV₀] at hv
    funext i
    by_cases hi : i.val < a
    · rw [plh_qtwoStdWin_apply_not_mem m a (m + 1 - a) hb' S v i (by omega)]
    · have hix : i = blockIdx a hb' ⟨i.val - a, by omega⟩ := by
        ext; simp only [blockIdx_val]; omega
      rw [hix, plh_qtwoStdWin_apply_window]
      have hzero : (fun y : Fin (m + 1 - a) => v (blockIdx a hb' y)) = 0 := by
        funext y; exact hv (blockIdx a hb' y) (by simp only [blockIdx_val]; omega)
      rw [hzero, Matrix.mulVec_zero]
      exact (hv (blockIdx a hb' ⟨i.val - a, by omega⟩)
        (by simp only [blockIdx_val]; omega)).symm
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro d hd
    rw [Set.mem_singleton_iff] at hd
    subst hd
    have ht₀ : torStdM ζ m a =
        diagHom F (unitaryInvolution K 2 1) (m + 1) (fun i => if i.val < a then 1 else ζ) := rfl
    rw [ht₀]
    exact plh_diagHom_comm_qtwoStdWin m a (m + 1 - a) hb'
      (fun i => if i.val < a then 1 else ζ)
      (fun p q hp1 hp2 hq1 hq2 => by rw [if_neg (by omega), if_neg (by omega)]) S

private theorem plh_window_isPerfect (hK : Nat.card K = 4) (m a : ℕ) (hb : 4 ≤ m + 1 - a) :
    ⁅(qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range,
      (qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range⁆ =
      (qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range := by
  obtain ⟨e⟩ := qtwoStdWin_range_equiv_statedSU (F := F) (K := K) hK m a (m + 1 - a) (by omega)
  have hq := torSU_isQuasisimple_label (E := K) hK hb e
  haveI : Group.IsPerfect ↥(qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range :=
    hq.1.1
  exact Subgroup.commutator_eq_self

theorem torStdM_win_le_P₁ (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2)
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (hb : 4 ≤ m + 1 - a) :
    (qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range ≤
      torP₁ (Qn E (m + 1)) (torStdM ζ m a) := by
  have hK : Nat.card K = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), hF, E.finrank_eq]
    norm_num
  have hWE1 := plh_window_le_torE₁ E hF hζ m a ha
  have hperf := plh_window_isPerfect (F := F) (K := K) hK m a hb
  calc (qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range
      = ⁅(qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range,
          (qtwoStdWin (F := F) (K := K) m a (m + 1 - a) (by omega)).range⁆ := hperf.symm
    _ ≤ ⁅torE₁ (Qn E (m + 1)) (torStdM ζ m a),
          torE₁ (Qn E (m + 1)) (torStdM ζ m a)⁆ := Subgroup.commutator_mono hWE1 hWE1
    _ = torP₁ (Qn E (m + 1)) (torStdM ζ m a) := rfl

end ModelU

end CFSG.StandardType.QTwo

end
