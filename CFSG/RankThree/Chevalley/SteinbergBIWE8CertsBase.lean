
module

public import CFSG.RankThree.Chevalley.SteinbergBIWE8Reps

@[expose] public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.WE8.Native

theorem toL_vecOf {l : List ℤ} (hl : l.length = 8) : toL (vecOf l) = l := by
  change List.ofFn (vecOf l) = l
  refine List.ext_getElem (by rw [List.length_ofFn, hl]; rfl) fun k h1 h2 => ?_
  rw [List.getElem_ofFn]
  exact List.getD_eq_getElem _ _ h2

theorem frameData_length : ∀ i < 9, ∀ l ∈ frameData.getD i [], l.length = 8 := by
  decide +kernel

theorem map_toL_frame {i : ℕ} (hi : i < 9) : (frame i).map toL = frameData.getD i [] := by
  rw [frame, List.map_map]
  conv_rhs => rw [← List.map_id (frameData.getD i [])]
  exact List.map_congr_left fun l hl => toL_vecOf (frameData_length i hi l hl)

theorem frameData_mem : ∀ i < 9, ∀ l ∈ frameData.getD i [], l ∈ rootsL := by
  decide +kernel

theorem frameData_pairwise : ∀ i < 9, (frameData.getD i []).Pairwise fun u v => ip u v = 0 := by
  decide +kernel

theorem frame_isRoot {i : ℕ} (hi : i < 9) : ∀ β ∈ frame i, IsRoot .E8 β := by
  intro β hβ
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hβ
  rw [← mem_rootsL, toL_vecOf (frameData_length i hi l hl)]
  exact frameData_mem i hi l hl

theorem frame_pairwise {i : ℕ} (hi : i < 9) : (frame i).Pairwise fun u v => iform u v = 0 := by
  rw [frame, List.pairwise_map]
  refine (frameData_pairwise i hi).imp_of_mem fun {u v} hu hv h => ?_
  rw [← ip_toL, toL_vecOf (frameData_length i hi u hu), toL_vecOf (frameData_length i hi v hv)]
  exact h

theorem code_rep {i : ℕ} (hi : i < 9) : code (rep i) = frameCode (frameData.getD i []) := by
  rw [rep, code_frameProd _ (frame_isRoot hi), map_toL_frame hi]

@[expose] def negCounts : List ℕ := [2, 4, 6, 8, 24, 26, 60, 126, 240]

theorem negCount_frameCode : ∀ i < 9,
    WE8.Native.negCount (frameCode (frameData.getD i [])) = negCounts.getD i 0 := by
  decide +kernel

theorem ncard_neg_rep {i : ℕ} (hi : i < 9) :
    {α : L8 | IsRoot .E8 α ∧ rep i • α = -α}.ncard = negCounts.getD i 0 := by
  rw [← negCount_code, code_rep hi, negCount_frameCode i hi]

abbrev z : W8 := rep 8

theorem frameCode_eight :
    frameCode (frameData.getD 8 []) = negI (List.ofFn fun i : Fin 8 => rootIdx (basisV i)) := by
  decide +kernel

theorem z_smul (v : L8) : z • v = -v := by
  have hc : code z = negI (code 1) := by
    rw [code_rep (by decide), frameCode_eight, code_one]
    rfl
  have hcol : ∀ i : Fin Tag.E8.rank, z • eb i = -eb i := by
    intro i
    have hlen : (i : ℕ) < (code 1).length := by rw [length_code]; exact i.2
    have e : (code z).getD i 0 = negT.getD ((code 1).getD i 0) 0 := by
      rw [hc, negI, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlen),
        List.getElem_map, List.getD_eq_getElem _ _ hlen]
    apply toL_injective
    rw [← col_code z i, e, negT_getD (getD_code_lt 1 i), col_code, one_smul, vneg_toL,
      getD_rootIdx (IsRoot.neg (isRoot_single _ i))]
  rw [smul_eq_sum_smul_single z v]
  simp only [hcol, smul_neg, Finset.sum_neg_distrib]
  congr 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem y0WordF_map : y0WordF.map Fin.val = y0Word := by
  decide +kernel

theorem code_y0 : code y0 = wordCode y0Word := by
  rw [y0, code_wordProd, y0WordF_map]

theorem mulI_y0 : mulI (wordCode y0Word) (wordCode y0Word) = frameCode (frameData.getD 8 []) := by
  decide +kernel

theorem y0_mul_y0 : y0 * y0 = z :=
  code_injective (by rw [code_mul, code_y0, mulI_y0, code_rep (by decide)])

end CFSG.RankThree.Chevalley.WeylE8
