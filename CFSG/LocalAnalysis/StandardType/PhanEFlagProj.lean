module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagGate
public import CFSG.LocalAnalysis.StandardType.PhanEGateMax
public import CFSG.LocalAnalysis.StandardType.PhanEFlagPart
import TauCeti.LinearAlgebra.Dimension.Sup
public import CFSG.LocalAnalysis.StandardType.PhanEFlagOpp

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] {n m : ℕ} {d : List ℕ}

private theorem q2cFPj_blockRev_eq (hd : IsCut (m + 1) d) :
    blockRev hd =
      longest (symCox m) (cutTypes m d) * longest (symCox m) Set.univ := by
  apply Equiv.ext
  intro k
  apply Fin.ext
  have hb := q2cFG_blkFin_lt hd k
  have hwin := q2cFG_blkFin_window hd k
  have hrev : ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) k).val = (m + 1) - (k.val + 1) :=
    rfl
  have hk₁ : d.getD (q2cFG_blkFin hd k) 0 ≤
      ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) k).val := by
    rw [hrev]; omega
  have hk₂ : ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) k).val <
      d.getD (q2cFG_blkFin hd k + 1) 0 := by
    rw [hrev]; omega
  have hdle : d.getD (q2cFG_blkFin hd k + 1) 0 ≤ m + 1 := q2cFPt_le_last hd hb
  have hdble : d.getD (q2cFG_blkFin hd k) 0 ≤ d.getD (q2cFG_blkFin hd k + 1) 0 :=
    le_of_lt (hd.strict _ hb)
  rw [blockRev_apply hd k hb hwin.1 hwin.2, Equiv.Perm.mul_apply, longest_symCox_univ,
    longest_cutTypes_apply (b := q2cFG_blkFin hd k) hd _ hb hk₁ hk₂, hrev]
  omega

theorem isMinimalCosetRep_blockRev (hd : IsCut (m + 1) d) :
    (symCox m).IsMinimalCosetRep (cutTypes m d) (blockRev hd)⁻¹ := by
  haveI : Finite ((symCox m).parabolic Set.univ) := Subtype.finite
  haveI : Finite ((symCox m).parabolic (cutTypes m d)) := Subtype.finite
  rw [(symCox m).isMinimalCosetRep_iff]
  intro i hi hdesc
  have hτ := q2cFPj_blockRev_eq hd
  have hu : (blockRev hd)⁻¹ =
      longest (symCox m) Set.univ * longest (symCox m) (cutTypes m d) := by
    rw [hτ, mul_inv_rev,
      (isLongest_longest (cs := symCox m) (cutTypes m d)).inv_eq,
      (isLongest_longest (cs := symCox m) Set.univ).inv_eq]
  have hstep : (symCox m).length
      (longest (symCox m) (cutTypes m d) * (symCox m).simple i) + 1 =
      (symCox m).length (longest (symCox m) (cutTypes m d)) := by
    have hdI := (isLongest_longest (cs := symCox m) (cutTypes m d)).isRightDescent hi
    simp only [CoxeterSystem.IsRightDescent] at hdI
    rcases (symCox m).length_mul_simple (longest (symCox m) (cutTypes m d)) i with h | h
    · omega
    · exact h
  have hlen_u : (symCox m).length ((blockRev hd)⁻¹) +
      (symCox m).length (longest (symCox m) (cutTypes m d)) =
      (symCox m).length (longest (symCox m) Set.univ) := by
    rw [hu]
    exact IsLongest.length_mul (isLongest_longest (cs := symCox m) Set.univ)
      (by rw [CoxeterSystem.parabolic_univ]; exact Subgroup.mem_top _)
  have hlen_us : (symCox m).length ((blockRev hd)⁻¹ * (symCox m).simple i) +
      (symCox m).length (longest (symCox m) (cutTypes m d) * (symCox m).simple i) =
      (symCox m).length (longest (symCox m) Set.univ) := by
    rw [hu, mul_assoc]
    exact IsLongest.length_mul (isLongest_longest (cs := symCox m) Set.univ)
      (by rw [CoxeterSystem.parabolic_univ]; exact Subgroup.mem_top _)
  simp only [CoxeterSystem.IsRightDescent] at hdesc
  omega

theorem resProj_eq_gateFlag (hd : IsCut (m + 1) d) {E x₀ : FlagK K (m + 1)}
    (hE : E ∈ farSet (m + 1) d) (hx₀ : x₀ ∈ refSet K (m + 1) d) :
    resProj (symCox m) (flagδ (K := K) m) (cutTypes m d) x₀ E = gateFlag hd hE := by
  have hB : IsWeylDistanceBuilding (symCox m) (flagδ (K := K) m) :=
    isWeylDistanceBuilding_flag (K := K) (m := m)
  have hmem : gateFlag hd hE ∈
      residue (symCox m) (flagδ (K := K) m) (cutTypes m d) x₀ := by
    rw [residue_cutTypes_eq hd hx₀]
    exact gateFlag_mem_refSet hd hE
  have hmin : (symCox m).IsMinimalCosetRep (cutTypes m d)
      (flagδ (K := K) m E (gateFlag hd hE)) := by
    rw [flagδ, hasPos_iff.mp (hasPos_gateFlag hd hE)]
    exact isMinimalCosetRep_blockRev hd
  exact resProj_eq hB (isProjection_of_gate hB hmem fun q hq =>
    (gate_of_isMinimalCosetRep hB hmem hmin hq).2)

theorem mem_farSet_of_opp (hd : IsCut n d) {E y : FlagK K n} (hy : y ∈ refSet K n d)
    (h : Opp E y) : E ∈ farSet n d := by
  intro i hi j hj
  have hc : d.getD i 0 ≤ n := q2cFPt_le_last hd hi
  have hyd : y.E (d.getD i 0) = Vsub n (d.getD i 0) := hy i hi
  have hop : E.E j ⊓ y.E (n - j) = ⊥ := h j hj
  by_cases hjc : j + d.getD i 0 ≤ n
  · have hle : Vsub n (d.getD i 0) ≤ y.E (n - j) := by
      rw [← hyd]
      exact y.mono (by omega)
    have hbot : E.E j ⊓ Vsub n (d.getD i 0) = ⊥ :=
      le_bot_iff.mp ((inf_le_inf (le_refl (E.E j)) hle).trans (le_of_eq hop))
    rw [hbot, finrank_bot]
    omega
  · have hnjc : n ≤ j + d.getD i 0 := le_of_lt (not_le.mp hjc)
    have hnj : n - j ≤ d.getD i 0 := by omega
    have hBsub : y.E (n - j) ≤ Vsub n (d.getD i 0) := by
      rw [← hyd]
      exact y.mono hnj
    have hAB : (E.E j ⊓ Vsub n (d.getD i 0)) ⊓ y.E (n - j) = ⊥ := by
      rw [inf_assoc, inf_eq_right.mpr hBsub, hop]
    have hub : finrank K ↥(E.E j ⊓ Vsub n (d.getD i 0)) ≤ j + d.getD i 0 - n := by
      have hle := TauCeti.finrank_add_finrank_le_of_inf_eq_bot (S := E.E j ⊓ Vsub n (d.getD i 0))
        (T := y.E (n - j)) (U := Vsub n (d.getD i 0)) inf_le_right hBsub hAB
      rw [y.dim (n - j) (by omega), finrank_Vsub hc] at hle
      omega
    have hlb : j + d.getD i 0 - n ≤ finrank K ↥(E.E j ⊓ Vsub n (d.getD i 0)) := by
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq (E.E j) (Vsub (K := K) n (d.getD i 0))
      have hsup_le : finrank K ↥(E.E j ⊔ Vsub n (d.getD i 0)) ≤ n := by
        calc finrank K ↥(E.E j ⊔ Vsub n (d.getD i 0)) ≤
              finrank K (⊤ : Submodule K (Fin n → K)) := Submodule.finrank_mono le_top
          _ = n := by rw [finrank_top, Module.finrank_fin_fun]
      rw [E.dim j hj, finrank_Vsub hc] at hsup
      omega
    exact le_antisymm hub hlb

theorem isFar_iff_mem_farSet (hd : IsCut (m + 1) d) {E x₀ : FlagK K (m + 1)}
    (hx₀ : x₀ ∈ refSet K (m + 1) d) :
    Gate.IsFar (symCox m) (flagδ (K := K) m) (cutTypes m d) Set.univ x₀ E ↔
      E ∈ farSet (m + 1) d := by
  have hB : IsWeylDistanceBuilding (symCox m) (flagδ (K := K) m) :=
    isWeylDistanceBuilding_flag (K := K) (m := m)
  haveI : Finite ((symCox m).parabolic (cutTypes m d)) := Subtype.finite
  haveI : Finite ((symCox m).parabolic Set.univ) := Subtype.finite
  have hτ := q2cFPj_blockRev_eq hd
  constructor
  · intro hfar
    unfold Gate.IsFar at hfar
    have hgmem : resProj (symCox m) (flagδ (K := K) m) (cutTypes m d) x₀ E ∈
        residue (symCox m) (flagδ (K := K) m) (cutTypes m d) x₀ :=
      resProj_mem hB _ _ _
    obtain ⟨y, hy, hgy⟩ := Gate.exists_mem_residue_dist_eq_mul hB
      (resProj (symCox m) (flagδ (K := K) m) (cutTypes m d) x₀ E)
      (resProj (symCox m) (flagδ (K := K) m) (cutTypes m d) x₀ E)
      (K := cutTypes m d) (v := longest (symCox m) (cutTypes m d))
      (isLongest_longest (cs := symCox m) (cutTypes m d)).1
    rw [hB.eq_one_self, one_mul] at hgy
    have hyx : y ∈ residue (symCox m) (flagδ (K := K) m) (cutTypes m d) x₀ := by
      rw [residue_eq_of_mem hB hgmem] at hy
      exact hy
    have hyref : y ∈ refSet K (m + 1) d := by
      rw [residue_cutTypes_eq hd hx₀] at hyx
      exact hyx
    have hgate := IsProjection.gate hB (isProjection_resProj hB (cutTypes m d) x₀ E) hyx
    have hEg : flagδ (K := K) m E
        (resProj (symCox m) (flagδ (K := K) m) (cutTypes m d) x₀ E) =
        longest (symCox m) Set.univ * longest (symCox m) (cutTypes m d) := by
      rw [flagδ_symm, hfar, mul_inv_rev,
        (isLongest_longest (cs := symCox m) (cutTypes m d)).inv_eq,
        (isLongest_longest (cs := symCox m) Set.univ).inv_eq]
    have hEy : flagδ (K := K) m E y = longest (symCox m) Set.univ := by
      rw [hgate.1, hEg, hgy, mul_assoc,
        (isLongest_longest (cs := symCox m) (cutTypes m d)).mul_self, mul_one]
    exact mem_farSet_of_opp hd hyref ((opp_iff_flagδ_eq_longest E y).mpr hEy)
  · intro hE
    have hproj := resProj_eq_gateFlag hd hE hx₀
    have h2 : flagδ (K := K) m E (gateFlag hd hE) = (blockRev hd)⁻¹ := by
      rw [flagδ, hasPos_iff.mp (hasPos_gateFlag hd hE)]
    have h1 : flagδ (K := K) m (gateFlag hd hE) E = blockRev hd := by
      rw [flagδ_symm, h2, inv_inv]
    unfold Gate.IsFar
    rw [hproj, h1, hτ]

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
