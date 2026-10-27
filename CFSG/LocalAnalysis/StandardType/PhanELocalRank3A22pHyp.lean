module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3A22pDef
public import CFSG.LocalAnalysis.StandardType.PhanELocalClsNR

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

private def plh_v2 (s : K) : Fin 2 → K := ![1, s]

private theorem plh_v2_ne_zero (s : K) : plh_v2 s ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa [plh_v2] using h0

private theorem plh_sgv_v2 (s : K) : sgv K f 2 (plh_v2 s) = plh_v2 (sg K f s) := by
  funext i
  fin_cases i <;> simp [plh_v2, sgv_apply]

private theorem plh_v2_mem_iff (s t : K) (h : plh_v2 t ∈ K ∙ plh_v2 s) : t = s := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have ha1 : a = 1 := by
    have h := congrFun ha 0
    simpa [plh_v2] using h
  have has : a * s = t := by
    have h := congrFun ha 1
    simpa [plh_v2] using h
  rw [← has, ha1, one_mul]

private theorem plh_v2_finrank (s : K) : finrank K (K ∙ plh_v2 s) = 1 :=
  finrank_span_singleton (plh_v2_ne_zero s)

private theorem plh_v2_inf_sgS (hK : Nat.card K = (2 ^ f) ^ 2) {s : K}
    (hs : sg K f s ≠ s) :
    (K ∙ plh_v2 s) ⊓ sgS K f 2 (K ∙ plh_v2 s) = ⊥ := by
  rw [sgS_span_singleton hK, plh_sgv_v2 (f := f)]
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hv1, hv2⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv2
  have hab : a = b := by
    have h := congrFun (ha.trans hb.symm) 0
    simpa [plh_v2] using h
  have has : a * s = b * sg K f s := by
    have h := congrFun (ha.trans hb.symm) 1
    simpa [plh_v2] using h
  have ha0 : a = 0 := by
    have hsne : s - sg K f s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    have hzero : a * (s - sg K f s) = 0 := by
      rw [mul_sub, has, hab, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_right hsne
  rw [← ha, ha0, zero_smul]

private theorem plh_v2_injective : Function.Injective (fun s : K => K ∙ plh_v2 s) := by
  intro s t hst
  change K ∙ plh_v2 s = K ∙ plh_v2 t at hst
  have hmem : plh_v2 t ∈ K ∙ plh_v2 s := by
    rw [hst]
    exact Submodule.mem_span_singleton_self _
  exact (plh_v2_mem_iff s t hmem).symm

theorem clsHyp_a3_22p (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ClsHyp (D22p (K := K) f) (2 ^ f + 1) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    by_contra h
    haveI : Fintype K := Fintype.ofFinite K
    set F : Finset K := Finset.univ.filter (fun s => sg K f s ≠ s) with hF
    have hFcard : Nat.card {s : K // sg K f s ≠ s} = F.card := by
      rw [hF, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h12 : 12 ≤ F.card := by
      have hmoved := card_sg_moved_ge (K := K) (f := f) hK
      have hge : 12 ≤ Nat.card K - 2 ^ f := by
        rw [hK, pow_two]
        have hmul : 4 * 3 ≤ 2 ^ f * (2 ^ f - 1) := Nat.mul_le_mul hq (by omega)
        calc 12 ≤ 4 * 3 := by norm_num
          _ ≤ 2 ^ f * (2 ^ f - 1) := hmul
          _ = 2 ^ f * 2 ^ f - 2 ^ f := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [← hFcard]
      exact le_trans hge hmoved
    have hupper : F.card ≤ S.card := by
      refine Finset.card_le_card_of_injOn (fun s : K => K ∙ plh_v2 s) ?_ ?_
      · intro s hs
        have hsF : s ∈ F := by simpa only [Finset.mem_coe] using hs
        have hsne : sg K f s ≠ s := by
          rw [hF] at hsF
          exact (Finset.mem_filter.mp hsF).2
        by_contra hsS
        apply h
        refine ⟨K ∙ plh_v2 s, ?_, plh_v2_finrank s, hsS⟩
        change (K ∙ plh_v2 s) ⊓ sgS K f 2 (K ∙ plh_v2 s) = ⊥
        exact plh_v2_inf_sgS (K := K) (f := f) hK hsne
      · intro s _ t _ hst
        exact plh_v2_injective hst
    omega
  · intro c _ _
    obtain ⟨M₁, M₂, hne, hM₁V, hM₂V, hf₁, hf₂, hg₁, hg₂⟩ :=
      exists_two_nrpt (K := K) f hK hq
    exact ⟨M₁, M₂, hne, hM₁V, hM₂V, hf₁, hf₂, hg₁, hg₂⟩
  · intro c c' _ _ _ _ _
    obtain ⟨M₁, M₂, hneM, hM₁V, hM₂V, hf₁, hf₂, hg₁, hg₂⟩ :=
      exists_two_nrpt (K := K) f hK hq
    exact ⟨M₁, hM₁V, hf₁, hg₁, hg₁⟩
  · intro a b d _ _ _ _ _ _ _ _ _
    obtain ⟨B, hBne, hBcard, hBmem, hBgood⟩ := exists_nr_lines (K := K) f hK hq
    refine ⟨B, hBne, hBcard, hBmem, ?_⟩
    intro w hwV hwB
    obtain ⟨hw0, hwNR⟩ := hBgood w hwV hwB
    exact ⟨hw0, hwNR, hwNR, hwNR⟩
  · rw [hK]
    nlinarith [hq]

end CFSG.ClassicalInvolution.Phan.PhanE

end
