module

public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def NRpt (M : Submodule K (Fin 4 → K)) : Prop :=
  M ⊓ sgS K f 4 M = ⊥

private def plh_ws (s : K) : Fin 4 → K := ![1, s, 0, 0]

private def plh_winf (K : Type) [Zero K] [One K] : Fin 4 → K := ![0, 1, 0, 0]

private theorem plh_ws_mem_Vsub (s : K) : plh_ws s ∈ Vsub 4 2 := by
  intro j hj
  fin_cases j <;> simp_all [plh_ws]

private theorem plh_winf_mem_Vsub : plh_winf K ∈ Vsub 4 2 := by
  intro j hj
  fin_cases j <;> simp_all [plh_winf]

private theorem plh_ws_ne_zero (s : K) : plh_ws s ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [plh_ws] at h0

private theorem plh_winf_ne_zero : plh_winf K ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp [plh_winf] at h1

private theorem plh_ws_finrank (s : K) : finrank K (K ∙ plh_ws s) = 1 :=
  finrank_span_singleton (plh_ws_ne_zero s)

private theorem plh_winf_finrank : finrank K (K ∙ plh_winf K) = 1 :=
  finrank_span_singleton plh_winf_ne_zero

private theorem plh_sgv_ws (s : K) : sgv K f 4 (plh_ws s) = plh_ws (sg K f s) := by
  funext i
  fin_cases i <;> simp [plh_ws, sgv_apply]

private theorem plh_nrpt_of_moved (hK : Nat.card K = (2 ^ f) ^ 2) {s : K}
    (hs : sg K f s ≠ s) : NRpt f (K ∙ plh_ws s) := by
  rw [NRpt, sgS_span_singleton hK, plh_sgv_ws (f := f)]
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hv1, hv2⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv2
  have h0 : a = b := by
    have h := congrFun (ha.trans hb.symm) 0
    simpa [plh_ws] using h
  have h1 : a * s = b * sg K f s := by
    have h := congrFun (ha.trans hb.symm) 1
    simpa [plh_ws] using h
  have ha0 : a = 0 := by
    have hsne : s - sg K f s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    have hzero : a * (s - sg K f s) = 0 := by
      rw [mul_sub, h1, h0, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_right hsne
  rw [← ha, ha0, zero_smul]

theorem exists_two_nrpt (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∃ M₁ M₂ : Submodule K (Fin 4 → K), M₁ ≠ M₂ ∧ M₁ ≤ Vsub 4 2 ∧ M₂ ≤ Vsub 4 2 ∧
      finrank K M₁ = 1 ∧ finrank K M₂ = 1 ∧ NRpt f M₁ ∧ NRpt f M₂ := by
  obtain ⟨s₁, hs₁, -, -⟩ := exists_sg_moved_avoid (K := K) (f := f) hK hq 0 0
  obtain ⟨s₂, hs₂, hs₂₁, -⟩ := exists_sg_moved_avoid (K := K) (f := f) hK hq s₁ s₁
  refine ⟨K ∙ plh_ws s₁, K ∙ plh_ws s₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hmem : plh_ws s₂ ∈ K ∙ plh_ws s₁ := by
      rw [h]; exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c = 1 := by
      have h := congrFun hc 0
      simpa [plh_ws] using h
    have hc1 : c * s₁ = s₂ := by
      have h := congrFun hc 1
      simpa [plh_ws] using h
    rw [hc0, one_mul] at hc1
    exact hs₂₁ hc1.symm
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (plh_ws_mem_Vsub s₁)
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (plh_ws_mem_Vsub s₂)
  · exact plh_ws_finrank s₁
  · exact plh_ws_finrank s₂
  · exact plh_nrpt_of_moved (f := f) hK hs₁
  · exact plh_nrpt_of_moved (f := f) hK hs₂

theorem exists_nr_lines (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∃ B : Finset (Submodule K (Fin 4 → K)), B.Nonempty ∧ B.card ≤ 2 ^ f + 1 ∧
      (∀ m ∈ B, m ≤ Vsub 4 2 ∧ finrank K m = 1) ∧
      ∀ w ∈ Vsub 4 2, (∀ m ∈ B, w ∉ m) → w ≠ 0 ∧ NRpt f (K ∙ w) := by
  classical
  haveI := Fintype.ofFinite K
  set Fx : Finset K := Finset.univ.filter (fun s => sg K f s = s) with hFx
  have hFxcard : Fx.card ≤ 2 ^ f := by
    have h := card_sg_fixed_le (K := K) (f := f) hK
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    simpa [hFx] using h
  set B : Finset (Submodule K (Fin 4 → K)) :=
    insert (K ∙ plh_winf K) (Fx.image (fun s => K ∙ plh_ws s)) with hB
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · rw [hB]; exact Finset.insert_nonempty _ _
  · rw [hB]
    calc (insert (K ∙ plh_winf K) (Fx.image (fun s => K ∙ plh_ws s))).card
        ≤ (Fx.image (fun s => K ∙ plh_ws s)).card + 1 := Finset.card_insert_le _ _
      _ ≤ Fx.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ 2 ^ f + 1 := Nat.add_le_add_right hFxcard 1
  · intro m hm
    rw [hB, Finset.mem_insert, Finset.mem_image] at hm
    rcases hm with rfl | ⟨s, -, rfl⟩
    · exact ⟨(Submodule.span_singleton_le_iff_mem _ _).mpr plh_winf_mem_Vsub,
        plh_winf_finrank⟩
    · exact ⟨(Submodule.span_singleton_le_iff_mem _ _).mpr (plh_ws_mem_Vsub s),
        plh_ws_finrank s⟩
  · intro w hwV hwB
    have hw0 : w ≠ 0 := by
      intro h0
      have hmem : w ∈ K ∙ plh_winf K := by
        rw [h0]; exact Submodule.zero_mem _
      exact hwB _ (by rw [hB]; exact Finset.mem_insert_self _ _) hmem
    have ha : w 0 ≠ 0 := by
      intro ha0
      have hw_eq : w = (w 1) • plh_winf K := by
        funext j
        fin_cases j
        · simp [plh_winf, ha0]
        · simp [plh_winf]
        · have h2 : w 2 = 0 := hwV 2 (by norm_num)
          simp [plh_winf, h2]
        · have h3 : w 3 = 0 := hwV 3 (by norm_num)
          simp [plh_winf, h3]
      have hmem : w ∈ K ∙ plh_winf K := by
        rw [hw_eq]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      exact hwB _ (by rw [hB]; exact Finset.mem_insert_self _ _) hmem
    set s : K := w 1 / w 0 with hs
    have hw_eq : w = w 0 • plh_ws s := by
      funext j
      fin_cases j
      · change w 0 = (w 0 • plh_ws s) 0
        simp [plh_ws]
      · change w 1 = (w 0 • plh_ws s) 1
        simp only [Pi.smul_apply, smul_eq_mul, plh_ws, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.head_cons]
        rw [hs]
        rw [mul_div_cancel₀ (w 1) ha]
      · change w 2 = (w 0 • plh_ws s) 2
        have h2 : w 2 = 0 := hwV 2 (by norm_num)
        simp [plh_ws, h2]
      · change w 3 = (w 0 • plh_ws s) 3
        have h3 : w 3 = 0 := hwV 3 (by norm_num)
        simp [plh_ws, h3]
    have hs_ne : sg K f s ≠ s := by
      intro hseq
      have hsFx : s ∈ Fx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hseq⟩
      have hmemB : K ∙ plh_ws s ∈ B := by
        rw [hB]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s, hsFx, rfl⟩)
      have hwmem : w ∈ K ∙ plh_ws s := by
        rw [hw_eq]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      exact hwB _ hmemB hwmem
    refine ⟨hw0, ?_⟩
    rw [hw_eq, Submodule.span_singleton_smul_eq (IsUnit.mk0 (w 0) ha) (plh_ws s)]
    exact plh_nrpt_of_moved (f := f) hK hs_ne

end CFSG.ClassicalInvolution.Phan.PhanE

end
