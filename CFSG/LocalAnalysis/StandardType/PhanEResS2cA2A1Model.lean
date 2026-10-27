module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagA2A1
public import CFSG.LocalAnalysis.StandardType.PhanEFlagBlkMap

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.ClassicalInvolution.Phan.PhanE.Flag

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

@[expose] def emb21 {K : Type} [Field K] (B : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, B 0 0, B 0 1; 0, B 1 0, B 1 1]

private theorem pls2a_jShift21_emb21 (B₂ : GL (Fin 2) K) (g₁' : GL (Fin 3) K)
    (hg₁' : (g₁' : Matrix (Fin 3) (Fin 3) K) =
      emb21 ((B₂ : Matrix (Fin 2) (Fin 2) K).map (sg K f : K →+* K)))
    (u : Fin 2 → K) :
    jShift21 K f (glLin B₂ u) = glLin g₁' (jShift21 K f u) := by
  funext i
  fin_cases i <;> simp [jShift21, glLin_apply, hg₁', emb21, Matrix.mulVec, Fin.sum_univ_three,
    Fin.sum_univ_two, map_add, map_mul, vecHead, vecTail]

private theorem pls2a_jShift21Inv_emb21 (B₁ : GL (Fin 2) K) (g₁ : GL (Fin 3) K)
    (hg₁ : (g₁ : Matrix (Fin 3) (Fin 3) K) = emb21 (B₁ : Matrix (Fin 2) (Fin 2) K))
    (g₂' : GL (Fin 2) K)
    (hg₂' : (g₂' : Matrix (Fin 2) (Fin 2) K) =
      (B₁ : Matrix (Fin 2) (Fin 2) K).map (sg K f : K →+* K))
    (v : Fin 3 → K) :
    jShift21Inv K f (glLin g₁ v) = glLin g₂' (jShift21Inv K f v) := by
  funext i
  fin_cases i <;> simp [jShift21Inv, glLin_apply, hg₁, hg₂', emb21, Matrix.mulVec,
    Fin.sum_univ_three, Fin.sum_univ_two, map_add, map_mul, vecHead, vecTail]

private theorem pls2a_stab_Vsub_one (M : Matrix (Fin 2) (Fin 2) K) (g : GL (Fin 3) K)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = emb21 M) :
    (Vsub 3 1).map (glLin g).toLinearMap = Vsub 3 1 := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro v hv j hj
    have hv1 : v 1 = 0 := hv 1 (by norm_num)
    have hv2 : v 2 = 0 := hv 2 (by norm_num)
    fin_cases j
    · simp at hj
    · simp [glLin_apply, hg, emb21, Matrix.mulVec, Fin.sum_univ_three, vecHead, vecTail, hv1, hv2]
    · simp [glLin_apply, hg, emb21, Matrix.mulVec, Fin.sum_univ_three, vecHead, vecTail, hv1, hv2]
  · intro v hv
    rw [Submodule.mem_map]
    refine ⟨v, hv, ?_⟩
    ext j
    fin_cases j
    · simp [glLin_apply, hg, emb21, Matrix.mulVec, Fin.sum_univ_three, vecHead, vecTail]
    · simp [glLin_apply, hg, emb21, Matrix.mulVec, Fin.sum_univ_three, vecHead, vecTail,
        hv 1 (by norm_num), hv 2 (by norm_num)]
    · simp [glLin_apply, hg, emb21, Matrix.mulVec, Fin.sum_univ_three, vecHead, vecTail,
        hv 1 (by norm_num), hv 2 (by norm_num)]

private theorem pls2a_stab_Vsub_zero (g : GL (Fin 3) K) :
    (Vsub 3 0).map (glLin g).toLinearMap = Vsub 3 0 := by
  simp [Vsub_zero]

private theorem pls2a_stab_Vsub_top (g : GL (Fin 3) K) :
    (Vsub 3 3).map (glLin g).toLinearMap = Vsub 3 3 := by
  simp [Vsub_self]

private theorem pls2a_map_span_jShift21 (B₂ : GL (Fin 2) K) (g₁' : GL (Fin 3) K)
    (hg₁' : (g₁' : Matrix (Fin 3) (Fin 3) K) =
      emb21 ((B₂ : Matrix (Fin 2) (Fin 2) K).map (sg K f : K →+* K)))
    (U : Submodule K (Fin 2 → K)) :
    Submodule.span K (jShift21 K f '' ((U.map (glLin B₂).toLinearMap : Set (Fin 2 → K)))) =
      (Submodule.span K (jShift21 K f '' (U : Set (Fin 2 → K)))).map (glLin g₁').toLinearMap := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨jShift21 K f u, ⟨u, hu, rfl⟩, (pls2a_jShift21_emb21 B₂ g₁' hg₁' u).symm⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨glLin B₂ u, ⟨u, hu, rfl⟩, pls2a_jShift21_emb21 B₂ g₁' hg₁' u⟩

private theorem pls2a_map_span_jShift21Inv (B₁ : GL (Fin 2) K) (g₁ : GL (Fin 3) K)
    (hg₁ : (g₁ : Matrix (Fin 3) (Fin 3) K) = emb21 (B₁ : Matrix (Fin 2) (Fin 2) K))
    (g₂' : GL (Fin 2) K)
    (hg₂' : (g₂' : Matrix (Fin 2) (Fin 2) K) =
      (B₁ : Matrix (Fin 2) (Fin 2) K).map (sg K f : K →+* K))
    (U : Submodule K (Fin 3 → K)) :
    Submodule.span K (jShift21Inv K f '' ((U.map (glLin g₁).toLinearMap : Set (Fin 3 → K)))) =
      (Submodule.span K (jShift21Inv K f '' (U : Set (Fin 3 → K)))).map
        (glLin g₂').toLinearMap := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨jShift21Inv K f u, ⟨u, hu, rfl⟩, (pls2a_jShift21Inv_emb21 B₁ g₁ hg₁ g₂' hg₂' u).symm⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨glLin g₁ u, ⟨u, hu, rfl⟩, pls2a_jShift21Inv_emb21 B₁ g₁ hg₁ g₂' hg₂' u⟩

theorem pls2a_stdFlag_3_mem : (stdFlag K 3) ∈ refSet K 3 [0, 1, 3] := by
  intro i hi
  rfl

private theorem pls2a_mem_Vsub_one {v : Fin 3 → K} (h1 : v 1 = 0) (h2 : v 2 = 0) :
    v ∈ Vsub 3 1 := by
  intro j hj
  have hjval : j.val = 1 ∨ j.val = 2 := by have := j.isLt; omega
  rcases hjval with h | h
  · have hj1 : j = (1 : Fin 3) := Fin.eq_of_val_eq h
    rw [hj1]; exact h1
  · have hj2 : j = (2 : Fin 3) := Fin.eq_of_val_eq h
    rw [hj2]; exact h2

private theorem pls2a_mem_Vsub_two {v : Fin 3 → K} (h : v 2 = 0) : v ∈ Vsub 3 2 := by
  intro j hj
  have hjval : j.val = 2 := by have := j.isLt; omega
  have hj2 : j = (2 : Fin 3) := Fin.eq_of_val_eq hjval
  rw [hj2]; exact h

private theorem pls2a_mem_Vsub_two_one {v : Fin 2 → K} (h : v 1 = 0) : v ∈ Vsub 2 1 := by
  intro j hj
  have hjval : j.val = 1 := by have := j.isLt; omega
  have hj1 : j = (1 : Fin 2) := Fin.eq_of_val_eq hjval
  rw [hj1]; exact h

private theorem pls2a_jShift21_jShift21Inv (hK : Nat.card K = (2 ^ f) ^ 2) (v : Fin 3 → K) :
    jShift21 K f (jShift21Inv K f v) = (![0, v 1, v 2] : Fin 3 → K) := by
  funext i
  fin_cases i
  · rfl
  · show sg K f (sg K f (v 1)) = v 1
    exact sg_sg hK (v 1)
  · show sg K f (sg K f (v 2)) = v 2
    exact sg_sg hK (v 2)

private theorem pls2a_flagAct_E {n : ℕ} (g : GL (Fin n) K) (x : FlagK K n) (j : ℕ) :
    (flagAct g x).E j = (x.E j).map (glLin g).toLinearMap := by
  change (flagMap (glLin g) x).E j = _
  rw [flagMap_E]

private theorem pls2a_stabV_of_emb21 (B : GL (Fin 2) K) (g : GL (Fin 3) K)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = emb21 (B : Matrix (Fin 2) (Fin 2) K)) :
    StabV 3 [0, 1, 3] g := by
  intro i hi
  have hi' : i < 3 := by simpa using hi
  interval_cases i
  · rw [show [0, 1, 3].getD 0 0 = 0 by rfl]
    exact pls2a_stab_Vsub_zero g
  · rw [show [0, 1, 3].getD 1 0 = 1 by rfl]
    exact pls2a_stab_Vsub_one (B : Matrix (Fin 2) (Fin 2) K) g hg
  · rw [show [0, 1, 3].getD 2 0 = 3 by rfl]
    exact pls2a_stab_Vsub_top g

private theorem pls2a_sup_jShift21_Vsub21 (hK : Nat.card K = (2 ^ f) ^ 2) :
    Vsub 3 1 ⊔ Submodule.span K (jShift21 K f '' ↑(Vsub 2 1 : Submodule K (Fin 2 → K))) =
      Vsub 3 2 := by
  apply le_antisymm
  · rw [sup_le_iff]
    constructor
    · exact Vsub_mono (by norm_num : 1 ≤ 2)
    · rw [Submodule.span_le]
      rintro x ⟨u, hu, rfl⟩
      apply pls2a_mem_Vsub_two
      have hu1 : u 1 = 0 := hu 1 (by norm_num)
      simp [jShift21, hu1]
  · intro v hv
    have hv2 : v 2 = 0 := hv 2 (by norm_num)
    have hw : jShift21 K f (jShift21Inv K f v) ∈
        Submodule.span K (jShift21 K f '' ↑(Vsub 2 1 : Submodule K (Fin 2 → K))) := by
      apply Submodule.subset_span
      refine ⟨jShift21Inv K f v, ?_, rfl⟩
      apply pls2a_mem_Vsub_two_one
      simp [jShift21Inv, hv2]
    have hdecomp : v = (![v 0, 0, 0] : Fin 3 → K) + (![0, v 1, 0] : Fin 3 → K) := by
      funext i
      fin_cases i <;> simp [hv2]
    have hw' : (![0, v 1, 0] : Fin 3 → K) = jShift21 K f (jShift21Inv K f v) := by
      rw [pls2a_jShift21_jShift21Inv hK v]
      funext i
      fin_cases i <;> simp [hv2]
    rw [hdecomp, hw']
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (by apply pls2a_mem_Vsub_one <;> simp))
      (Submodule.mem_sup_right hw)

private theorem pls2a_span_jShift21Inv_Vsub32 (hK : Nat.card K = (2 ^ f) ^ 2) :
    Submodule.span K (jShift21Inv K f '' ↑(Vsub 3 2 : Submodule K (Fin 3 → K))) =
      Vsub 2 1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨v, hv, rfl⟩
    apply pls2a_mem_Vsub_two_one
    have hv2 : v 2 = 0 := hv 2 (by norm_num)
    simp [jShift21Inv, hv2]
  · intro u hu
    have hu1 : u 1 = 0 := hu 1 (by norm_num)
    have hmem : u = jShift21Inv K f (![0, sg K f (u 0), 0] : Fin 3 → K) := by
      funext i
      fin_cases i
      · show u 0 = sg K f (sg K f (u 0))
        exact (sg_sg hK (u 0)).symm
      · simp [jShift21Inv, hu1]
    rw [hmem]
    refine Submodule.subset_span ⟨![0, sg K f (u 0), 0], ?_, rfl⟩
    apply pls2a_mem_Vsub_two
    simp

theorem psiA2A1_flagAct (hK : Nat.card K = (2 ^ f) ^ 2) (B₁ B₂ : GL (Fin 2) K)
    (g₁ g₁' : GL (Fin 3) K) (g₂' : GL (Fin 2) K)
    (hg₁ : (g₁ : Matrix (Fin 3) (Fin 3) K) = emb21 (B₁ : Matrix (Fin 2) (Fin 2) K))
    (hg₁' : (g₁' : Matrix (Fin 3) (Fin 3) K) =
      emb21 ((B₂ : Matrix (Fin 2) (Fin 2) K).map (sg K f : K →+* K)))
    (hg₂' : (g₂' : Matrix (Fin 2) (Fin 2) K) =
      (B₁ : Matrix (Fin 2) (Fin 2) K).map (sg K f : K →+* K))
    {c : FlagK K 3 × FlagK K 2} (hc : c.1 ∈ refSet K 3 [0, 1, 3]) :
    psiA2A1 hK (flagAct g₁ c.1, flagAct B₂ c.2) =
      (flagAct g₁' (psiA2A1 hK c).1, flagAct g₂' (psiA2A1 hK c).2) := by
  have hg₁_mem : flagAct g₁ c.1 ∈ refSet K 3 [0, 1, 3] :=
    StabV.flagAct_mem_refSet (pls2a_stabV_of_emb21 B₁ g₁ hg₁) hc
  have hc_def : psiA2A1 hK c = Classical.choose (exists_psiA2A1 hK (c := c) hc) := by
    rw [psiA2A1, dif_pos hc]
  have hd_def : psiA2A1 hK (flagAct g₁ c.1, flagAct B₂ c.2) =
      Classical.choose (exists_psiA2A1 hK (c := (flagAct g₁ c.1, flagAct B₂ c.2)) hg₁_mem) := by
    rw [psiA2A1, dif_pos hg₁_mem]
  rw [hc_def, hd_def]
  have hc' := Classical.choose_spec (exists_psiA2A1 hK (c := c) hc)
  have hd' := Classical.choose_spec
    (exists_psiA2A1 hK (c := (flagAct g₁ c.1, flagAct B₂ c.2)) hg₁_mem)
  have hF1 : (Classical.choose (exists_psiA2A1 hK (c := c) hc)).1.E 1 = Vsub 3 1 :=
    hc'.1 1 (by decide)
  have hF'1 : (Classical.choose
      (exists_psiA2A1 hK (c := (flagAct g₁ c.1, flagAct B₂ c.2)) hg₁_mem)).1.E 1 = Vsub 3 1 :=
    hd'.1 1 (by decide)
  have hF2 : (Classical.choose (exists_psiA2A1 hK (c := c) hc)).1.E 2 =
      Vsub 3 1 ⊔ Submodule.span K (jShift21 K f '' (c.2.E 1 : Set (Fin 2 → K))) := hc'.2.1
  have hF'2 : (Classical.choose
      (exists_psiA2A1 hK (c := (flagAct g₁ c.1, flagAct B₂ c.2)) hg₁_mem)).1.E 2 =
      Vsub 3 1 ⊔ Submodule.span K
        (jShift21 K f '' ((flagAct B₂ c.2).E 1 : Set (Fin 2 → K))) := by
    simpa using hd'.2.1
  have hZ1 : (Classical.choose (exists_psiA2A1 hK (c := c) hc)).2.E 1 =
      Submodule.span K (jShift21Inv K f '' (c.1.E 2 : Set (Fin 3 → K))) := hc'.2.2
  have hZ'1 : (Classical.choose
      (exists_psiA2A1 hK (c := (flagAct g₁ c.1, flagAct B₂ c.2)) hg₁_mem)).2.E 1 =
      Submodule.span K
        (jShift21Inv K f '' ((flagAct g₁ c.1).E 2 : Set (Fin 3 → K))) := by
    simpa using hd'.2.2
  refine Prod.ext ?_ ?_
  · show (Classical.choose
        (exists_psiA2A1 hK (c := (flagAct g₁ c.1, flagAct B₂ c.2)) hg₁_mem)).1 =
      flagAct g₁' (Classical.choose (exists_psiA2A1 hK (c := c) hc)).1
    apply FlagK.ext_of_mid
    intro j hj1 hj3
    interval_cases j
    · rw [hF'1, pls2a_flagAct_E (n := 3), hF1]
      exact (pls2a_stab_Vsub_one
        ((B₂ : Matrix (Fin 2) (Fin 2) K).map (sg K f : K →+* K)) g₁' hg₁').symm
    · rw [hF'2, pls2a_flagAct_E (n := 3), hF2, Submodule.map_sup,
        pls2a_stab_Vsub_one ((B₂ : Matrix (Fin 2) (Fin 2) K).map (sg K f : K →+* K)) g₁' hg₁',
        pls2a_flagAct_E (n := 2), pls2a_map_span_jShift21 B₂ g₁' hg₁' (c.2.E 1)]
  · show (Classical.choose
        (exists_psiA2A1 hK (c := (flagAct g₁ c.1, flagAct B₂ c.2)) hg₁_mem)).2 =
      flagAct g₂' (Classical.choose (exists_psiA2A1 hK (c := c) hc)).2
    apply FlagK.ext_of_mid
    intro j hj1 hj2
    interval_cases j
    rw [hZ'1, pls2a_flagAct_E (n := 2), hZ1, pls2a_flagAct_E (n := 3),
      pls2a_map_span_jShift21Inv B₁ g₁ hg₁ g₂' hg₂' (c.1.E 2)]

theorem psiA2A1_stdFlag (hK : Nat.card K = (2 ^ f) ^ 2) :
    psiA2A1 hK (stdFlag K 3, stdFlag K 2) = (stdFlag K 3, stdFlag K 2) := by
  have hc : (stdFlag K 3) ∈ refSet K 3 [0, 1, 3] := pls2a_stdFlag_3_mem
  rw [psiA2A1, dif_pos hc]
  have hc' := Classical.choose_spec (exists_psiA2A1 hK (c := (stdFlag K 3, stdFlag K 2)) hc)
  refine Prod.ext ?_ ?_
  · show (Classical.choose (exists_psiA2A1 hK (c := (stdFlag K 3, stdFlag K 2)) hc)).1 =
      stdFlag K 3
    apply FlagK.ext_of_mid
    intro j hj1 hj3
    interval_cases j
    · exact hc'.1 1 (by decide)
    · rw [hc'.2.1]
      change Vsub 3 1 ⊔ Submodule.span K
        (jShift21 K f '' ↑((stdFlag K 2).E 1)) = (stdFlag K 3).E 2
      rw [show (stdFlag K 2).E 1 = (Vsub 2 1 : Submodule K (Fin 2 → K)) from rfl]
      change Vsub 3 1 ⊔ Submodule.span K
        (jShift21 K f '' ↑(Vsub 2 1 : Submodule K (Fin 2 → K))) = Vsub 3 2
      rw [pls2a_sup_jShift21_Vsub21 hK]
  · show (Classical.choose (exists_psiA2A1 hK (c := (stdFlag K 3, stdFlag K 2)) hc)).2 =
      stdFlag K 2
    apply FlagK.ext_of_mid
    intro j hj1 hj2
    interval_cases j
    rw [hc'.2.2]
    change Submodule.span K
      (jShift21Inv K f '' ↑((stdFlag K 3).E 2)) = (stdFlag K 2).E 1
    rw [show (stdFlag K 3).E 2 = (Vsub 3 2 : Submodule K (Fin 3 → K)) from rfl]
    change Submodule.span K
      (jShift21Inv K f '' ↑(Vsub 3 2 : Submodule K (Fin 3 → K))) = Vsub 2 1
    rw [pls2a_span_jShift21Inv_Vsub32 hK]

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
