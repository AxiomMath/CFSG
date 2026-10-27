module

public import CFSG.Monster.B.TwoA.Sp8.T8Coords
public import CFSG.GroupTheory.ElementaryAbelianTransport

set_option linter.unusedSectionVars false

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Open
open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank

@[expose] def t8A : Fin 4 → Subgroup Dfull :=
  ![nfGrp gensA1, nfGrp gensA2, (nfGrp gensA2).map (MulAut.conj xD⁻¹).toMonoidHom,
    (nfGrp gensA4').map (MulAut.conj yD⁻¹).toMonoidHom]

private theorem uE_zero : uE 0 = 1 := by
  rw [uE, uProd]
  have h : (List.range 10).flatMap
      (fun k => if (0 : ℕ).testBit k then uWord k else []) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro k hk
    simp
  rw [h, wordX_nil]

private theorem nfD_mem_Lgrp_of_third_eq_zero {σ τ κ : ℕ} (hκ : κ = 0) :
    nfD (σ, τ, κ) ∈ Lgrp := by
  subst hκ
  rw [nfD, uE_zero, mul_one]
  exact Lgrp.mul_mem (lD_mem_Lgrp σ) (T9_le_Lgrp (tD_mem_T9 τ))

private theorem gensA1_third : ∀ c ∈ gensA1, c.2.2 = 0 := by
  decide

private theorem nfGrp_gensA1_le_Lgrp : nfGrp gensA1 ≤ Lgrp := by
  rw [nfGrp]
  refine (Subgroup.closure_le Lgrp).2 ?_
  rintro g ⟨c, hc, rfl⟩
  exact nfD_mem_Lgrp_of_third_eq_zero (gensA1_third c hc)

private theorem flagGens_bound : ∀ i : Fin 4, ∀ v ∈ flagGens i, v < 2 ^ 9 := by
  decide

private theorem xT9_bound : ∀ c ∈ xT9, c < 2 ^ 9 := by
  decide

private theorem yT9_bound : ∀ c ∈ yT9, c < 2 ^ 9 := by
  decide

private theorem P0_le_Xgrp : P0 ≤ Xgrp := P0_le_flagS.trans flagS_le_Xgrp

private theorem conjA2_conj_tD (c : ℕ × ℕ × ℕ) {v : ℕ} (hv : v < 2 ^ 9) :
    (xD⁻¹ * nfD c * xD) * tD v * (xD⁻¹ * nfD c * xD)⁻¹ =
      tD (colsAct xT9inv (actK p0Data.uConjT c.2.2 (colsAct xT9 v))) := by
  have h1 : colsAct xT9 v < 2 ^ 9 := colsAct_lt xT9_bound v
  have h2 : actK p0Data.uConjT c.2.2 (colsAct xT9 v) < 2 ^ 9 :=
    actK_uConjT_lt c.2.2 h1
  calc (xD⁻¹ * nfD c * xD) * tD v * (xD⁻¹ * nfD c * xD)⁻¹
      = xD⁻¹ * nfD c * (xD * tD v * xD⁻¹) * (nfD c)⁻¹ * xD := by group
    _ = xD⁻¹ * nfD c * tD (colsAct xT9 v) * (nfD c)⁻¹ * xD := by
          rw [xD_conj_tD hv]
    _ = xD⁻¹ * (nfD c * tD (colsAct xT9 v) * (nfD c)⁻¹) * xD := by group
    _ = xD⁻¹ * tD (actK p0Data.uConjT c.2.2 (colsAct xT9 v)) * xD := by
          rw [nfD_conj_tD c h1]
    _ = tD (colsAct xT9inv (actK p0Data.uConjT c.2.2 (colsAct xT9 v))) := by
          rw [xD_inv_conj_tD h2]

private theorem conjA4'_conj_tD (c : ℕ × ℕ × ℕ) {v : ℕ} (hv : v < 2 ^ 9) :
    (yD⁻¹ * nfD c * yD) * tD v * (yD⁻¹ * nfD c * yD)⁻¹ =
      tD (colsAct yT9 (actK p0Data.uConjT c.2.2 (colsAct yT9 v))) := by
  have h1 : colsAct yT9 v < 2 ^ 9 := colsAct_lt yT9_bound v
  have h2 : actK p0Data.uConjT c.2.2 (colsAct yT9 v) < 2 ^ 9 :=
    actK_uConjT_lt c.2.2 h1
  calc (yD⁻¹ * nfD c * yD) * tD v * (yD⁻¹ * nfD c * yD)⁻¹
      = yD⁻¹ * nfD c * (yD * tD v * yD⁻¹) * (nfD c)⁻¹ * yD := by group
    _ = yD⁻¹ * nfD c * tD (colsAct yT9 v) * (nfD c)⁻¹ * yD := by
          rw [yD_conj_tD hv]
    _ = yD⁻¹ * (nfD c * tD (colsAct yT9 v) * (nfD c)⁻¹) * yD := by group
    _ = yD⁻¹ * tD (actK p0Data.uConjT c.2.2 (colsAct yT9 v)) * yD := by
          rw [nfD_conj_tD c h1]
    _ = tD (colsAct yT9 (actK p0Data.uConjT c.2.2 (colsAct yT9 v))) := by
          rw [yD_inv_conj_tD h2]

private theorem mem_xorSpan_conjA2 :
    ∀ c ∈ gensA2, ∀ i : Fin 4, ∀ v ∈ flagGens i,
      colsAct xT9inv (actK p0Data.uConjT c.2.2 (colsAct xT9 v)) ∈ xorSpan (flagGens i) := by
  decide

private theorem mem_xorSpan_conjA4' :
    ∀ c ∈ gensA4', ∀ i : Fin 4, ∀ v ∈ flagGens i,
      colsAct yT9 (actK p0Data.uConjT c.2.2 (colsAct yT9 v)) ∈ xorSpan (flagGens i) := by
  decide

private theorem conjA2_mem_flagS (c : ℕ × ℕ × ℕ) (hc : c ∈ gensA2) :
    xD⁻¹ * nfD c * xD ∈ flagS := by
  have hgen : nfD c ∈ nfGrp gensA2 := Subgroup.subset_closure ⟨c, hc, rfl⟩
  have hP0 : nfD c ∈ P0 := nfGrp_le_P0 gensA2 hgen
  refine mem_flagS_of ?_ ?_
  · exact Xgrp.mul_mem (Xgrp.mul_mem (Xgrp.inv_mem xD_mem_Xgrp)
      (P0_le_Xgrp hP0)) xD_mem_Xgrp
  · intro i v hv
    exact ⟨_, mem_xorSpan_conjA2 c hc i v hv, conjA2_conj_tD c (flagGens_bound i v hv)⟩

private theorem conjA4'_mem_flagS (c : ℕ × ℕ × ℕ) (hc : c ∈ gensA4') :
    yD⁻¹ * nfD c * yD ∈ flagS := by
  have hgen : nfD c ∈ nfGrp gensA4' := Subgroup.subset_closure ⟨c, hc, rfl⟩
  have hP0 : nfD c ∈ P0 := nfGrp_le_P0 gensA4' hgen
  refine mem_flagS_of ?_ ?_
  · exact Xgrp.mul_mem (Xgrp.mul_mem (Xgrp.inv_mem yD_mem_Xgrp)
      (P0_le_Xgrp hP0)) yD_mem_Xgrp
  · intro i v hv
    exact ⟨_, mem_xorSpan_conjA4' c hc i v hv, conjA4'_conj_tD c (flagGens_bound i v hv)⟩

theorem t8A_le_flagS (i : Fin 4) : t8A i ≤ flagS := by
  fin_cases i
  · simpa [t8A] using (nfGrp_le_P0 gensA1).trans P0_le_flagS
  · simpa [t8A] using (nfGrp_le_P0 gensA2).trans P0_le_flagS
  · change (nfGrp gensA2).map (MulAut.conj xD⁻¹).toMonoidHom ≤ flagS
    rw [nfGrp, MonoidHom.map_closure]
    refine (Subgroup.closure_le flagS).2 ?_
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, SetLike.mem_coe] using
      conjA2_mem_flagS c hc
  · change (nfGrp gensA4').map (MulAut.conj yD⁻¹).toMonoidHom ≤ flagS
    rw [nfGrp, MonoidHom.map_closure]
    refine (Subgroup.closure_le flagS).2 ?_
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, SetLike.mem_coe] using
      conjA4'_mem_flagS c hc

theorem t8A_isElemAbelian (i : Fin 4) : IsElemAbelian 2 (t8A i) := by
  fin_cases i
  · simpa [t8A] using isElemAbelian_A1
  · simpa [t8A] using isElemAbelian_A2
  · simpa [t8A] using IsElemAbelian.map isElemAbelian_A2 (MulAut.conj xD⁻¹).toMonoidHom
  · simpa [t8A] using IsElemAbelian.map isElemAbelian_A4' (MulAut.conj yD⁻¹).toMonoidHom

theorem t8A_card (i : Fin 4) : Nat.card (t8A i) = 2 ^ 14 := by
  fin_cases i
  · simpa [t8A] using layers_A1.2.2.2
  · simpa [t8A] using layers_A2.2.2.2
  · change Nat.card ((nfGrp gensA2).map (MulAut.conj xD⁻¹).toMonoidHom) = 2 ^ 14
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj xD⁻¹).toMonoidHom)
      (MulAut.conj xD⁻¹).injective]
    exact layers_A2.2.2.2
  · change Nat.card ((nfGrp gensA4').map (MulAut.conj yD⁻¹).toMonoidHom) = 2 ^ 14
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj yD⁻¹).toMonoidHom)
      (MulAut.conj yD⁻¹).injective]
    exact layers_A4'.2.2.2

private theorem mem_xorSpan_A1_A2 :
    ∀ σ ∈ xorSpan [14479, 52645, 64475, 52504, 43198],
      σ ∈ xorSpan [132, 12, 68, 4] → σ = 0 := by
  decide

private theorem tau_check :
    ∀ τ ∈ List.range (2 ^ 9),
      τ ∈ xorSpan [2, 48, 304, 268, 271] →
      colsAct xT9 τ ∈ xorSpan [2, 48, 304, 268, 271] →
      colsAct yT9 τ ∈ xorSpan [284, 48, 63, 288, 2] →
      τ < 4 := by
  decide +kernel

theorem mem_iInf_t8A {h : Dfull} (hh : h ∈ (⨅ i, t8A i : Subgroup Dfull)) :
    h = tD 0 ∨ h = tD 1 ∨ h = tD 2 ∨ h = tD 3 := by
  classical
  have h0 : h ∈ nfGrp gensA1 := by
    simpa [t8A] using (Subgroup.mem_iInf.1 hh 0)
  have h1 : h ∈ nfGrp gensA2 := by
    simpa [t8A] using (Subgroup.mem_iInf.1 hh 1)
  have h2 : h ∈ (nfGrp gensA2).map (MulAut.conj xD⁻¹).toMonoidHom := by
    simpa [t8A] using (Subgroup.mem_iInf.1 hh 2)
  have h3 : h ∈ (nfGrp gensA4').map (MulAut.conj yD⁻¹).toMonoidHom := by
    simpa [t8A] using (Subgroup.mem_iInf.1 hh 3)
  have hL : h ∈ Lgrp := nfGrp_gensA1_le_Lgrp h0
  obtain ⟨σ, hσ16, hσcoord⟩ :=
    CFSG.KC.BvecLoop.exists_bvec 16 (sCoord ⟨h, hL⟩).toAdd
  have hσc : sCoord ⟨h, hL⟩ = Multiplicative.ofAdd (bvec 16 σ) := by
    rw [← ofAdd_toAdd (sCoord ⟨h, hL⟩), ← hσcoord]
  have hσD1 : σ ∈ layerD (nfGrp gensA1) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hσ16, ?_⟩
    exact ⟨⟨h, hL⟩, h0, hσc⟩
  have hσD2 : σ ∈ layerD (nfGrp gensA2) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hσ16, ?_⟩
    exact ⟨⟨h, hL⟩, h1, hσc⟩
  rw [layers_A1.1] at hσD1
  rw [layers_A2.1] at hσD2
  have hσ0 : σ = 0 :=
    mem_xorSpan_A1_A2 σ (by simpa using hσD1) (by simpa using hσD2)
  have hscoord : sCoord ⟨h, hL⟩ = 1 := by
    rw [hσc, hσ0]
    simp [bvec_zero]
  have hT9 : h ∈ T9 := (sCoord_eq_one_iff ⟨h, hL⟩).1 hscoord
  obtain ⟨τ, hτ, hτeq⟩ := exists_tD_of_mem_T9 hT9
  have hx2 : xD * h * xD⁻¹ ∈ nfGrp gensA2 := by
    obtain ⟨n, hn, hfn⟩ := Subgroup.mem_map.1 h2
    have hconj : xD * h * xD⁻¹ = n := by
      rw [← hfn]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hconj]
    exact hn
  have hY2 : colsAct xT9 τ ∈ layerY (nfGrp gensA2) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (colsAct_lt xT9_bound τ), ?_⟩
    rw [← xD_conj_tD hτ, ← hτeq]
    exact hx2
  have hτY : τ ∈ layerY (nfGrp gensA2) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hτ, ?_⟩
    rw [← hτeq]
    exact h1
  have hτY' : τ ∈ (xorSpan [2, 48, 304, 268, 271]).toFinset := by
    simpa [layers_A2.2.2.1] using hτY
  have hY2' : colsAct xT9 τ ∈ (xorSpan [2, 48, 304, 268, 271]).toFinset := by
    simpa [layers_A2.2.2.1] using hY2
  have hy3 : yD * h * yD⁻¹ ∈ nfGrp gensA4' := by
    obtain ⟨n, hn, hfn⟩ := Subgroup.mem_map.1 h3
    have hconj : yD * h * yD⁻¹ = n := by
      rw [← hfn]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hconj]
    exact hn
  have hY3 : colsAct yT9 τ ∈ layerY (nfGrp gensA4') := by
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (colsAct_lt yT9_bound τ), ?_⟩
    rw [← yD_conj_tD hτ, ← hτeq]
    exact hy3
  have hY3' : colsAct yT9 τ ∈ (xorSpan [284, 48, 63, 288, 2]).toFinset := by
    simpa [layers_A4'.2.2.1] using hY3
  have hτ4 : τ < 4 :=
    tau_check τ (List.mem_range.2 hτ) (by simpa using hτY') (by simpa using hY2')
      (by simpa using hY3')
  rw [hτeq]
  interval_cases τ <;> simp

theorem card_iInf_t8A : Nat.card (⨅ i, t8A i : Subgroup Dfull) ≤ 4 := by
  have hsub : ((⨅ i, t8A i : Subgroup Dfull) : Set Dfull) ⊆
      ({tD 0, tD 1, tD 2, tD 3} : Set Dfull) := by
    intro h hh
    rcases mem_iInf_t8A hh with rfl | rfl | rfl | rfl <;> simp
  change Nat.card (((⨅ i, t8A i : Subgroup Dfull) : Set Dfull)) ≤ 4
  rw [Nat.card_coe_set_eq]
  refine (Set.ncard_le_ncard hsub).trans ?_
  have h0 := Set.ncard_insert_le (tD 0) ({tD 1, tD 2, tD 3} : Set Dfull)
  have h1 := Set.ncard_insert_le (tD 1) ({tD 2, tD 3} : Set Dfull)
  have h2 := Set.ncard_insert_le (tD 2) ({tD 3} : Set Dfull)
  have h3 : ({tD 3} : Set Dfull).ncard = 1 := Set.ncard_singleton _
  change (insert (tD 0) (insert (tD 1) (insert (tD 2) {tD 3}) : Set Dfull)).ncard ≤ 4
  omega

theorem exists_four_elemAbelian :
    ∃ (S : Subgroup Dfull) (A : Fin 4 → Subgroup Dfull), S ≤ Jhat ∧ IsPGroup 2 S ∧
      (∀ i, A i ≤ S ∧ IsElemAbelian 2 (A i) ∧ Nat.card (A i) = 2 ^ 14) ∧
      Nat.card (⨅ i, A i : Subgroup Dfull) ≤ 4 :=
  ⟨flagS, t8A, flagS_le_Jhat, isPGroup_flagS,
    fun i => ⟨t8A_le_flagS i, t8A_isElemAbelian i, t8A_card i⟩, card_iInf_t8A⟩

end CFSG.Monster.B.TwoA.Sp8.WordRel
