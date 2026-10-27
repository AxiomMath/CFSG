module

public import CFSG.Monster.B.CTIB.Rep4371Rho
public import CFSG.Monster.B.Rep4371.Glue
public import CFSG.Monster.B.Rep4371.RBasis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.SpinLattice
  CFSG.Monster.Spin CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.Rep4371

theorem linearIndependent_RrawA :
    LinearIndependent ℚ (fun k : Fin 23 => Rraw k) := by
  have h := (linearIndependent_Rraw octDataOK_true).comp (fun k : Fin 23 => (⟨k, by omega⟩ :
    Fin 4371)) (fun k k' h => Fin.ext (by simpa using congrArg Fin.val h))
  exact h

theorem linearIndependent_RrawT :
    LinearIndependent ℚ (fun t : Fin 2048 => Rraw (2323 + t)) := by
  have h := (linearIndependent_Rraw octDataOK_true).comp
    (fun t : Fin 2048 => (⟨2323 + t, by omega⟩ :
    Fin 4371)) (fun t t' h => Fin.ext (by have := congrArg Fin.val h; simp only at this; omega))
  exact h

theorem Across_eq_span :
    Across isShortCoord_rStar = Submodule.span ℚ (Set.range fun k : Fin 23 => Rraw k) :=
  le_antisymm Across_le_span (Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact Rraw_mem_Across (by omega)))

theorem Tplus_eq_span :
    Tplus isShortCoord_rStar = Submodule.span ℚ (Set.range fun t : Fin 2048 => Rraw (2323 + t)) :=
  le_antisymm Tplus_le_span (Submodule.span_le.2 (by
    rintro _ ⟨t, rfl⟩
    exact Rraw_mem_Tplus (by omega)))

theorem finrank_Across :
    Module.finrank ℚ (Across isShortCoord_rStar) = 23 := by
  rw [Across_eq_span, finrank_span_eq_card linearIndependent_RrawA, Fintype.card_fin]

theorem finrank_Xdiff :
    Module.finrank ℚ (Xdiff isShortCoord_rStar) = 2300 := by
  rw [← (xdiff_Rraw octDataOK_true).2.1,
    finrank_span_eq_card (xdiff_Rraw octDataOK_true).1, Fintype.card_fin]

theorem finrank_Tplus :
    Module.finrank ℚ (Tplus isShortCoord_rStar) = 2048 := by
  rw [Tplus_eq_span, finrank_span_eq_card linearIndependent_RrawT, Fintype.card_fin]

theorem disjoint_blocks_A : Disjoint blockA (blockX ⊔ blockW) := by
  rw [Submodule.disjoint_def]
  intro v hA hXW
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.1 hXW
  have h1 : (x + w).1 = 0 := by simp [hx.1, hw.1]
  exact Prod.ext h1 (Prod.ext hA.1 hA.2)

theorem disjoint_blocks_X : Disjoint blockX (blockA ⊔ blockW) := by
  rw [Submodule.disjoint_def]
  intro v hX hAW
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.1 hAW
  have h1 : (x + w).2.1 = 0 := by simp [hx.1, hw.2]
  exact Prod.ext hX.1 (Prod.ext h1 hX.2)

theorem disjoint_blocks_W : Disjoint blockW (blockA ⊔ blockX) := by
  rw [Submodule.disjoint_def]
  intro v hW hAX
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.1 hAX
  have h1 : (x + w).2.2 = 0 := by simp [hx.2, hw.2]
  exact Prod.ext hW.1 (Prod.ext hW.2 h1)

theorem iSupIndep_three {M : Type*} [AddCommGroup M] [Module ℚ M] {A B C : Submodule ℚ M}
    (h1 : Disjoint A (B ⊔ C)) (h2 : Disjoint B (A ⊔ C)) (h3 : Disjoint C (A ⊔ B)) :
    iSupIndep ![A, B, C] := by
  intro i
  fin_cases i
  · refine h1.mono_right (iSup₂_le fun j hj => ?_)
    fin_cases j
    · exact absurd rfl hj
    · exact le_sup_left
    · exact le_sup_right
  · refine h2.mono_right (iSup₂_le fun j hj => ?_)
    fin_cases j
    · exact le_sup_left
    · exact absurd rfl hj
    · exact le_sup_right
  · refine h3.mono_right (iSup₂_le fun j hj => ?_)
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
    · exact absurd rfl hj

theorem iSupIndep_summands :
    iSupIndep ![Across isShortCoord_rStar, Xdiff isShortCoord_rStar, Tplus isShortCoord_rStar] :=
  iSupIndep_three
    (disjoint_blocks_A.mono Across_le_blockA (sup_le_sup Xdiff_le_blockX Tplus_le_blockW))
    (disjoint_blocks_X.mono Xdiff_le_blockX (sup_le_sup Across_le_blockA Tplus_le_blockW))
    (disjoint_blocks_W.mono Tplus_le_blockW (sup_le_sup Across_le_blockA Xdiff_le_blockX))

theorem Vst_eq_sup :
    Vst = Across isShortCoord_rStar ⊔ Xdiff isShortCoord_rStar ⊔ Tplus isShortCoord_rStar :=
  V4_eq_sup isShortCoord_rStar

theorem Across_le_Vst : Across isShortCoord_rStar ≤ Vst := by
  rw [Vst_eq_sup]
  exact le_sup_left.trans le_sup_left

theorem Xdiff_le_Vst : Xdiff isShortCoord_rStar ≤ Vst := by
  rw [Vst_eq_sup]
  exact le_sup_right.trans le_sup_left

theorem Tplus_le_Vst : Tplus isShortCoord_rStar ≤ Vst := by
  rw [Vst_eq_sup]
  exact le_sup_right

theorem finrank_V23 : Module.finrank ℚ V23 = 23 :=
  (Submodule.comapSubtypeEquivOfLe Across_le_Vst).finrank_eq.trans finrank_Across

theorem finrank_V2300 : Module.finrank ℚ V2300 = 2300 :=
  (Submodule.comapSubtypeEquivOfLe Xdiff_le_Vst).finrank_eq.trans finrank_Xdiff

theorem finrank_V2048 : Module.finrank ℚ V2048 = 2048 :=
  (Submodule.comapSubtypeEquivOfLe Tplus_le_Vst).finrank_eq.trans finrank_Tplus

theorem iSupIndep_comap_subtype {M : Type*} [AddCommGroup M] [Module ℚ M] (N : Submodule ℚ M)
    {ι : Type*} {p : ι → Submodule ℚ M} (h : iSupIndep p) :
    iSupIndep fun i => (p i).comap N.subtype := by
  intro i
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have hle : (⨆ j, ⨆ (_ : j ≠ i), (p j).comap N.subtype) ≤
      (⨆ j, ⨆ (_ : j ≠ i), p j).comap N.subtype :=
    iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => p j) j hj)
  exact Subtype.ext (Submodule.disjoint_def.1 (h i) _ hv (hle hv'))

theorem iSupIndep_V : iSupIndep ![V23, V2300, V2048] := by
  have h := iSupIndep_comap_subtype Vst iSupIndep_summands
  convert h using 1
  funext i
  fin_cases i <;> rfl

theorem sup_V : V23 ⊔ V2300 ⊔ V2048 = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have hv' := hv
  rw [Vst_eq_sup] at hv'
  obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hv'
  obtain ⟨a, ha, x, hx, rfl⟩ := Submodule.mem_sup.1 hy
  have e : (⟨a + x + t, hv⟩ : Vst) =
      ⟨a, Across_le_Vst ha⟩ + ⟨x, Xdiff_le_Vst hx⟩ + ⟨t, Tplus_le_Vst ht⟩ := rfl
  rw [e]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.mem_sup_left ha))
    (Submodule.mem_sup_left (Submodule.mem_sup_right hx))) (Submodule.mem_sup_right ht)

end CFSG.Monster.B.CTIB
