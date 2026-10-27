module

public import CFSG.Sporadic.Co1I301.Elements
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo1Nat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
import CFSG.Sporadic.Co1Patterson.GraphCover
import CFSG.Certificates.ExtraspecialNormalForm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1I301

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.Co1Patterson CFSG.Sporadic.Co1Patterson.Native CFSG.Sporadic.Co1I301.Native
  CFSG.Sporadic.Co1.Module CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301 CFSG.LocalAnalysis.GLTheoremA.H301B
open CFSG.Blueprint (NativeSporadic.Co1)


private theorem mem_centralizer_of_mem_twoAQNC {x : NativeSporadic.Co1} (hx : x ∈ twoAQNC) :
    x ∈ centralizer ({aNC} : Set NativeSporadic.Co1) :=
  mem_centralizer_aNC_iff.2 (Subgroup.mem_inf.1 (twoAQ_le (show nativeEmb x ∈ twoAQ from hx))).2

private theorem mem_co1R_iff {x : NativeSporadic.Co1} : x ∈ co1R ↔ x ∈ twoAQNC := by
  rw [co1R, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro hx
    exact ⟨⟨x, mem_centralizer_of_mem_twoAQNC hx⟩, hx, rfl⟩

private theorem aNC_mem_twoAQNC : aNC ∈ twoAQNC := by
  show nativeEmb aNC ∈ twoAQ
  rw [nativeEmb_aNC]
  exact aG_mem_twoAQ

private theorem mem_rowR0Of_iff {x : NativeSporadic.Co1} :
    x ∈ rowR0Of dC co1R ↔ x ∈ twoAQNC ∧ x * dC = dC * x := by
  rw [rowR0Of, Subgroup.mem_inf, mem_co1R_iff]
  exact and_congr_right fun _ =>
    @Subgroup.mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance dC x

private theorem chkR0_parts :
    CFSG.Sporadic.Co1.TwoBNative.gtOK (r0Gens ()) (r0Tree ()) = true ∧
      (r0Tree ()).pts.size = 128 ∧
      (∀ i < 6, (commR (rRw i) (dRw ()) = true ∧ qPts.contains (rRw i) = true) ∧
        Native.mul (rRw i) (rRw i) = Native.one) ∧
      (∀ x ∈ twoAQTree.pts, commR x (dRw ()) = true → (r0Set ()).contains x = true) ∧
      ∀ i j : Fin 6, Native.mul (rRw i) (rRw j) =
        Native.mul (Native.mul (rRw j) (rRw i)) (if cR i j = 1 then aRw else Native.one) := by
  have h := co1RowCheck_parts.2.2.2.2.1
  simp only [chkR0, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.mem_finRange, true_implies, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, fun x hx hc => ?_, h5⟩
  have h6 := h4 x hx
  rw [hc] at h6
  simpa using h6

private theorem rRw_valid {i : ℕ} (hi : i < 6) :
    CFSG.Sporadic.Co1.InvNative.validRows (rRw i) = true :=
  cEl_valid (j := 27 + i) (by omega) (by omega)

private theorem dRw_valid : CFSG.Sporadic.Co1.InvNative.validRows (dRw ()) = true :=
  cEl_valid (j := 21) (by norm_num) (by norm_num)

private theorem rC_mem_twoAQNC {i : ℕ} (hi : i < 6) : rC i ∈ twoAQNC :=
  (mem_twoAQNC_iff_contains (nrep_rC i) (rRw_valid hi)).2 (chkR0_parts.2.2.1 i hi).1.2

private theorem rC_comm_dC {i : ℕ} (hi : i < 6) : rC i * dC = dC * rC i :=
  commute_of_nrep (nrep_rC i) nrep_dC (chkR0_parts.2.2.1 i hi).1.1

private theorem commR_of_comm {Y : Native.Rows} {y : NativeSporadic.Co1} (hY : NRep Y y)
    (hv : CFSG.Sporadic.Co1.InvNative.validRows Y = true) (h : y * dC = dC * y) :
    commR Y (dRw ()) = true := by
  have h1 := hY.mul nrep_dC
  have h2 := nrep_dC.mul hY
  rw [h] at h1
  exact beq_iff_eq.2 (NRep.rows_eq h1 h2 (validRows_mul hv dRw_valid) (validRows_mul dRw_valid hv))

private noncomputable def gen0 (l : ℕ) : NativeSporadic.Co1 := if l = 0 then aNC else rC (l - 1)

private noncomputable def R0S : Subgroup NativeSporadic.Co1 :=
  Subgroup.closure (insert aNC (Set.range fun i : Fin 6 => rC (i : ℕ)))

private theorem r0Gens_size : (r0Gens ()).size = 7 := by simp [r0Gens]

private theorem cons_map_range_getElem! {α : Type} [Inhabited α] (a : α) (f : ℕ → α) {n l : ℕ}
    (hl : l < n) : (a :: (List.range n).map f).toArray[l + 1]! = f l := by
  simp [hl]

private theorem r0Gens_zero : (r0Gens ())[0]! = aRw := by simp [r0Gens]

private theorem r0Gens_succ {l : ℕ} (hl : l < 6) : (r0Gens ())[l + 1]! = rRw l :=
  cons_map_range_getElem! aRw rRw hl

private theorem gen0_zero : gen0 0 = aNC := by simp [gen0]

private theorem gen0_succ (l : ℕ) : gen0 (l + 1) = rC l := by simp [gen0]

private theorem nrep_gen0 :
    ∀ l < (r0Gens ()).size, matHom (gen0 l) = rowsMatrix 24 (r0Gens ())[l]! := by
  intro l hl
  rcases l with _ | l
  · rw [r0Gens_zero, gen0_zero]
    exact nrep_aC
  · have hl6 : l < 6 := by rw [r0Gens_size] at hl; omega
    rw [r0Gens_succ hl6, gen0_succ]
    exact nrep_rC l

private theorem image_gen0 :
    gen0 '' {l | l < (r0Gens ()).size} = insert aNC (Set.range fun i : Fin 6 => rC (i : ℕ)) := by
  rw [r0Gens_size]
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_range]
  constructor
  · rintro ⟨l, hl, rfl⟩
    by_cases h0 : l = 0
    · left
      rw [h0, gen0_zero]
    · right
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
      exact ⟨⟨k, by omega⟩, (gen0_succ k).symm⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, by norm_num, gen0_zero⟩
    · have := i.isLt
      exact ⟨i + 1, by omega, gen0_succ i⟩

private theorem mem_R0S_of_contains {Y : Native.Rows} {y : NativeSporadic.Co1} (hY : NRep Y y)
    (h : (r0Set ()).contains Y = true) : y ∈ R0S := by
  haveI := CFSG.Sporadic.Co1.Module.finite_co1
  obtain ⟨f, hf, -, heq⟩ := CFSG.Sporadic.Co1.Module.TwoB.gtOK_closure_eq chkR0_parts.1 gen0
    nrep_gen0
  unfold r0Set at h
  rw [Std.HashSet.contains_ofList, List.contains_iff_mem, Array.mem_toList_iff,
    Array.mem_iff_getElem] at h
  obtain ⟨i, hi, hie⟩ := h
  have hy : f i = y := by
    apply matHom_injective
    rw [hf i hi, getElem!_pos _ i hi, hie]
    exact hY.symm
  have hmem : y ∈ (Subgroup.closure (gen0 '' {l | l < (r0Gens ()).size}) :
      Set NativeSporadic.Co1) := by
    rw [heq]
    exact ⟨i, hi, hy⟩
  rw [image_gen0] at hmem
  exact hmem

private theorem exists_nrep (x : NativeSporadic.Co1) :
    ∃ Y : Native.Rows, NRep Y x ∧ CFSG.Sporadic.Co1.InvNative.validRows Y = true := by
  have h : ∀ i : Fin 24, ∃ n : ℕ, n < 2 ^ 24 ∧ toVecD 24 n = matHom x i := by
    intro i
    have hmem : matHom x i ∈ toVecD 24 '' Set.Iio (2 ^ 24) := by
      rw [toVecD_image_Iio]
      trivial
    obtain ⟨n, hn, e⟩ := hmem
    exact ⟨n, hn, e⟩
  choose n hn he using h
  refine ⟨Array.ofFn n, ?_, ?_⟩
  · unfold NRep
    ext i j
    rw [rowsMatrix_apply, Array.getElem?_ofFn]
    simp [i.isLt, he i]
  · simp only [CFSG.Sporadic.Co1.InvNative.validRows, Bool.and_eq_true, beq_iff_eq,
      Array.all_eq_true_iff_forall_mem, decide_eq_true_eq]
    refine ⟨Array.size_ofFn, fun r hr => ?_⟩
    obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hr
    exact hn i

private theorem R0S_le : R0S ≤ rowR0Of dC co1R := by
  rw [R0S, Subgroup.closure_le]
  rintro x (rfl | ⟨i, rfl⟩)
  · exact mem_rowR0Of_iff.2 ⟨aNC_mem_twoAQNC, dC_comm_aNC.symm⟩
  · exact mem_rowR0Of_iff.2 ⟨rC_mem_twoAQNC i.isLt, rC_comm_dC i.isLt⟩

private theorem contains_of_mem {Y : Native.Rows} {y : NativeSporadic.Co1} (hY : NRep Y y)
    (hv : CFSG.Sporadic.Co1.InvNative.validRows Y = true) (hy : y ∈ rowR0Of dC co1R) :
    (r0Set ()).contains Y = true := by
  obtain ⟨hyQ, hyd⟩ := mem_rowR0Of_iff.1 hy
  have hq := (mem_twoAQNC_iff_contains hY hv).1 hyQ
  refine chkR0_parts.2.2.2.1 Y ?_ (commR_of_comm hY hv hyd)
  unfold qPts at hq
  rwa [Std.HashSet.contains_ofList, List.contains_iff_mem, Array.mem_toList_iff] at hq

private theorem le_R0S : rowR0Of dC co1R ≤ R0S := by
  intro x hx
  obtain ⟨Y, hY, hv⟩ := exists_nrep x
  exact mem_R0S_of_contains hY (contains_of_mem hY hv hx)

private theorem rowR0Of_eq : rowR0Of dC co1R = R0S := le_antisymm le_R0S R0S_le

theorem mem_rowR0_iff {Y : Native.Rows} {y : NativeSporadic.Co1} (hY : NRep Y y)
    (hv : CFSG.Sporadic.Co1.InvNative.validRows Y = true) :
    y ∈ rowR0Of dC co1R ↔ (r0Set ()).contains Y = true :=
  ⟨contains_of_mem hY hv, fun h => R0S_le (mem_R0S_of_contains hY h)⟩

theorem card_rowR0 : Nat.card (rowR0Of dC co1R) = 2 ^ 7 := by
  haveI := CFSG.Sporadic.Co1.Module.finite_co1
  have h := CFSG.Sporadic.Co1.Module.TwoB.gtOK_card chkR0_parts.1 gen0 nrep_gen0
  rw [image_gen0, chkR0_parts.2.1] at h
  rw [rowR0Of_eq]
  exact h.trans (by norm_num)

section Extraspecial

open CFSG.Certificates

private theorem rC_comm_aNC {i : ℕ} (hi : i < 6) : aNC * rC i = rC i * aNC :=
  ((@Subgroup.mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance aNC (rC i)).1
    (mem_centralizer_of_mem_twoAQNC (rC_mem_twoAQNC hi))).symm

private theorem rC_mul_self {i : ℕ} (hi : i < 6) : rC i * rC i = 1 :=
  eq_one_of_nrep ((nrep_rC i).mul (nrep_rC i)) (chkR0_parts.2.2.1 i hi).2

private theorem comm_of_rows {Ri Rj Ra : Native.Rows} {xi xj a : NativeSporadic.Co1}
    (hi : NRep Ri xi) (hj : NRep Rj xj) (ha : NRep Ra a) {b : ZMod 2}
    (h : Native.mul Ri Rj = Native.mul (Native.mul Rj Ri) (if b = 1 then Ra else Native.one)) :
    xi * xj = xj * xi * a ^ b.val := by
  have hrep : NRep (Native.mul (Native.mul Rj Ri) (if b = 1 then Ra else Native.one))
      (xj * xi * (if b = 1 then a else 1)) := by
    refine (hj.mul hi).mul ?_
    split_ifs
    exacts [ha, NRep.one']
  rw [← h] at hrep
  rw [eq_of_nrep (hi.mul hj) hrep]
  rcases ExtraspecialNF.zmod_two_cases b with h0 | h1
  · subst h0
    rw [if_neg (by decide), ZMod.val_zero, pow_zero]
  · subst h1
    rw [if_pos rfl, ExtraspecialNF.val_one_two, pow_one]

private theorem rC_comm_rC (i j : Fin 6) :
    rC i * rC j = rC j * rC i * aNC ^ (cR i j).val :=
  comm_of_rows (nrep_rC i) (nrep_rC j) nrep_aC (chkR0_parts.2.2.2.2 i j)

private theorem rel_r0 : ExtraspecialNF.Rel aNC (fun i : Fin 6 => rC (i : ℕ)) cR where
  z_sq := by
    have h := pow_orderOf_eq_one aNC
    rwa [orderOf_aNC, sq] at h
  z_comm := fun i => rC_comm_aNC i.isLt
  q_sq := fun i => rC_mul_self i.isLt
  comm := rC_comm_rC

private theorem cR_nondegenerate : ExtraspecialNF.Nondegenerate cR := by decide

private theorem card_R0S : Nat.card R0S = 2 ^ 7 := by
  rw [← rowR0Of_eq]
  exact card_rowR0

private theorem nf_injective :
    Function.Injective (Function.uncurry (ExtraspecialNF.nf aNC (fun i : Fin 6 => rC (i : ℕ)))) :=
  ExtraspecialNF.injective_of_card_ge rel_r0 (le_of_eq card_R0S.symm)

theorem rowR0_extraspecial : IsExtraSpec2 (rowR0Of dC co1R) := by
  rw [rowR0Of_eq]
  obtain ⟨h2, hc, hf, hz⟩ :=
    ExtraspecialNF.isExtraspecialPGroup rel_r0 nf_injective cR_nondegenerate (by norm_num)
  exact ⟨h2, hc.trans hf.symm, hf, hz⟩

theorem centerOf_rowR0 : centerOf (rowR0Of dC co1R) = Subgroup.zpowers aNC := by
  rw [rowR0Of_eq]
  exact ExtraspecialNF.map_center_eq rel_r0 nf_injective cR_nondegenerate

end Extraspecial

end CFSG.Sporadic.Co1I301
