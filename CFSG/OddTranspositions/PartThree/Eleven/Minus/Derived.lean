module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Perm
public import Certificates.Certificate1383008

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CFSG.QuasithinUnique.Id2519.HSAut

@[expose] def minusL : Subgroup minusPerm := minusLPerm.subgroupOf minusPerm

private theorem derived_check_parts :
    minusLGensCheck () = true ∧ minusLEnumCheck (minusLEnum ()) = true ∧
      minusLSizeCheck (minusLEnum ()) = true ∧ minusLReflCheck (minusLEnum ()) = true ∧
      minusLCentralCheck (minusEnum ()) = true ∧ minusLTransCheck (minusEnum ()) = true ∧
      minusLLocalCheck (minusLEnum ()) = true := by
  have h := Certificates.certificate1383008.1
  simp only [minusDerivedCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem gens_check : minusLGensCheck () = true := derived_check_parts.1

private theorem enum_check : minusLEnumCheck (minusLEnum ()) = true := derived_check_parts.2.1

private theorem refl_check : minusLReflCheck (minusLEnum ()) = true := derived_check_parts.2.2.2.1

private theorem central_check : minusLCentralCheck (minusEnum ()) = true :=
  derived_check_parts.2.2.2.2.1

private theorem trans_check : minusLTransCheck (minusEnum ()) = true :=
  derived_check_parts.2.2.2.2.2.1

private theorem local_check : minusLLocalCheck (minusLEnum ()) = true :=
  derived_check_parts.2.2.2.2.2.2

private theorem class_fact : ∃ e : Fin minusLSizes.size ≃ ConjClasses minusLPerm,
    (∀ l, Nat.card (e l).carrier = minusLSizes[l.val]!) ∧
      ∃ l₀ : Fin minusLSizes.size, l₀.val = 0 ∧ e l₀ = ConjClasses.mk 1 :=
  Certificates.certificate1383008.2

private theorem minusBase_lt : ∀ p ∈ minusBase, p < 65 := by simp [minusBase]

private theorem table_valid {i : ℕ} (hi : i < 65) : validA 65 minusTable[i]! = true := by
  have h := Certificates.certificate1383006.1
  simp only [minusTableCheck, Bool.and_eq_true] at h
  exact allLt_spec h.1.1.1.2 (i := i) hi

private theorem gens_size : minusLGens.size = 5 := by
  have h := gens_check
  simp only [minusLGensCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1

private theorem gens_valid {k : ℕ} (hk : k < 5) : validA 65 minusLGens[k]! = true := by
  have h := gens_check
  simp only [minusLGensCheck, Bool.and_eq_true] at h
  exact allLt_spec h.1.1.1.1.1.2 (i := k) hk

private theorem gens_eqA0 :
    eqA 65 minusLGens[0]! (compA 65 minusTable[0]! minusTable[1]!) = true := by
  have h := gens_check
  simp only [minusLGensCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

private theorem gens_eqA1 :
    eqA 65 minusLGens[1]! (compA 65 minusTable[0]! minusTable[3]!) = true := by
  have h := gens_check
  simp only [minusLGensCheck, Bool.and_eq_true] at h
  exact h.1.1.1.2

private theorem gens_eqA2 :
    eqA 65 minusLGens[2]! (compA 65 minusTable[0]! minusTable[4]!) = true := by
  have h := gens_check
  simp only [minusLGensCheck, Bool.and_eq_true] at h
  exact h.1.1.2

private theorem gens_eqA3 :
    eqA 65 minusLGens[3]! (compA 65 minusTable[0]! minusTable[10]!) = true := by
  have h := gens_check
  simp only [minusLGensCheck, Bool.and_eq_true] at h
  exact h.1.2

private theorem gens_eqA4 :
    eqA 65 minusLGens[4]! (compA 65 minusTable[0]! minusTable[11]!) = true := by
  have h := gens_check
  simp only [minusLGensCheck, Bool.and_eq_true] at h
  exact h.2

private theorem enumOK_minusL : enumOK 65 minusLGens minusBase (minusLEnum ()) = true := by
  have h := enum_check
  simp only [minusLEnumCheck, Bool.and_eq_true] at h
  exact h.1

private theorem enum_size : (minusLEnum ()).pts.size = 7800 := by
  have h := enum_check
  simp only [minusLEnumCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private theorem refl_eq_check {j i : ℕ} (hj : j < (minusLEnum ()).pts.size) (hi : i < 65) :
    eqA 65 ((minusLEnum ()).pts[j]!) minusTable[i]! = false := by
  have h := refl_check
  simp only [minusLReflCheck] at h
  have h2 := allLt_spec h (i := j) hj
  have h3 := allLt_spec h2 (i := i) hi
  simpa using h3

private theorem central_or {i : ℕ} (hi : i < (minusEnum ()).pts.size) :
    (!(allLt minusLGens.size fun k =>
        eqA 65 (compA 65 ((minusEnum ()).pts[i]!) minusLGens[k]!)
          (compA 65 minusLGens[k]! ((minusEnum ()).pts[i]!))) ||
      eqA 65 ((minusEnum ()).pts[i]!) (idA 65)) = true := by
  have h := central_check
  simp only [minusLCentralCheck] at h
  exact allLt_spec h (i := i) hi

private theorem trans_any {i : ℕ} (hi : i < 65) :
    ((List.range (minusEnum ()).pts.size).any fun j =>
      ((minusEnum ()).pts[j]!)[0]! == i) = true := by
  have h := trans_check
  simp only [minusLTransCheck] at h
  exact allLt_spec h (i := i) hi

private def lsB1 : Finset (Fin 15) := {1, 2}
private def lsBmid : Finset (Fin 15) := {4, 5, 6, 7, 8, 9}
private def lsBtop : Finset (Fin 15) := {10, 11, 12, 13, 14}

private def lsW (l : Fin 15) : ℕ :=
  (if l = 0 then 1 else 0) + 312 * (if l ∈ lsB1 then 1 else 0) +
    325 * (if l = 3 then 1 else 0) + 600 * (if l ∈ lsBmid then 1 else 0) +
    650 * (if l ∈ lsBtop then 1 else 0)

private theorem lsW_eq : ∀ l : Fin 15, minusLSizes[l.val]! = lsW l := by decide

private theorem sum_lsW (U : Finset (Fin 15)) :
    (∑ l ∈ U, lsW l) =
      (U.filter (· = 0)).card + 312 * (U.filter (· ∈ lsB1)).card +
      325 * (U.filter (· = 3)).card + 600 * (U.filter (· ∈ lsBmid)).card +
      650 * (U.filter (· ∈ lsBtop)).card := by
  simp only [lsW, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter]

private theorem count_dvd (a b c d : ℕ) (ha : a ≤ 2) (hb : b ≤ 1) (hc : c ≤ 6) (hd : d ≤ 5)
    (h : (1 + 312 * a + 325 * b + 600 * c + 650 * d) ∣ 7800) :
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (a = 2 ∧ b = 1 ∧ c = 6 ∧ d = 5) := by
  have hbounded : ∀ a' : Fin 3, ∀ b' : Fin 2, ∀ c' : Fin 7, ∀ d' : Fin 6,
      (1 + 312 * a'.val + 325 * b'.val + 600 * c'.val + 650 * d'.val) ∣ 7800 →
      (a'.val = 0 ∧ b'.val = 0 ∧ c'.val = 0 ∧ d'.val = 0) ∨
        (a'.val = 2 ∧ b'.val = 1 ∧ c'.val = 6 ∧ d'.val = 5) := by decide
  exact hbounded ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, by omega⟩ h

private theorem hsums_minusLSizes :
    ∀ U : Finset (Fin 15), (0 : Fin 15) ∈ U →
      (∑ l ∈ U, minusLSizes[l.val]!) ∣ 7800 → U = {0} ∨ U = Finset.univ := by
  intro U h0 hdvd
  have hW : (∑ l ∈ U, minusLSizes[l.val]!) = (∑ l ∈ U, lsW l) :=
    Finset.sum_congr rfl fun l _ => lsW_eq l
  rw [hW, sum_lsW] at hdvd
  have h0card : (U.filter (· = 0)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h.symm ▸ h0, h⟩
  rw [h0card] at hdvd
  have ha_le : (U.filter (· ∈ lsB1)).card ≤ 2 := by
    have := Finset.card_le_card (show U.filter (· ∈ lsB1) ⊆ lsB1 from
      fun x hx => (Finset.mem_filter.1 hx).2)
    simpa [lsB1] using this
  have hb_le : (U.filter (· = 3)).card ≤ 1 := by
    have := Finset.card_le_card (show U.filter (· = 3) ⊆ ({3} : Finset (Fin 15)) from
      fun x hx => by simpa using (Finset.mem_filter.1 hx).2)
    simpa using this
  have hc_le : (U.filter (· ∈ lsBmid)).card ≤ 6 := by
    have := Finset.card_le_card (show U.filter (· ∈ lsBmid) ⊆ lsBmid from
      fun x hx => (Finset.mem_filter.1 hx).2)
    simpa [lsBmid] using this
  have hd_le : (U.filter (· ∈ lsBtop)).card ≤ 5 := by
    have := Finset.card_le_card (show U.filter (· ∈ lsBtop) ⊆ lsBtop from
      fun x hx => (Finset.mem_filter.1 hx).2)
    simpa [lsBtop] using this
  rcases count_dvd _ _ _ _ ha_le hb_le hc_le hd_le hdvd with
    ⟨ha0, hb0, hc0, hd0⟩ | ⟨ha2, hb2, hc2, hd2⟩
  · left
    have hB1e : U.filter (· ∈ lsB1) = ∅ := Finset.card_eq_zero.1 ha0
    have hB3e : U.filter (· = 3) = ∅ := Finset.card_eq_zero.1 hb0
    have hBme : U.filter (· ∈ lsBmid) = ∅ := Finset.card_eq_zero.1 hc0
    have hBte : U.filter (· ∈ lsBtop) = ∅ := Finset.card_eq_zero.1 hd0
    have hnotB1 : ∀ x, x ∈ U → x ∉ lsB1 := by
      intro x hx hx1
      have hmem : x ∈ U.filter (· ∈ lsB1) := Finset.mem_filter.2 ⟨hx, hx1⟩
      rw [hB1e] at hmem
      simpa using hmem
    have hnotB3 : ∀ x, x ∈ U → x ≠ 3 := by
      intro x hx hx3
      have hmem : x ∈ U.filter (· = 3) := Finset.mem_filter.2 ⟨hx, hx3⟩
      rw [hB3e] at hmem
      simpa using hmem
    have hnotBm : ∀ x, x ∈ U → x ∉ lsBmid := by
      intro x hx hxm
      have hmem : x ∈ U.filter (· ∈ lsBmid) := Finset.mem_filter.2 ⟨hx, hxm⟩
      rw [hBme] at hmem
      simpa using hmem
    have hnotBt : ∀ x, x ∈ U → x ∉ lsBtop := by
      intro x hx hxt
      have hmem : x ∈ U.filter (· ∈ lsBtop) := Finset.mem_filter.2 ⟨hx, hxt⟩
      rw [hBte] at hmem
      simpa using hmem
    apply Finset.Subset.antisymm
    · intro x hx
      fin_cases x
      · simp
      · exact absurd (by decide : (1 : Fin 15) ∈ lsB1) (hnotB1 1 hx)
      · exact absurd (by decide : (2 : Fin 15) ∈ lsB1) (hnotB1 2 hx)
      · exact absurd rfl (hnotB3 3 hx)
      · exact absurd (by decide : (4 : Fin 15) ∈ lsBmid) (hnotBm 4 hx)
      · exact absurd (by decide : (5 : Fin 15) ∈ lsBmid) (hnotBm 5 hx)
      · exact absurd (by decide : (6 : Fin 15) ∈ lsBmid) (hnotBm 6 hx)
      · exact absurd (by decide : (7 : Fin 15) ∈ lsBmid) (hnotBm 7 hx)
      · exact absurd (by decide : (8 : Fin 15) ∈ lsBmid) (hnotBm 8 hx)
      · exact absurd (by decide : (9 : Fin 15) ∈ lsBmid) (hnotBm 9 hx)
      · exact absurd (by decide : (10 : Fin 15) ∈ lsBtop) (hnotBt 10 hx)
      · exact absurd (by decide : (11 : Fin 15) ∈ lsBtop) (hnotBt 11 hx)
      · exact absurd (by decide : (12 : Fin 15) ∈ lsBtop) (hnotBt 12 hx)
      · exact absurd (by decide : (13 : Fin 15) ∈ lsBtop) (hnotBt 13 hx)
      · exact absurd (by decide : (14 : Fin 15) ∈ lsBtop) (hnotBt 14 hx)
    · intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      exact h0
  · right
    have hB1sub : lsB1 ⊆ U := by
      have hcard : (U.filter (· ∈ lsB1)).card = lsB1.card := by rw [ha2]; decide
      have heq : U.filter (· ∈ lsB1) = lsB1 :=
        Finset.eq_of_subset_of_card_le
          (fun x hx => (Finset.mem_filter.1 hx).2) (by rw [hcard])
      intro x hx
      have : x ∈ U.filter (· ∈ lsB1) := by rw [heq]; exact hx
      exact (Finset.mem_filter.1 this).1
    have h3sub : (3 : Fin 15) ∈ U := by
      have hcard : (U.filter (· = 3)).card = ({3} : Finset (Fin 15)).card := by
        rw [hb2]; decide
      have heq : U.filter (· = 3) = {3} :=
        Finset.eq_of_subset_of_card_le
          (fun x hx => by simpa using (Finset.mem_filter.1 hx).2) (by rw [hcard])
      have : (3 : Fin 15) ∈ U.filter (· = 3) := by rw [heq]; simp
      exact (Finset.mem_filter.1 this).1
    have hBmsub : lsBmid ⊆ U := by
      have hcard : (U.filter (· ∈ lsBmid)).card = lsBmid.card := by rw [hc2]; decide
      have heq : U.filter (· ∈ lsBmid) = lsBmid :=
        Finset.eq_of_subset_of_card_le
          (fun x hx => (Finset.mem_filter.1 hx).2) (by rw [hcard])
      intro x hx
      have : x ∈ U.filter (· ∈ lsBmid) := by rw [heq]; exact hx
      exact (Finset.mem_filter.1 this).1
    have hBtsub : lsBtop ⊆ U := by
      have hcard : (U.filter (· ∈ lsBtop)).card = lsBtop.card := by rw [hd2]; decide
      have heq : U.filter (· ∈ lsBtop) = lsBtop :=
        Finset.eq_of_subset_of_card_le
          (fun x hx => (Finset.mem_filter.1 hx).2) (by rw [hcard])
      intro x hx
      have : x ∈ U.filter (· ∈ lsBtop) := by rw [heq]; exact hx
      exact (Finset.mem_filter.1 this).1
    apply Finset.eq_univ_iff_forall.2
    intro x
    fin_cases x
    · exact h0
    · exact hB1sub (by decide)
    · exact hB1sub (by decide)
    · exact h3sub
    · exact hBmsub (by decide)
    · exact hBmsub (by decide)
    · exact hBmsub (by decide)
    · exact hBmsub (by decide)
    · exact hBmsub (by decide)
    · exact hBmsub (by decide)
    · exact hBtsub (by decide)
    · exact hBtsub (by decide)
    · exact hBtsub (by decide)
    · exact hBtsub (by decide)
    · exact hBtsub (by decide)

private theorem hsums_transport {n : ℕ} (hn : n = 15)
    (h : ∀ U : Finset (Fin 15), (0 : Fin 15) ∈ U →
      (∑ l ∈ U, minusLSizes[l.val]!) ∣ 7800 → U = {0} ∨ U = Finset.univ) :
    ∀ l₀ : Fin n, l₀.val = 0 → ∀ U : Finset (Fin n), l₀ ∈ U →
      (∑ l ∈ U, minusLSizes[l.val]!) ∣ 7800 → U = {l₀} ∨ U = Finset.univ := by
  subst hn
  intro l₀ hl₀ U hU hdvd
  have hz : l₀ = 0 := Fin.ext hl₀
  rw [hz] at hU ⊢
  exact h U hU hdvd

private theorem gens_mem (k : Fin 5) : permOfArr 65 minusLGens[k.val]! ∈ minusPerm := by
  have hmem0 : minusRefl (0 : Fin 65) ∈ minusPerm := Subgroup.subset_closure ⟨0, rfl⟩
  have hmem : ∀ i : Fin 65, minusRefl i ∈ minusPerm := fun i =>
    Subgroup.subset_closure ⟨i, rfl⟩
  have hrep (j : Fin 65) : Rep 65 minusTable[j.val]! (minusRefl j) := by
    simp only [minusRefl]
    exact rep_of_validA (table_valid j.isLt)
  fin_cases k
  · have hr : Rep 65 minusLGens[0]! (permOfArr 65 minusLGens[0]!) :=
      rep_of_validA (gens_valid (by norm_num))
    have hc : Rep 65 (compA 65 minusTable[0]! minusTable[1]!) (minusRefl 0 * minusRefl 1) :=
      rep_compA (hrep 0) (hrep 1)
    have he := (eqA_iff hr hc).1 gens_eqA0
    rw [he]
    exact mul_mem (hmem 0) (hmem 1)
  · have hr : Rep 65 minusLGens[1]! (permOfArr 65 minusLGens[1]!) :=
      rep_of_validA (gens_valid (by norm_num))
    have hc : Rep 65 (compA 65 minusTable[0]! minusTable[3]!) (minusRefl 0 * minusRefl 3) :=
      rep_compA (hrep 0) (hrep 3)
    have he := (eqA_iff hr hc).1 gens_eqA1
    rw [he]
    exact mul_mem (hmem 0) (hmem 3)
  · have hr : Rep 65 minusLGens[2]! (permOfArr 65 minusLGens[2]!) :=
      rep_of_validA (gens_valid (by norm_num))
    have hc : Rep 65 (compA 65 minusTable[0]! minusTable[4]!) (minusRefl 0 * minusRefl 4) :=
      rep_compA (hrep 0) (hrep 4)
    have he := (eqA_iff hr hc).1 gens_eqA2
    rw [he]
    exact mul_mem (hmem 0) (hmem 4)
  · have hr : Rep 65 minusLGens[3]! (permOfArr 65 minusLGens[3]!) :=
      rep_of_validA (gens_valid (by norm_num))
    have hc : Rep 65 (compA 65 minusTable[0]! minusTable[10]!) (minusRefl 0 * minusRefl 10) :=
      rep_compA (hrep 0) (hrep 10)
    have he := (eqA_iff hr hc).1 gens_eqA3
    rw [he]
    exact mul_mem (hmem 0) (hmem 10)
  · have hr : Rep 65 minusLGens[4]! (permOfArr 65 minusLGens[4]!) :=
      rep_of_validA (gens_valid (by norm_num))
    have hc : Rep 65 (compA 65 minusTable[0]! minusTable[11]!) (minusRefl 0 * minusRefl 11) :=
      rep_compA (hrep 0) (hrep 11)
    have he := (eqA_iff hr hc).1 gens_eqA4
    rw [he]
    exact mul_mem (hmem 0) (hmem 11)

theorem minusLPerm_le_minusPerm : minusLPerm ≤ minusPerm := by
  rw [minusLPerm, Subgroup.closure_le]
  rintro x ⟨k, hk, rfl⟩
  have hk5 : k < 5 := by rwa [gens_size] at hk
  exact gens_mem ⟨k, hk5⟩

theorem card_minusLPerm : Nat.card minusLPerm = 7800 := by
  obtain ⟨-, hcard, -⟩ := enumOK_spec (n := 65) (gs := minusLGens) (ps := minusBase)
    (c := minusLEnum ()) minusBase_lt enumOK_minusL
  rw [minusLPerm, hcard, enum_size]

theorem card_minusL : Nat.card minusL = 7800 := by
  rw [minusL]
  calc Nat.card (minusLPerm.subgroupOf minusPerm)
      = Nat.card minusLPerm :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe minusLPerm_le_minusPerm).toEquiv
    _ = 7800 := card_minusLPerm

theorem index_minusL : minusL.index = 2 := by
  have h := Subgroup.index_mul_card (G := minusPerm) (H := minusL)
  rw [card_minusL, card_minusPerm] at h
  generalize hk : minusL.index = k at h ⊢
  omega

theorem minusL_normal : minusL.Normal := Subgroup.normal_of_index_eq_two index_minusL

private theorem trans_index (i : Fin 65) :
    ∃ j < (minusEnum ()).pts.size,
      permOfArr 65 ((minusEnum ()).pts[j]!) 0 = i := by
  have h := trans_any i.isLt
  rw [List.any_eq_true] at h
  obtain ⟨j, hj, hji⟩ := h
  have hj' : j < (minusEnum ()).pts.size := List.mem_range.1 hj
  refine ⟨j, hj', ?_⟩
  have hrep : Rep 65 ((minusEnum ()).pts[j]!) (permOfArr 65 ((minusEnum ()).pts[j]!)) :=
    rep_of_validA ((minusEnum_spec.2.2) j hj')
  have h0 : ((minusEnum ()).pts[j]!)[0]! = (i : ℕ) := by simpa using hji
  apply Fin.ext
  have hz : (0 : Fin 65) = ⟨0, by norm_num⟩ := Fin.ext rfl
  rw [hz, ← hrep ⟨0, by norm_num⟩, h0]

theorem isSimpleGroup_minusLPerm : IsSimpleGroup minusLPerm := by
  obtain ⟨e, he, l₀, hl₀0, hl₀⟩ := class_fact
  refine isSimpleGroup_of_classes e (fun l => minusLSizes[l.val]!) he l₀ hl₀
    (by rw [card_minusLPerm]; norm_num) ?_
  rw [card_minusLPerm]
  exact hsums_transport (by decide) hsums_minusLSizes l₀ hl₀0

theorem isSimpleGroup_minusL : IsSimpleGroup minusL := by
  letI : IsSimpleGroup minusLPerm := isSimpleGroup_minusLPerm
  exact (Subgroup.subgroupOfEquivOfLe minusLPerm_le_minusPerm).isSimpleGroup

theorem minusRefl_not_mem_minusLPerm (i : Fin 65) : minusRefl i ∉ minusLPerm := by
  intro hmem
  obtain ⟨hmem', -, hval⟩ := enumOK_spec (n := 65) (gs := minusLGens) (ps := minusBase)
    (c := minusLEnum ()) minusBase_lt enumOK_minusL
  obtain ⟨j, hj, hjeq⟩ := (hmem' (minusRefl i)).1 hmem
  have hfalse := refl_eq_check hj i.isLt
  have hr : Rep 65 ((minusLEnum ()).pts[j]!) (permOfArr 65 ((minusLEnum ()).pts[j]!)) :=
    rep_of_validA (hval j hj)
  have hc : Rep 65 minusTable[i.val]! (minusRefl i) := by
    simp only [minusRefl]
    exact rep_of_validA (table_valid i.isLt)
  have htrue : eqA 65 ((minusLEnum ()).pts[j]!) minusTable[i.val]! = true :=
    (eqA_iff hr hc).2 hjeq
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

theorem not_mem_minusL_of_mem_minusClass {x : minusPerm} (hx : x ∈ minusClass) : x ∉ minusL := by
  obtain ⟨i, hi⟩ := hx
  intro hxL
  have hxL' : (x : Equiv.Perm (Fin 65)) ∈ minusLPerm := hxL
  rw [hi] at hxL'
  exact minusRefl_not_mem_minusLPerm i hxL'

theorem centralizer_minusL : Subgroup.centralizer (minusL : Set minusPerm) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨hmemM, -, hvalM⟩ := minusEnum_spec
  obtain ⟨i, hi, hzi⟩ := (hmemM z).1 z.2
  have hcomm : ∀ k : Fin 5,
      permOfArr 65 minusLGens[k.val]! * (z : Equiv.Perm (Fin 65)) =
        (z : Equiv.Perm (Fin 65)) * permOfArr 65 minusLGens[k.val]! := by
    intro k
    have hmemL : permOfArr 65 minusLGens[k.val]! ∈ minusLPerm :=
      Subgroup.subset_closure (mem_permsA (n := 65) (gs := minusLGens) (k := k.val)
        (by rw [gens_size]; exact k.isLt))
    let h : minusPerm := ⟨permOfArr 65 minusLGens[k.val]!, minusLPerm_le_minusPerm hmemL⟩
    have hhL : h ∈ minusL := hmemL
    have hh := hz h hhL
    have := congrArg (Subtype.val) hh
    simpa [h] using this
  have hcommk : ∀ k < minusLGens.size,
      eqA 65 (compA 65 ((minusEnum ()).pts[i]!) minusLGens[k]!)
        (compA 65 minusLGens[k]! ((minusEnum ()).pts[i]!)) = true := by
    intro k hk
    have hk5 : k < 5 := by rwa [gens_size] at hk
    have hr1 : Rep 65 (compA 65 ((minusEnum ()).pts[i]!) minusLGens[k]!)
        (permOfArr 65 ((minusEnum ()).pts[i]!) * permOfArr 65 minusLGens[k]!) :=
      rep_compA (rep_of_validA (hvalM i hi)) (rep_of_validA (gens_valid hk5))
    have hr2 : Rep 65 (compA 65 minusLGens[k]! ((minusEnum ()).pts[i]!))
        (permOfArr 65 minusLGens[k]! * permOfArr 65 ((minusEnum ()).pts[i]!)) :=
      rep_compA (rep_of_validA (gens_valid hk5)) (rep_of_validA (hvalM i hi))
    refine (eqA_iff hr1 hr2).2 ?_
    rw [hzi]
    exact (hcomm ⟨k, hk5⟩).symm
  have hgenall : allLt minusLGens.size
      (fun k => eqA 65 (compA 65 ((minusEnum ()).pts[i]!) minusLGens[k]!)
        (compA 65 minusLGens[k]! ((minusEnum ()).pts[i]!))) = true :=
    allLt_iff.2 hcommk
  have hor := central_or hi
  rw [hgenall] at hor
  simp only [Bool.not_true, Bool.false_or] at hor
  have hz1 : z = 1 := by
    have heq : permOfArr 65 ((minusEnum ()).pts[i]!) = 1 :=
      (eqA_iff (rep_of_validA (hvalM i hi)) (rep_idA (n := 65))).1 hor
    apply Subtype.ext
    show (z : Equiv.Perm (Fin 65)) = 1
    rw [← hzi, heq]
  exact hz1

theorem minusClass_eq_setOf_isConj :
    minusClass = {g | IsConj (⟨minusRefl 0, minusRefl_mem 0⟩ : minusPerm) g} := by
  ext g
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj, h0i⟩ := trans_index i
    have hgmem : permOfArr 65 ((minusEnum ()).pts[j]!) ∈ minusPerm :=
      (minusEnum_spec.1 _).2 ⟨j, hj, rfl⟩
    refine isConj_iff.2 ⟨⟨permOfArr 65 ((minusEnum ()).pts[j]!), hgmem⟩, ?_⟩
    apply Subtype.ext
    show (permOfArr 65 ((minusEnum ()).pts[j]!) * minusRefl (0 : Fin 65) *
        (permOfArr 65 ((minusEnum ()).pts[j]!))⁻¹) = (g : Equiv.Perm (Fin 65))
    rw [conj_minusRefl hgmem 0, h0i]
    exact hi.symm
  · intro hg
    obtain ⟨c, hc⟩ := isConj_iff.1 hg
    refine ⟨(c : Equiv.Perm (Fin 65)) 0, ?_⟩
    have h1 : (g : Equiv.Perm (Fin 65)) =
        (c : Equiv.Perm (Fin 65)) * minusRefl (0 : Fin 65) *
          (c : Equiv.Perm (Fin 65))⁻¹ := by
      have := congrArg (Subtype.val) hc
      simpa using this.symm
    calc (g : Equiv.Perm (Fin 65))
        = (c : Equiv.Perm (Fin 65)) * minusRefl (0 : Fin 65) *
            (c : Equiv.Perm (Fin 65))⁻¹ := h1
      _ = minusRefl ((c : Equiv.Perm (Fin 65)) 0) := conj_minusRefl c.2 0

private theorem local_mem_of_any {arr : Array ℕ}
    (hany : (minusLEnum ()).pts.toList.any (eqA 65 arr) = true)
    (hval : validA 65 arr = true) : permOfArr 65 arr ∈ minusLPerm :=
  enumOK_mem_of_any (n := 65) (gs := minusLGens) (ps := minusBase) (c := minusLEnum ())
    minusBase_lt enumOK_minusL (rep_of_validA hval) hany

theorem minusLocal_mem : permOfArr 65 minusSylowA ∈ minusLPerm ∧
    permOfArr 65 minusSylowB ∈ minusLPerm ∧
    permOfArr 65 minusA5Gens[0]! ∈ minusLPerm ∧ permOfArr 65 minusA5Gens[1]! ∈ minusLPerm := by
  have h := local_check
  simp only [minusLLocalCheck, Bool.and_eq_true] at h
  exact ⟨local_mem_of_any h.1.1.1.1.1.1.1 h.1.1.1.2,
    local_mem_of_any h.1.1.1.1.1.1.2 h.1.1.2,
    local_mem_of_any h.1.1.1.1.1.2 h.1.2,
    local_mem_of_any h.1.1.1.1.2 h.2⟩

end CFSG.OddTranspositions.PartThree
