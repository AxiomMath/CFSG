module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.PermData
public import Certificates.Certificate1383006

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native


@[expose] noncomputable def minusRefl (i : Fin 65) : Equiv.Perm (Fin 65) :=
  permOfArr 65 minusTable[(i : ℕ)]!

@[expose] def minusPerm : Subgroup (Equiv.Perm (Fin 65)) := Subgroup.closure (Set.range minusRefl)

@[expose] def minusClass : Set minusPerm := {x | ∃ i, (x : Equiv.Perm (Fin 65)) = minusRefl i}

private theorem minusPerm_table_parts :
    minusTableSizeCheck () = true ∧ minusTableValidCheck () = true ∧
      minusTableInvolCheck () = true ∧ minusTableConjCheck () = true ∧
      minusTableKeyCheck () = true := by
  have h := Certificates.certificate1383006.1
  simp only [minusTableCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem minusPerm_size : minusTable.size = 65 := by
  have h := minusPerm_table_parts.1
  simp only [minusTableSizeCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

private theorem minusPerm_valid {i : ℕ} (hi : i < 65) : validA 65 minusTable[i]! = true := by
  have h := minusPerm_table_parts.2.1
  simp only [minusTableValidCheck] at h
  exact allLt_spec h (i := i) hi

private theorem minusPerm_invol {i j : ℕ} (hi : i < 65) (hj : j < 65) :
    (minusTable[i]!)[(minusTable[i]!)[j]!]! = j := by
  have h := minusPerm_table_parts.2.2.1
  simp only [minusTableInvolCheck] at h
  have hij := allLt_spec (allLt_spec h (i := i) hi) (i := j) hj
  simpa [beq_iff_eq] using hij

private theorem minusPerm_conj {i j : ℕ} (hi : i < 65) (hj : j < 65) :
    eqA 65 minusTable[(minusTable[i]!)[j]!]!
      (compA 65 minusTable[i]! (compA 65 minusTable[j]! minusTable[i]!)) = true := by
  have h := minusPerm_table_parts.2.2.2.1
  simp only [minusTableConjCheck] at h
  exact allLt_spec (allLt_spec h (i := i) hi) (i := j) hj

private theorem minusPerm_key {i j : ℕ} (hi : i < 65) (hj : j < 65) :
    ((keyA 65 minusBase minusTable[i]! == keyA 65 minusBase minusTable[j]!) == (i == j)) =
      true := by
  have h := minusPerm_table_parts.2.2.2.2
  simp only [minusTableKeyCheck] at h
  exact allLt_spec (allLt_spec h (i := i) hi) (i := j) hj

private theorem minusPerm_enumOK : enumOK 65 minusTable minusBase (minusEnum ()) = true := by
  have h := Certificates.certificate1383006.2
  simp only [minusEnumCheck, Bool.and_eq_true] at h
  exact h.1

private theorem minusPerm_enum_size : (minusEnum ()).pts.size = 15600 := by
  have h := Certificates.certificate1383006.2
  simp only [minusEnumCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private theorem minusPerm_base_lt : ∀ p ∈ minusBase, p < 65 := by
  simp [minusBase]

private theorem minusPerm_permsA : permsA 65 minusTable = Set.range minusRefl := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, by simpa [minusPerm_size] using hk⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(i : ℕ), by rw [minusPerm_size]; exact i.isLt, rfl⟩

theorem minusRefl_apply (i j : Fin 65) :
    ((minusRefl i j : Fin 65) : ℕ) = (minusTable[(i : ℕ)]!)[(j : ℕ)]! := by
  exact ((rep_of_validA (n := 65) (a := minusTable[(i : ℕ)]!) (minusPerm_valid i.isLt)) j).symm

theorem minusRefl_injective : Function.Injective minusRefl := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hkey : keyA 65 minusBase minusTable[(i : ℕ)]! = keyA 65 minusBase minusTable[(j : ℕ)]! :=
    keyA_eq (n := 65) (ps := minusBase) minusPerm_base_lt (minusPerm_valid hi) (minusPerm_valid hj)
      (by simpa [minusRefl] using hij)
  have hk := minusPerm_key hi hj
  have hiff : (keyA 65 minusBase minusTable[(i : ℕ)]! ==
        keyA 65 minusBase minusTable[(j : ℕ)]!) = (i == j) :=
    beq_iff_eq.1 hk
  have htrue : (i == j) = true := by
    rw [← hiff]
    exact beq_iff_eq.2 hkey
  exact beq_iff_eq.1 htrue

theorem minusRefl_mul_self (i : Fin 65) : minusRefl i * minusRefl i = 1 := by
  ext j
  rw [Equiv.Perm.mul_apply, minusRefl_apply i (minusRefl i j), minusRefl_apply i j]
  simp only [Equiv.Perm.one_apply]
  exact minusPerm_invol i.isLt j.isLt

theorem minusRefl_conj (i j : Fin 65) :
    minusRefl i * minusRefl j * (minusRefl i)⁻¹ = minusRefl (minusRefl i j) := by
  have hri : Rep 65 minusTable[(i : ℕ)]! (permOfArr 65 minusTable[(i : ℕ)]!) :=
    rep_of_validA (minusPerm_valid i.isLt)
  have hrj : Rep 65 minusTable[(j : ℕ)]! (permOfArr 65 minusTable[(j : ℕ)]!) :=
    rep_of_validA (minusPerm_valid j.isLt)
  have h1 : Rep 65 (compA 65 minusTable[(i : ℕ)]!
        (compA 65 minusTable[(j : ℕ)]! minusTable[(i : ℕ)]!))
      (minusRefl i * minusRefl j * minusRefl i) := by
    rw [mul_assoc]
    exact rep_compA hri (rep_compA hrj hri)
  have h2 : Rep 65 minusTable[(minusRefl i j : Fin 65).val]!
      (permOfArr 65 minusTable[(minusRefl i j : Fin 65).val]!) :=
    rep_of_validA (minusPerm_valid (minusRefl i j).isLt)
  have hconj : eqA 65 minusTable[(minusRefl i j : Fin 65).val]!
      (compA 65 minusTable[(i : ℕ)]! (compA 65 minusTable[(j : ℕ)]! minusTable[(i : ℕ)]!)) =
        true := by
    rw [minusRefl_apply i j]
    exact minusPerm_conj i.isLt j.isLt
  have hgoal : minusRefl i * minusRefl j * minusRefl i = minusRefl (minusRefl i j) :=
    Rep.unique h1 (rep_of_eqA (n := 65) h2 hconj)
  have hinv : (minusRefl i)⁻¹ = minusRefl i := inv_eq_of_mul_eq_one_right (minusRefl_mul_self i)
  rw [hinv, hgoal]

theorem minusRefl_mem (i : Fin 65) : minusRefl i ∈ minusPerm :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem conj_minusRefl {g : Equiv.Perm (Fin 65)} (hg : g ∈ minusPerm) (k : Fin 65) :
    g * minusRefl k * g⁻¹ = minusRefl (g k) := by
  revert k
  unfold minusPerm at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact minusRefl_conj i
  | one => intro k; simp
  | mul a b ha hb iha ihb =>
    intro k
    have e : (a * b) * minusRefl k * (a * b)⁻¹ = a * (b * minusRefl k * b⁻¹) * a⁻¹ := by
      group
    rw [e, ihb k, iha (b k), Equiv.Perm.mul_apply]
  | inv a ha iha =>
    intro k
    have h := iha (a⁻¹ k)
    have hk : a (a⁻¹ k) = k := by simp
    rw [hk] at h
    calc a⁻¹ * minusRefl k * a = a⁻¹ * (a * minusRefl (a⁻¹ k) * a⁻¹) * a := by rw [← h]
      _ = minusRefl (a⁻¹ k) := by group

theorem commute_minusRefl_iff (i j : Fin 65) :
    Commute (minusRefl i) (minusRefl j) ↔ minusRefl i j = j := by
  have h : Commute (minusRefl i) (minusRefl j) ↔
      minusRefl i * minusRefl j * (minusRefl i)⁻¹ = minusRefl j := by
    rw [commute_iff_eq, mul_inv_eq_iff_eq_mul]
  rw [h, minusRefl_conj i j, minusRefl_injective.eq_iff]

theorem minusEnum_spec :
    (∀ x, x ∈ minusPerm ↔ ∃ i < (minusEnum ()).pts.size, permOfArr 65 (minusEnum ()).pts[i]! = x) ∧
      (minusEnum ()).pts.size = 15600 ∧
      ∀ i < (minusEnum ()).pts.size, validA 65 (minusEnum ()).pts[i]! = true := by
  obtain ⟨hmem, -, hvalid⟩ :=
    enumOK_spec (n := 65) (gs := minusTable) (ps := minusBase) (c := minusEnum ())
      minusPerm_base_lt minusPerm_enumOK
  refine ⟨?_, minusPerm_enum_size, hvalid⟩
  intro x
  rw [minusPerm, ← minusPerm_permsA]
  exact hmem x

theorem card_minusPerm : Nat.card minusPerm = 15600 := by
  obtain ⟨-, hcard, -⟩ :=
    enumOK_spec (n := 65) (gs := minusTable) (ps := minusBase) (c := minusEnum ())
      minusPerm_base_lt minusPerm_enumOK
  rw [minusPerm, ← minusPerm_permsA, hcard, minusPerm_enum_size]

end CFSG.OddTranspositions.PartThree
