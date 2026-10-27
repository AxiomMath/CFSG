module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.PermData
public import Certificates.Certificate1383001

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native


@[expose] noncomputable def plusRefl (i : Fin 60) : Equiv.Perm (Fin 60) :=
  permOfArr 60 plusTable[(i : ℕ)]!

@[expose] def plusPerm : Subgroup (Equiv.Perm (Fin 60)) := Subgroup.closure (Set.range plusRefl)

@[expose] def plusClass : Set plusPerm := {x | ∃ i, (x : Equiv.Perm (Fin 60)) = plusRefl i}

private theorem s11p1_table_parts :
    plusTableSizeCheck () = true ∧ plusTableValidCheck () = true ∧
      plusTableInvolCheck () = true ∧ plusTableConjCheck () = true ∧
      plusTableKeyCheck () = true := by
  have h := Certificates.certificate1383001.1
  simp only [plusTableCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem s11p1_size : plusTable.size = 60 := by
  have h := s11p1_table_parts.1
  simp only [plusTableSizeCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

private theorem s11p1_valid {i : ℕ} (hi : i < 60) : validA 60 plusTable[i]! = true := by
  have h := s11p1_table_parts.2.1
  simp only [plusTableValidCheck] at h
  exact allLt_spec h (i := i) hi

private theorem s11p1_invol {i j : ℕ} (hi : i < 60) (hj : j < 60) :
    (plusTable[i]!)[(plusTable[i]!)[j]!]! = j := by
  have h := s11p1_table_parts.2.2.1
  simp only [plusTableInvolCheck] at h
  have hij := allLt_spec (allLt_spec h (i := i) hi) (i := j) hj
  simpa [beq_iff_eq] using hij

private theorem s11p1_conj {i j : ℕ} (hi : i < 60) (hj : j < 60) :
    eqA 60 plusTable[(plusTable[i]!)[j]!]!
      (compA 60 plusTable[i]! (compA 60 plusTable[j]! plusTable[i]!)) = true := by
  have h := s11p1_table_parts.2.2.2.1
  simp only [plusTableConjCheck] at h
  exact allLt_spec (allLt_spec h (i := i) hi) (i := j) hj

private theorem s11p1_key {i j : ℕ} (hi : i < 60) (hj : j < 60) :
    ((keyA 60 plusBase plusTable[i]! == keyA 60 plusBase plusTable[j]!) == (i == j)) = true := by
  have h := s11p1_table_parts.2.2.2.2
  simp only [plusTableKeyCheck] at h
  exact allLt_spec (allLt_spec h (i := i) hi) (i := j) hj

private theorem s11p1_enumOK : enumOK 60 plusTable plusBase (plusEnum ()) = true := by
  have h := Certificates.certificate1383001.2
  simp only [plusEnumCheck, Bool.and_eq_true] at h
  exact h.1

private theorem s11p1_enum_size : (plusEnum ()).pts.size = 7200 := by
  have h := Certificates.certificate1383001.2
  simp only [plusEnumCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private theorem s11p1_base_lt : ∀ p ∈ plusBase, p < 60 := by
  simp [plusBase]

private theorem s11p1_permsA : permsA 60 plusTable = Set.range plusRefl := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, by simpa [s11p1_size] using hk⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(i : ℕ), by rw [s11p1_size]; exact i.isLt, rfl⟩

theorem plusRefl_apply (i j : Fin 60) :
    ((plusRefl i j : Fin 60) : ℕ) = (plusTable[(i : ℕ)]!)[(j : ℕ)]! := by
  exact ((rep_of_validA (n := 60) (a := plusTable[(i : ℕ)]!) (s11p1_valid i.isLt)) j).symm

theorem plusRefl_injective : Function.Injective plusRefl := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hkey : keyA 60 plusBase plusTable[(i : ℕ)]! = keyA 60 plusBase plusTable[(j : ℕ)]! :=
    keyA_eq (n := 60) (ps := plusBase) s11p1_base_lt (s11p1_valid hi) (s11p1_valid hj)
      (by simpa [plusRefl] using hij)
  have hk := s11p1_key hi hj
  have hiff : (keyA 60 plusBase plusTable[(i : ℕ)]! ==
        keyA 60 plusBase plusTable[(j : ℕ)]!) = (i == j) :=
    beq_iff_eq.1 hk
  have htrue : (i == j) = true := by
    rw [← hiff]
    exact beq_iff_eq.2 hkey
  exact beq_iff_eq.1 htrue

theorem plusRefl_mul_self (i : Fin 60) : plusRefl i * plusRefl i = 1 := by
  ext j
  rw [Equiv.Perm.mul_apply, plusRefl_apply i (plusRefl i j), plusRefl_apply i j]
  simp only [Equiv.Perm.one_apply]
  exact s11p1_invol i.isLt j.isLt

theorem plusRefl_conj (i j : Fin 60) :
    plusRefl i * plusRefl j * (plusRefl i)⁻¹ = plusRefl (plusRefl i j) := by
  have hri : Rep 60 plusTable[(i : ℕ)]! (permOfArr 60 plusTable[(i : ℕ)]!) :=
    rep_of_validA (s11p1_valid i.isLt)
  have hrj : Rep 60 plusTable[(j : ℕ)]! (permOfArr 60 plusTable[(j : ℕ)]!) :=
    rep_of_validA (s11p1_valid j.isLt)
  have h1 : Rep 60 (compA 60 plusTable[(i : ℕ)]!
        (compA 60 plusTable[(j : ℕ)]! plusTable[(i : ℕ)]!))
      (plusRefl i * plusRefl j * plusRefl i) := by
    rw [mul_assoc]
    exact rep_compA hri (rep_compA hrj hri)
  have h2 : Rep 60 plusTable[(plusRefl i j : Fin 60).val]!
      (permOfArr 60 plusTable[(plusRefl i j : Fin 60).val]!) :=
    rep_of_validA (s11p1_valid (plusRefl i j).isLt)
  have hconj : eqA 60 plusTable[(plusRefl i j : Fin 60).val]!
      (compA 60 plusTable[(i : ℕ)]! (compA 60 plusTable[(j : ℕ)]! plusTable[(i : ℕ)]!)) =
        true := by
    rw [plusRefl_apply i j]
    exact s11p1_conj i.isLt j.isLt
  have hgoal : plusRefl i * plusRefl j * plusRefl i = plusRefl (plusRefl i j) :=
    Rep.unique h1 (rep_of_eqA (n := 60) h2 hconj)
  have hinv : (plusRefl i)⁻¹ = plusRefl i := inv_eq_of_mul_eq_one_right (plusRefl_mul_self i)
  rw [hinv, hgoal]

theorem plusRefl_mem (i : Fin 60) : plusRefl i ∈ plusPerm :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem conj_plusRefl {g : Equiv.Perm (Fin 60)} (hg : g ∈ plusPerm) (k : Fin 60) :
    g * plusRefl k * g⁻¹ = plusRefl (g k) := by
  revert k
  unfold plusPerm at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact plusRefl_conj i
  | one => intro k; simp
  | mul a b ha hb iha ihb =>
    intro k
    have e : (a * b) * plusRefl k * (a * b)⁻¹ = a * (b * plusRefl k * b⁻¹) * a⁻¹ := by
      group
    rw [e, ihb k, iha (b k), Equiv.Perm.mul_apply]
  | inv a ha iha =>
    intro k
    have h := iha (a⁻¹ k)
    have hk : a (a⁻¹ k) = k := by simp
    rw [hk] at h
    calc a⁻¹ * plusRefl k * a = a⁻¹ * (a * plusRefl (a⁻¹ k) * a⁻¹) * a := by rw [← h]
      _ = plusRefl (a⁻¹ k) := by group

theorem commute_plusRefl_iff (i j : Fin 60) :
    Commute (plusRefl i) (plusRefl j) ↔ plusRefl i j = j := by
  have h : Commute (plusRefl i) (plusRefl j) ↔
      plusRefl i * plusRefl j * (plusRefl i)⁻¹ = plusRefl j := by
    rw [commute_iff_eq, mul_inv_eq_iff_eq_mul]
  rw [h, plusRefl_conj i j, plusRefl_injective.eq_iff]

theorem plusEnum_spec :
    (∀ x, x ∈ plusPerm ↔ ∃ i < (plusEnum ()).pts.size, permOfArr 60 (plusEnum ()).pts[i]! = x) ∧
      (plusEnum ()).pts.size = 7200 ∧
      ∀ i < (plusEnum ()).pts.size, validA 60 (plusEnum ()).pts[i]! = true := by
  obtain ⟨hmem, -, hvalid⟩ :=
    enumOK_spec (n := 60) (gs := plusTable) (ps := plusBase) (c := plusEnum ())
      s11p1_base_lt s11p1_enumOK
  refine ⟨?_, s11p1_enum_size, hvalid⟩
  intro x
  rw [plusPerm, ← s11p1_permsA]
  exact hmem x

theorem card_plusPerm : Nat.card plusPerm = 7200 := by
  obtain ⟨-, hcard, -⟩ :=
    enumOK_spec (n := 60) (gs := plusTable) (ps := plusBase) (c := plusEnum ())
      s11p1_base_lt s11p1_enumOK
  rw [plusPerm, ← s11p1_permsA, hcard, s11p1_enum_size]

end CFSG.OddTranspositions.PartThree
