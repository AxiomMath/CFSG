module

public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.Th

open Native

theorem parAll_eq_true_of {n chunks : ℕ} {p : ℕ → Bool} (h : ∀ i < n, p i = true) :
    parAll n chunks p = true := by
  unfold parAll
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply]
  intro j hj
  change allStep j (chunks + 1) n p = true
  unfold allStep
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨k, hk⟩ _
  apply h
  have hcpos : 0 < chunks + 1 := Nat.succ_pos _
  have hle := (Nat.le_div_iff_mul_le hcpos).1 (Nat.succ_le_of_lt hk)
  have e : (k + 1) * (chunks + 1) = (chunks + 1) * k + (chunks + 1) := by ring
  rw [e] at hle
  generalize (chunks + 1) * k = X at hle ⊢
  omega

theorem parAll_chunks (n c c' : ℕ) (p : ℕ → Bool) : parAll n c p = parAll n c' p :=
  Bool.eq_iff_iff.mpr ⟨fun h => parAll_eq_true_of (parAll_eq_true h),
    fun h => parAll_eq_true_of (parAll_eq_true h)⟩

theorem orbitOK_chunks (tA tB : Array V4) (w : Key) (st : BFSState) (c c' : ℕ) :
    orbitOK tA tB w st c = orbitOK tA tB w st c' := by
  unfold orbitOK
  rw [parAll_chunks _ c c']

theorem globalChecks_chunks (n : ℕ) (alpha beta betaInv gpl : Table) (ch : Chain) (c c' : ℕ) :
    globalChecks n alpha beta betaInv gpl ch c = globalChecks n alpha beta betaInv gpl ch c' := by
  unfold globalChecks
  rw [parAll_chunks _ c c', parAll_chunks _ c c']

theorem tableChecks_chunks (n : ℕ) (alpha beta betaInv gpl : Table) (c c' : ℕ) :
    tableChecks n alpha beta betaInv gpl c = tableChecks n alpha beta betaInv gpl c' := by
  unfold tableChecks
  simp only [globalChecks_chunks _ _ _ _ _ _ c c', parAll_chunks _ c c']

theorem thCertificate_chunks (c c' : ℕ) : thCertificate c = thCertificate c' := by
  unfold thCertificate
  simp only [orbitOK_chunks _ _ _ _ c c', tableChecks_chunks _ _ _ _ _ c c']

end CFSG.Sporadic.Th
