module

public import CFSG.Sporadic.Co2Smith.GlU62Check
public import CFSG.Sporadic.Co2Smith.GlDataF0

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem u62_parts :
    Native.u62QOK = true ∧ Native.u62CommOK = true ∧ Native.u62L1OK = true ∧
      Native.u62OrbOK = true ∧ Native.u62C1OK = true := by
  have h := u62_check
  rw [Native.u62OK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

@[expose] noncomputable def u62QNFK
    (c : ℕ × ℕ × ℕ × ℕ × ℕ) : K :=
  (if c.1 == 1 then z0 else 1) * xRootK 0 c.2.1 * xRootK 1 c.2.2.1 * xRootK 2 c.2.2.2.1 *
    xRootK 3 c.2.2.2.2

theorem u62QNFK_val (c : ℕ × ℕ × ℕ × ℕ × ℕ) :
    (u62QNFK c).val.val = rowsMatrix 22 (Native.u62QNFR c) := by
  have h0 : (if c.1 == 1 then z0 else 1).val.val =
      rowsMatrix 22 (if c.1 == 1 then Native.glZ else idRows 22) := by
    split_ifs
    · exact z0_val'
    · rw [rowsMatrix_idRows]
      rfl
  unfold u62QNFK Native.u62QNFR
  rw [val_val_mul, val_val_mul, val_val_mul, val_val_mul, h0, xRootK_val, xRootK_val, xRootK_val,
    xRootK_val, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows,
    ← rowsMatrix_mulRows]

theorem hE_eq_u62QNFK
    (i : Fin 8) : hE i = u62QNFK (Native.u62QNF.getD i (0, 0, 0, 0, 0)) := by
  have h := u62_parts.1
  rw [Native.u62QOK, List.all_eq_true] at h
  have hi := beq_iff_eq.1 (h i (List.mem_range.2 i.isLt))
  have e : hE i = glElt (i + 1) := by
    change mWord Native.hWords[(i : ℕ)]! = mWord Native.glLetterWords[(i : ℕ) + 1]!
    rw [glLetterWords_hWords i i.isLt]
  rw [e]
  refine eq_of_val_rows (glElt_val (by omega)) (u62QNFK_val _) ?_
  rw [← hi, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [glRows_size]; omega),
    Option.getD_some]
  exact getElem!_pos _ _ _

theorem xRootK_of_ge {r t : ℕ} (hr : r < 4) (ht : 4 ≤ t) :
    xRootK r t = 1 := by
  rw [xRootK_eq_glE hr (by omega), getElem!_neg _ t (by rw [glPosNF_size r hr]; omega)]
  rfl

theorem comm_Qsub_of_comm_roots
    {c : K} (hz : c * z0 = z0 * c) (hr : ∀ r < 4, ∀ t < 4, c * xRootK r t = xRootK r t * c) :
    ∀ q ∈ Qsub, c * q = q * c := by
  have hle : Qsub ≤ centralizer ({c} : Set K) := by
    rw [Qsub, Subgroup.closure_le]
    rintro x (rfl | ⟨i, rfl⟩)
    · exact mem_centralizer_singleton_iff.2 hz.symm
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff, hE_eq_u62QNFK, u62QNFK]
      have hc : ∀ r < 4, ∀ t, Commute (xRootK r t) c := fun r hr' t => by
        by_cases ht : t < 4
        · exact (hr r hr' t ht).symm
        · rw [xRootK_of_ge hr' (by omega)]
          exact Commute.one_left c
      have h0 : Commute (if (Native.u62QNF.getD (↑i) (0, 0, 0, 0, 0)).1 == 1 then z0 else 1) c := by
        split_ifs
        · exact hz.symm
        · exact Commute.one_left c
      exact ((((h0.mul_left (hc 0 (by norm_num) _)).mul_left (hc 1 (by norm_num) _)).mul_left
        (hc 2 (by norm_num) _)).mul_left (hc 3 (by norm_num) _))
  intro q hq
  exact (mem_centralizer_singleton_iff.1 (hle hq)).symm

theorem x16K_x61K_ne :
    x16K * x61K ≠ x61K * x16K := by
  have h := u62_parts.2.1
  rw [Native.u62CommOK, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  intro e
  have := eq_of_rowsMatrix_eq h1 h2 (by
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← x16K_val, ← x61K_val, ← val_val_mul,
      ← val_val_mul, e])
  rw [Native.commRows, this, beq_self_eq_true] at h3
  exact absurd h3 (by decide)

end CFSG.Sporadic.Co2Smith
