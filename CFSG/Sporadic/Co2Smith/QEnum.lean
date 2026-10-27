module

public import CFSG.Sporadic.Co2Smith.S0Enum

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Certificates.ExtraspecialNF
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] noncomputable def qElt
    (e : ℕ) : K := nf z0 hE ((e / 256 : ℕ) : ZMod 2) (bitVec (e % 256))

theorem qElt_mem (e : ℕ) : qElt e ∈ Qsub := nf_mem_closure z0 hE _ _

theorem qElt_val {e : ℕ} (he : e < 512) :
    (qElt e).val.val = rowsMatrix 22 (Native.nfRows seedRowsArr hR (e / 256) (e % 256)) := by
  rw [qElt, nf_val]
  congr 2
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by omega)

theorem exists_qElt
    {q : K} (hq : q ∈ Qsub) : ∃ e < 512, qElt e = q := by
  obtain ⟨s, u, rfl⟩ := (mem_closure_iff hE_rel).mp hq
  obtain ⟨w, hw, rfl⟩ := exists_bitVec u
  refine ⟨s.val * 256 + w, ?_, ?_⟩
  · have := ZMod.val_lt s
    omega
  · rw [qElt, show (s.val * 256 + w) / 256 = s.val by omega,
      show (s.val * 256 + w) % 256 = w by omega, ZMod.natCast_zmod_val]

theorem bitVec_injOn {v w : ℕ} (hv : v < 256) (hw : w < 256) (h : bitVec v = bitVec w) :
    v = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have := congrFun h ⟨i, hi⟩
    simp only [bitVec] at this
    by_cases h1 : v.testBit i <;> by_cases h2 : w.testBit i <;> simp_all
  · rw [Nat.testBit_eq_false_of_lt (by
      calc v < 256 := hv
        _ = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)),
      Nat.testBit_eq_false_of_lt (by
      calc w < 256 := hw
        _ = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))]

theorem qElt_injOn
    {e e' : ℕ} (he : e < 512) (he' : e' < 512) (h : qElt e = qElt e') :
    e = e' := by
  have h2 := nf_injective (a₁ := (((e / 256 : ℕ) : ZMod 2), bitVec (e % 256)))
    (a₂ := (((e' / 256 : ℕ) : ZMod 2), bitVec (e' % 256))) h
  simp only [Prod.mk.injEq] at h2
  have h3 : e / 256 = e' / 256 := by
    have := congrArg ZMod.val h2.1
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
  have h4 := bitVec_injOn (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h2.2
  omega

@[expose] noncomputable def cElt (e n : ℕ) : K := sElt n * qElt e

theorem cElt_mem
    (e n : ℕ) : cElt e n ∈ Cz :=
  Cz.mul_mem (S0_le_Cz (sElt_mem_S0 n)) (Qsub_le_Cz (qElt_mem e))

theorem exists_cElt
    {g : K} (hg : g ∈ Cz) : ∃ e < 512, ∃ n < 1451520, cElt e n = g := by
  obtain ⟨s, hs, q, hq, rfl⟩ := exists_mul_eq hg
  obtain ⟨n, hn, rfl⟩ := exists_sElt hs
  obtain ⟨e, he, rfl⟩ := exists_qElt hq
  exact ⟨e, he, n, hn, rfl⟩

theorem cElt_injOn
    {e e' n n' : ℕ} (he : e < 512) (he' : e' < 512) (hn : n < 1451520)
    (hn' : n' < 1451520) (h : cElt e n = cElt e' n') : e = e' ∧ n = n' := by
  have h2 := prodMap_injective (a₁ := (⟨sElt n, sElt_mem_S0 n⟩, ⟨qElt e, qElt_mem e⟩))
    (a₂ := (⟨sElt n', sElt_mem_S0 n'⟩, ⟨qElt e', qElt_mem e'⟩)) (Subtype.ext h)
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h2
  exact ⟨qElt_injOn he he' h2.2, sElt_injOn hn hn' h2.1⟩

end CFSG.Sporadic.Co2Smith
