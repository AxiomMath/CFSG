module

public import Certificates.Kernel.Co2.Words
public import CFSG.Certificates.Kernel.Orders.Co2.RelsBind
public import CFSG.Certificates.Kernel.Co2.Bound3.Rels
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelCo2

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE

abbrev P : TauCeti.GroupPresentation := TauCeti.Sporadic.co2Presentation

noncomputable abbrev tg : ℕ → PresentedGroup P.relatorSet := pgen P.relatorSet

theorem gens_eq : P.generatorCount = 2 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.co2Presentation_generatorNames]

theorem rel_val : ∀ r < 10, bval tg (wWord (Co2B.rel r)) (wLen (Co2B.rel r)) = 1 := by
  have hl := Co2B.relatorLetters_ent
  have hb : ∀ w ∈ P.relatorLetters, (∀ l ∈ w, l.1 < 127) ∧ w.length < 1024 := by
    rw [CFSG.KD.OrdCo2.rels_eq]
    decide
  have hlen : (P.relatorLetters.map Co2B.ent).length = 10 := by rw [hl]; rfl
  intro r hr
  have e : Co2B.rel r = (P.relatorLetters.map Co2B.ent)[r]'(by omega) := by
    rw [List.getElem_of_eq hl]
    interval_cases r <;> rfl
  rw [e, List.getElem_map]
  have hm := List.getElem_mem (l := P.relatorLetters) (n := r) (by
    rw [List.length_map] at hlen
    omega)
  rw [bval_ent _ _ (hb _ hm).1 (hb _ hm).2]
  exact swd_relatorLetters P _ hm

theorem beq_false {r i : ℕ} (h : i < r) : Nat.beq r i = false :=
  Bool.eq_false_iff.mpr fun h' => by
    have := Nat.eq_of_beq_eq_true h'
    omega

theorem rel_ge {r : ℕ} (h : 10 ≤ r) : Co2B.rel r = 0 := by
  simp only [Co2B.rel, beq_false (r := r) (i := nat_lit 0) (Nat.lt_of_lt_of_le (by decide) h), beq_false (r := r) (i := nat_lit 1) (Nat.lt_of_lt_of_le (by decide) h),
    beq_false (r := r) (i := nat_lit 2) (Nat.lt_of_lt_of_le (by decide) h), beq_false (r := r) (i := nat_lit 3) (Nat.lt_of_lt_of_le (by decide) h),
    beq_false (r := r) (i := nat_lit 4) (Nat.lt_of_lt_of_le (by decide) h), beq_false (r := r) (i := nat_lit 5) (Nat.lt_of_lt_of_le (by decide) h),
    beq_false (r := r) (i := nat_lit 6) (Nat.lt_of_lt_of_le (by decide) h), beq_false (r := r) (i := nat_lit 7) (Nat.lt_of_lt_of_le (by decide) h),
    beq_false (r := r) (i := nat_lit 8) (Nat.lt_of_lt_of_le (by decide) h), beq_false (r := r) (i := nat_lit 9) (Nat.lt_of_lt_of_le (by decide) h)]

theorem sub_ge {r : ℕ} (h : 7 ≤ r) : Co2B.sub r = 0 := by
  simp only [Co2B.sub, beq_false (r := r) (i := nat_lit 0) (Nat.lt_of_lt_of_le (by decide) h), beq_false (r := r) (i := nat_lit 1) (Nat.lt_of_lt_of_le (by decide) h),
    beq_false (r := r) (i := nat_lit 2) (Nat.lt_of_lt_of_le (by decide) h), beq_false (r := r) (i := nat_lit 3) (Nat.lt_of_lt_of_le (by decide) h),
    beq_false (r := r) (i := nat_lit 4) (Nat.lt_of_lt_of_le (by decide) h), beq_false (r := r) (i := nat_lit 5) (Nat.lt_of_lt_of_le (by decide) h),
    beq_false (r := r) (i := nat_lit 6) (Nat.lt_of_lt_of_le (by decide) h)]

theorem gen_ge {r : ℕ} (h : 6 ≤ r) : Co2K.gen r = 0 := by
  simp only [Co2K.gen, beq_false (r := r) (i := nat_lit 1) (Nat.lt_of_lt_of_le (by decide) h), beq_false (r := r) (i := nat_lit 2) (Nat.lt_of_lt_of_le (by decide) h),
    beq_false (r := r) (i := nat_lit 3) (Nat.lt_of_lt_of_le (by decide) h), beq_false (r := r) (i := nat_lit 4) (Nat.lt_of_lt_of_le (by decide) h),
    beq_false (r := r) (i := nat_lit 5) (Nat.lt_of_lt_of_le (by decide) h)]

theorem bval_nil {G : Type*} [Group G] (gen : ℕ → G) : bval gen (wWord 0) (wLen 0) = 1 := rfl

theorem rel_norm : relsNorm Co2B.rel (nat_lit 10) = true := by quickRfl

theorem rel_all : ∀ r, wWord (Co2B.rel r) < 2 ^ (8 * wLen (Co2B.rel r)) ∧
    bval tg (wWord (Co2B.rel r)) (wLen (Co2B.rel r)) = 1 := by
  intro r
  by_cases hr : r < 10
  · exact ⟨relsNorm_spec rel_norm r hr, rel_val r hr⟩
  · rw [rel_ge (by omega)]
    exact ⟨by decide, rfl⟩

theorem a_sq : tg 0 * tg 0 = 1 := by
  have h := rel_val 0 (by norm_num)
  have e : Co2B.rel 0 = 8 := rfl
  rw [e, show wWord 8 = 0 from rfl, show wLen 8 = 2 from rfl, bval_succ, bval_succ] at h
  simpa [letV, wLet_eq, bval] using h

end CertificateChecks.KernelCo2

end
