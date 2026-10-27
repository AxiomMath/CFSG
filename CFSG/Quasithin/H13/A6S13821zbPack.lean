module

public import CFSG.Quasithin.H13.A6S1372L19aPack

public section

namespace CFSG.Quasithin.H13.A6.ZbPack

open Equiv CFSG.Permutation.FinPack CFSG.Quasithin.H13.L32A.C.Alt7Pack CFSG.Quasithin.H13.A6.L19aPack

@[expose] def fixK (c p : ℕ) : Bool := Nat.beq (rd c p) p

@[expose] noncomputable def p4K (c : ℕ) : Bool := Nat.beq (powK 5 e5 c 4) e5

@[expose] noncomputable def conjIK (cg cx : ℕ) : ℕ := mulK 5 (mulK 5 (invCK 5 cg) cx) cg

@[expose] noncomputable def tnK (cc cr : ℕ) : Bool :=
  p4K cr && p4K (mulK 5 cr (conjK5 cc cr)) && p4K (mulK 5 cr (conjIK cc cr)) &&
    p4K (mulK 5 (conjK5 cc cr) (conjIK cc cr))

@[expose] noncomputable def evInvK (c : ℕ) : Bool := evenK 5 c && Nat.beq (mulK 5 c c) e5

theorem fixK_of {σ : Perm (Fin 5)} {p : Fin 5} (h : σ p = p) : fixK (enc σ) p = true := by
  rw [fixK, rd_enc h5, h, Nat.beq_refl]

theorem p4K_of {g : Perm (Fin 5)} (h : g ^ 4 = 1) : p4K (enc g) = true := by
  rw [p4K, ← enc_one5, ← enc_pow h5, h, Nat.beq_refl]

theorem p4K_false {g : Perm (Fin 5)} (h : p4K (enc g) = false) : g ^ 4 ≠ 1 := fun e => by
  rw [p4K_of e] at h
  exact absurd h (by decide)

theorem enc_conjI (g x : Perm (Fin 5)) : enc (g⁻¹ * x * g) = conjIK (enc g) (enc x) := by
  rw [conjIK, enc_mul h5, enc_mul h5, enc_inv_invCK h5]

theorem evInvK_iff (σ : Perm (Fin 5)) :
    evInvK (enc σ) = true ↔ Perm.sign σ = 1 ∧ σ * σ = 1 := by
  rw [evInvK, Bool.and_eq_true, ← sign_eq_one_iff_evenK h5, ← enc_one5, beq_mul_iff]

theorem evenK_false {σ : Perm (Fin 5)} (h : Perm.sign σ = -1) : evenK 5 (enc σ) = false :=
  Bool.eq_false_iff.2 fun e => by
    have h1 := (sign_eq_one_iff_evenK h5 σ).2 e
    rw [h] at h1
    exact absurd h1 (by decide)

theorem z1_ok : allK (fun cc => Nat.beq cc e5 || allLtK (fun p => !fixK cc p ||
    allK (fun cr => !fixK cr p || !tnK cc cr || evInvK cr) twoC) 5) c3eC = true := by
  decide +kernel

theorem z2_ok : allK (fun ct => !walkK 5 (fun cs =>
    !(evenK 5 cs && !p4K (powK 5 e5 (mulK 5 ct (conjK5 cs ct)) 6))) 5 0 0 0) invC5 = true := by
  decide +kernel

theorem z3_ok : allK (fun cc => Nat.beq cc e5 || allLtK (fun p => !fixK cc p ||
    walkK 5 (fun cs => !fixK cs p || evenK 5 cs ||
      !p4K (mulK 5 (conjK5 cs cc) (invCK 5 cc))) 5 0 0 0) 5) c3eC = true := by
  decide +kernel

theorem z4_ok : allLtK (fun p => allK (fun ca => !fixK ca p || allK (fun cb => !fixK cb p ||
    Nat.beq ca cb || walkK 5 (fun cx => !Nat.beq (mulK 5 cx ca) (mulK 5 ca cx) ||
      !Nat.beq (mulK 5 cx cb) (mulK 5 cb cx) || (fixK cx p && evInvK cx)) 5 0 0 0) invC5)
    invC5) 5 = true := by
  decide +kernel

theorem z5_ok : allK (fun c => p4K c) twoC = true := by
  decide +kernel

theorem v4_of_tn {p : Fin 5} {c r : Perm (Fin 5)} (hcp : c p = p) (hc3 : c * c * c = 1)
    (hc1 : c ≠ 1) (hrp : r p = p) (h1 : r ^ 4 = 1) (h2 : (r * (c * r * c⁻¹)) ^ 4 = 1)
    (h3 : (r * (c⁻¹ * r * c)) ^ 4 = 1) (h4 : ((c * r * c⁻¹) * (c⁻¹ * r * c)) ^ 4 = 1) :
    Perm.sign r = 1 ∧ r * r = 1 := by
  have hr8 : r ^ 8 = 1 := by
    have e : r ^ 8 = (r ^ 4) ^ 2 := by rw [← pow_mul]
    rw [e, h1, one_pow]
  have hc := allK_iff.1 z1_ok _ (memK_iff.1 (mem_c3eC hc3))
  beta_reduce at hc
  rw [beq_one_false hc1, Bool.false_or] at hc
  have hp := allLtK_iff.1 hc p p.isLt
  beta_reduce at hp
  rw [fixK_of hcp, Bool.not_true, Bool.false_or] at hp
  have hr := allK_iff.1 hp _ (memK_iff.1 (mem_twoC hr8))
  beta_reduce at hr
  have ht : tnK (enc c) (enc r) = true := by
    rw [tnK, ← enc_conj, ← enc_conjI, ← enc_mul h5, ← enc_mul h5, ← enc_mul h5, p4K_of h1,
      p4K_of h2, p4K_of h3, p4K_of h4]
    all_goals rfl
  rw [fixK_of hrp, ht] at hr
  simp only [Bool.not_true, Bool.false_or] at hr
  exact (evInvK_iff r).1 hr

theorem conj_pow {τ : Perm (Fin 5)} (hs : Perm.sign τ = 1) (h2 : τ * τ = 1) (h1 : τ ≠ 1) :
    ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ (τ * (σ * τ * σ⁻¹)) ^ 24 ≠ 1 := by
  have h := allK_iff.1 z2_ok _ (memK_iff.1 (mem_invC5 h2 h1 hs))
  beta_reduce at h
  have hw : walkK 5 (fun cs => !(evenK 5 cs &&
      !p4K (powK 5 e5 (mulK 5 (enc τ) (conjK5 cs (enc τ))) 6))) 5 0 0 0 = false :=
    Bool.eq_false_iff.2 fun e => by
      rw [e] at h
      exact absurd h (by decide)
  obtain ⟨σ, hσ⟩ := exists_of_walkK (P := fun cs => evenK 5 cs &&
    !p4K (powK 5 e5 (mulK 5 (enc τ) (conjK5 cs (enc τ))) 6)) hw
  beta_reduce at hσ
  rw [Bool.and_eq_true] at hσ
  obtain ⟨hσ1, hσ2⟩ := hσ
  refine ⟨σ, (sign_eq_one_iff_evenK h5 σ).2 hσ1, ?_⟩
  have e : (τ * (σ * τ * σ⁻¹)) ^ 24 = ((τ * (σ * τ * σ⁻¹)) ^ 6) ^ 4 := by rw [← pow_mul]
  rw [e]
  apply p4K_false
  rw [← enc_one5] at hσ2
  rw [enc_pow h5, enc_mul h5, enc_conj]
  exact Bool.eq_false_iff.2 fun e => by
    rw [e] at hσ2
    exact absurd hσ2 (by decide)

theorem comm_ne {p : Fin 5} {c σ : Perm (Fin 5)} (hcp : c p = p) (hc3 : c * c * c = 1)
    (hc1 : c ≠ 1) (hsp : σ p = p) (hs : Perm.sign σ = -1) : (σ * c * σ⁻¹ * c⁻¹) ^ 4 ≠ 1 := by
  have hc := allK_iff.1 z3_ok _ (memK_iff.1 (mem_c3eC hc3))
  beta_reduce at hc
  rw [beq_one_false hc1, Bool.false_or] at hc
  have hp := allLtK_iff.1 hc p p.isLt
  beta_reduce at hp
  rw [fixK_of hcp, Bool.not_true, Bool.false_or] at hp
  have h := walkK_sound hp σ
  beta_reduce at h
  rw [fixK_of hsp, evenK_false hs] at h
  simp only [Bool.not_true, Bool.false_or] at h
  apply p4K_false
  rw [enc_mul h5, enc_conj, enc_inv_invCK h5]
  exact Bool.eq_false_iff.2 fun e => by
    rw [e] at h
    exact absurd h (by decide)

theorem v4_of_comm {p : Fin 5} {a b x : Perm (Fin 5)} (hap : a p = p) (hsa : Perm.sign a = 1)
    (ha : a * a = 1) (ha1 : a ≠ 1) (hbp : b p = p) (hsb : Perm.sign b = 1) (hb : b * b = 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (hxa : x * a = a * x) (hxb : x * b = b * x) :
    x p = p ∧ Perm.sign x = 1 ∧ x * x = 1 := by
  have hp := allLtK_iff.1 z4_ok p p.isLt
  beta_reduce at hp
  have h1 := allK_iff.1 hp _ (memK_iff.1 (mem_invC5 ha ha1 hsa))
  beta_reduce at h1
  rw [fixK_of hap, Bool.not_true, Bool.false_or] at h1
  have h2 := allK_iff.1 h1 _ (memK_iff.1 (mem_invC5 hb hb1 hsb))
  beta_reduce at h2
  rw [fixK_of hbp, beq_enc_false h5 hab] at h2
  simp only [Bool.not_true, Bool.false_or] at h2
  have h := walkK_sound h2 x
  beta_reduce at h
  rw [(comm_enc_iff h5).2 hxa, (comm_enc_iff h5).2 hxb] at h
  simp only [Bool.not_true, Bool.false_or] at h
  rw [Bool.and_eq_true, evInvK_iff] at h
  refine ⟨?_, h.2⟩
  have hf := h.1
  rw [fixK, rd_enc h5, Nat.beq_eq] at hf
  exact Fin.ext hf

theorem pow4_of_pow8 {σ : Perm (Fin 5)} (h : σ ^ 8 = 1) : σ ^ 4 = 1 := by
  have h1 := allK_iff.1 z5_ok _ (memK_iff.1 (mem_twoC h))
  beta_reduce at h1
  rw [p4K, ← enc_one5, ← enc_pow h5, beq_enc_iff h5] at h1
  exact h1

end CFSG.Quasithin.H13.A6.ZbPack
