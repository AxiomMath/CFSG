module

public import CFSG.Quasithin.Recognition.HSType15a
public import CFSG.Quasithin.H13.L32AC50aPack
public import CFSG.Permutation.FinPackInv

public section

namespace CFSG.Quasithin.HSType.Pack16a

open Equiv CFSG.Permutation.FinPack CFSG.Quasithin.H13.L32A.C.Alt7Pack

theorem h6 : (6 : ℕ) ≤ 16 := by norm_num

@[expose] def actF (f : Fin 6 → Fin 6) (v : SpV) : SpV :=
  v 0 • (duadPt (f 0) + duadPt (f 1)) + v 1 • (duadPt (f 1) + duadPt (f 2)) +
    v 2 • (duadPt (f 3) + duadPt (f 4)) + v 3 • (duadPt (f 4) + duadPt (f 5))

@[expose] def lamP (f : Fin 6 → Fin 6) : Bool :=
  decide (∀ k : Fin 4, actF f (hsJ (spE k)) = hsJ (actF f (spE k)))

@[expose] def stabP (f : Fin 6 → Fin 6) : Bool := decide (∀ v : SpV, InV2m v → InV2m (actF f v))

@[expose] def fixP (f : Fin 6 → Fin 6) : Bool := decide (∀ v : SpV, InV2m v → actF f v = v)

@[expose] def lamC : List ℕ := [
    5517840, 4530960, 5456160, 3478560, 4346160, 2364720, 3232320, 1254720, 2179920, 1193040,
    4534785, 5513985, 4411425, 3409185, 5390385, 2425905, 2118465, 144705, 3162705, 205905,
    3490050, 5444610, 3428370, 4392210, 1070130, 83250, 5320770, 1377090, 4206930, 267090,
    2380035, 4330755, 2441235, 5374995, 87075, 1066275, 5251395, 332355, 4268115, 1311315,
    1266180, 3220740, 152340, 2110740, 1388580, 5309220, 336180, 5247540, 3280980, 2294100,
    1196805, 2176005, 213525, 3154965, 274725, 4199205, 1318965, 4260405, 2297925, 3277125]

@[expose] def stabC : List ℕ := [
    5517840, 4534800, 5514000, 4530960, 3298320, 2315280, 3294480, 2311440, 5517825, 4534785,
    5513985, 4530945, 3298305, 2315265, 3294465, 2311425, 5509170, 4526130, 5505330, 4522290,
    1070130, 87090, 1066290, 83250, 5509155, 4526115, 5505315, 4522275, 1070115, 87075, 1066275,
    83235, 3280980, 2297940, 3277140, 2294100, 1061460, 78420, 1057620, 74580, 3280965, 2297925,
    3277125, 2294085, 1061445, 78405, 1057605, 74565]

@[expose] def fixC : List ℕ := [
    5517840, 4534800, 5514000, 4530960, 5517825, 4534785, 5513985, 4530945]

theorem mem_lamS_K : ∀ σ : Perm (Fin 6), σ ∈ lamS ↔ memK (enc σ) lamC = true := by
  have hc := card_lamS
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  refine mem_iff_count h6 (· ∈ lamS) lamP (fun σ => ?_) lamC (by decide +kernel)
    (le_of_eq_of_le hc (by decide +kernel))
  rw [lamP, decide_eq_true_iff]
  exact mem_lamS_iff_basis σ

theorem mem_stabS_K : ∀ σ : Perm (Fin 6), σ ∈ stabS ↔ memK (enc σ) stabC = true := by
  have hc := card_stabS
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  refine mem_iff_count h6 (· ∈ stabS) stabP (fun σ => ?_) stabC (by decide +kernel)
    (le_of_eq_of_le hc (by decide +kernel))
  rw [stabP, decide_eq_true_iff]
  exact Iff.rfl

theorem mem_fixS_K : ∀ σ : Perm (Fin 6), σ ∈ fixS ↔ memK (enc σ) fixC = true := by
  have hc := card_fixS
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  refine mem_iff_count h6 (· ∈ fixS) fixP (fun σ => ?_) fixC (by decide +kernel)
    (le_of_eq_of_le hc (by decide +kernel))
  rw [fixP, decide_eq_true_iff]
  exact Iff.rfl

@[expose] noncomputable def inLam0 (c : ℕ) : Bool := memK c stabC && memK c lamC

theorem mem_lam0_K (σ : Perm (Fin 6)) : σ ∈ lam0 ↔ inLam0 (enc σ) = true := by
  change σ ∈ lamS ⊓ stabS ↔ _
  rw [Subgroup.mem_inf, mem_lamS_K, mem_stabS_K, inLam0, Bool.and_eq_true, and_comm]

@[expose] def one6 : ℕ := 5517840

@[expose] def alphaC : ℕ := 4530960

@[expose] def betaC : ℕ := 4411425

@[expose] def sigmaC : ℕ := 1070130

@[expose] def sigmaInvC : ℕ := 3280980

theorem enc_one6 : enc (1 : Perm (Fin 6)) = one6 := by decide +kernel

theorem enc_αS : enc αS = alphaC := by decide +kernel

theorem enc_βS : enc βS = betaC := by decide +kernel

theorem enc_σS0 : enc σS0 = sigmaC := by decide +kernel

theorem enc_σS0_inv : enc σS0⁻¹ = sigmaInvC := by
  rw [enc_inv_invCK h6, enc_σS0]
  decide +kernel

@[expose] def evenInvC : List ℕ := [3298320, 5509170, 1061460]

@[expose] def jInvC : List ℕ := [1193040, 3428370, 5247540]

@[expose] def ellC : List ℕ := [5517840, 3277125, 2294100, 4534785, 74565, 3294480, 4526130, 3298305]

@[expose] noncomputable def normK2 (c ci : ℕ) : Bool :=
  memK (mulK 6 (mulK 6 c alphaC) ci) lamC && memK (mulK 6 (mulK 6 c betaC) ci) lamC

@[expose] noncomputable def normK (c : ℕ) : Bool := normK2 c (invCK 6 c)

theorem normK_iff (ρ : Perm (Fin 6)) :
    (ρ * αS * ρ⁻¹ ∈ lamS ∧ ρ * βS * ρ⁻¹ ∈ lamS) ↔ normK (enc ρ) = true := by
  rw [mem_lamS_K, mem_lamS_K, enc_mul h6, enc_mul h6, enc_mul h6, enc_mul h6, enc_inv_invCK h6,
    enc_αS, enc_βS, normK, normK2, Bool.and_eq_true]

@[expose] noncomputable def invertsK (c : ℕ) : Bool :=
  Nat.beq (mulK 6 (mulK 6 c sigmaC) (invCK 6 c)) sigmaInvC

theorem invertsK_iff (ρ : Perm (Fin 6)) : invertsK (enc ρ) = true ↔ ρ * σS0 * ρ⁻¹ = σS0⁻¹ := by
  rw [invertsK, ← enc_σS0, ← enc_σS0_inv, ← enc_inv_invCK h6, ← enc_mul h6, ← enc_mul h6,
    beq_enc_iff h6]

theorem invertsK_of (ρ : Perm (Fin 6)) (h : ρ * σS0 * ρ⁻¹ = σS0⁻¹) : invertsK (enc ρ) = true :=
  (invertsK_iff ρ).2 h

theorem involK_iff (ρ : Perm (Fin 6)) :
    Nat.beq (mulK 6 (enc ρ) (enc ρ)) one6 = true ↔ ρ * ρ = 1 := by
  rw [← enc_mul h6, ← enc_one6, beq_enc_iff h6]

theorem involK_of (ρ : Perm (Fin 6)) (h : ρ * ρ = 1) :
    Nat.beq (mulK 6 (enc ρ) (enc ρ)) one6 = true :=
  (involK_iff ρ).2 h

theorem not_mem_of_K {p : Perm (Fin 6) → Prop} {L : List ℕ}
    (hp : ∀ σ, p σ ↔ memK (enc σ) L = true) {σ : Perm (Fin 6)} (h : (!memK (enc σ) L) = true) :
    ¬ p σ := fun hσ => by
  rw [(hp σ).1 hσ] at h
  exact absurd h (by decide)

@[expose] noncomputable def fpfK (c : ℕ) : Bool := allLtK (fun i => !Nat.beq (rd c i) i) 6

theorem fpf_of_K (σ : Perm (Fin 6)) (h : fpfK (enc σ) = true) : ∀ x, σ x ≠ x := by
  intro x hx
  have h1 := allLtK_iff.1 h x x.isLt
  rw [rd_enc h6 σ x, hx, Nat.beq_refl] at h1
  exact absurd h1 (by decide)

@[expose] noncomputable def q7 (c : ℕ) : Bool :=
  memK c stabC && !memK c lamC && !memK c fixC && fpfK c && Nat.beq (mulK 6 c c) one6 &&
    invertsK c && normK c

theorem facts_of_q7 (x : Perm (Fin 6)) (h : q7 (enc x) = true) :
    x ∈ stabS ∧ x ∉ lamS ∧ x ∉ fixS ∧ (∀ i, x i ≠ i) ∧ x * x = 1 ∧ x * σS0 * x⁻¹ = σS0⁻¹ ∧
      (x * αS * x⁻¹ ∈ lamS ∧ x * βS * x⁻¹ ∈ lamS) := by
  simp only [q7, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h
  exact ⟨(mem_stabS_K x).2 a1, not_mem_of_K mem_lamS_K a2, not_mem_of_K mem_fixS_K a3,
    fpf_of_K x a4, (involK_iff x).1 a5, (invertsK_iff x).1 a6, (normK_iff x).2 a7⟩

@[expose] def iotaC : List ℕ := [2311425, 4522275, 74565]

theorem q7_ok : allK q7 iotaC = true := by decide +kernel

@[expose] def cosetC : List ℕ := [5517840, 5456160, 3478560, 3232320, 1254720]

theorem cosetC_ok : allK (fun c => memK c lamC) cosetC = true := by decide +kernel

theorem evenInvC_ok :
    allK (fun c => !memK c lamC && inLam0 (mulK 6 c 3298320)) evenInvC = true := by
  decide +kernel

theorem evenInvC_jInvC_ok :
    allK (fun a => allK (fun b => Nat.beq (powK 6 one6 (mulK 6 a b) 3) one6) jInvC) evenInvC =
      true := by
  decide +kernel

theorem ellC_ok : allK (fun c => memK c stabC && normK c && normK (invCK 6 c)) ellC = true := by
  decide +kernel

theorem pow3K_of (ρ : Perm (Fin 6)) (h : ρ ^ 3 = 1) :
    Nat.beq (powK 6 one6 (enc ρ) 3) one6 = true := by
  rw [← enc_one6, ← enc_pow h6, h, Nat.beq_refl]

@[expose] noncomputable def q1 (c : ℕ) : Bool :=
  inLam0 c || normK c || memK (powK 6 one6 c 3) fixC || evenK 6 c

theorem q1_ok : allK q1 stabC = true := by decide +kernel

@[expose] noncomputable def q2 (r c : ℕ) : Bool := !evenK 6 c || memK c lamC || inLam0 (mulK 6 c r)

theorem q2_ok : allK (q2 3298320) stabC = true := by decide +kernel

@[expose] def cosetBC : List ℕ := [3298320, 4281120, 5325360, 5386560, 4399440]

@[expose] noncomputable def q3 (c : ℕ) : Bool :=
  !evenK 6 c || memK c lamC || anyK (fun d => memK (mulK 6 c d) lamC) cosetBC

theorem q3_ok : walkK 6 q3 6 0 0 0 = true := by decide +kernel

@[expose] noncomputable def q4 (c : ℕ) : Bool :=
  !evenK 6 c || !Nat.beq (mulK 6 c c) one6 || !invertsK c || memK c evenInvC

theorem q4_ok : allK q4 stabC = true := by decide +kernel

@[expose] noncomputable def q5 (c : ℕ) : Bool :=
  memK c stabC || !Nat.beq (mulK 6 c c) one6 || !invertsK c || memK c jInvC

theorem q5_ok : allK q5 lamC = true := by decide +kernel

@[expose] noncomputable def q6 (c : ℕ) : Bool :=
  !Nat.beq (powK 6 one6 c 3) one6 || Nat.beq c one6 ||
    anyK (fun l => Nat.beq (mulK 6 (mulK 6 l c) (invCK 6 l)) sigmaC) ellC

theorem q6_ok : allK q6 stabC = true := by decide +kernel

end CFSG.Quasithin.HSType.Pack16a
