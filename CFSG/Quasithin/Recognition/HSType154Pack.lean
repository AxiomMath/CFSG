module

public import CFSG.Permutation.FinPackAll6
public import CFSG.Permutation.FinPackF2
public import CFSG.Quasithin.Recognition.HSType16a

public section

namespace CFSG.Quasithin.HSType.Pack154

open CFSG.Permutation.FinPack Equiv

@[expose] def stabCodes : List ℕ := [
    74565, 74580, 78405, 78420, 83235, 83250, 87075, 87090, 1057605, 1057620,
    1061445, 1061460, 1066275, 1066290, 1070115, 1070130, 2294085, 2294100, 2297925, 2297940,
    2311425, 2311440, 2315265, 2315280, 3277125, 3277140, 3280965, 3280980, 3294465, 3294480,
    3298305, 3298320, 4522275, 4522290, 4526115, 4526130, 4530945, 4530960, 4534785, 4534800,
    5505315, 5505330, 5509155, 5509170, 5513985, 5514000, 5517825, 5517840]

@[expose] def normCodes : List ℕ := [
    74565, 78420, 83250, 87075, 136245, 144705, 147795, 152340, 202020, 205905,
    213525, 217410, 267090, 271635, 274725, 283185, 332355, 336180, 341010, 344865,
    1057620, 1061445, 1066275, 1070130, 1180980, 1193040, 1196805, 1200195, 1246245, 1254720,
    1261650, 1266180, 1311315, 1318965, 1324290, 1332000, 1377090, 1385475, 1388580, 1393200,
    2102355, 2110740, 2113845, 2118465, 2164035, 2176005, 2179920, 2183220, 2294100, 2297925,
    2311425, 2315280, 2360085, 2364720, 2371665, 2380035, 2425905, 2429700, 2437440, 2441235,
    3151170, 3154965, 3162705, 3166500, 3212370, 3220740, 3227685, 3232320, 3277125, 3280980,
    3294480, 3298305, 3409185, 3412485, 3416400, 3428370, 3473940, 3478560, 3481665, 3490050,
    4199205, 4203825, 4206930, 4215315, 4260405, 4268115, 4273440, 4281090, 4326225, 4330755,
    4337685, 4346160, 4392210, 4395600, 4399365, 4411425, 4522275, 4526130, 4530960, 4534785,
    5247540, 5251395, 5256225, 5260050, 5309220, 5317680, 5320770, 5325315, 5374995, 5378880,
    5386500, 5390385, 5440065, 5444610, 5447700, 5456160, 5505330, 5509155, 5513985, 5517840]

@[expose] def lamCodes : List ℕ := [
    83250, 87075, 144705, 152340, 205905, 213525, 267090, 274725, 332355, 336180,
    1066275, 1070130, 1193040, 1196805, 1254720, 1266180, 1311315, 1318965, 1377090, 1388580,
    2110740, 2118465, 2176005, 2179920, 2294100, 2297925, 2364720, 2380035, 2425905, 2441235,
    3154965, 3162705, 3220740, 3232320, 3277125, 3280980, 3409185, 3428370, 3478560, 3490050,
    4199205, 4206930, 4260405, 4268115, 4330755, 4346160, 4392210, 4411425, 4530960, 4534785,
    5247540, 5251395, 5309220, 5320770, 5374995, 5390385, 5444610, 5456160, 5513985, 5517840]

@[expose] def duadT : ℕ := 574838

@[expose] def dK (c i : ℕ) : ℕ := rd duadT (rd c i)

@[expose] def actK (c x : ℕ) : ℕ :=
  linK (Nat.xor (dK c 0) (dK c 1)) (Nat.xor (dK c 1) (dK c 2)) (Nat.xor (dK c 3) (dK c 4))
    (Nat.xor (dK c 4) (dK c 5)) x

@[expose] def jK (x : ℕ) : ℕ :=
  Nat.add (bitK x 3) (Nat.add (Nat.mul 2 (bitK x 2))
    (Nat.add (Nat.mul 4 (Nat.xor (bitK x 1) (bitK x 2))) (Nat.mul 8 (Nat.xor (bitK x 0) (bitK x 3)))))

theorem vc_duad : ∀ i : Fin 6, vc (duadPt i) = rd duadT i := by decide +kernel

theorem vc_hsJ : ∀ v : SpV, vc (hsJ v) = jK (vc v) := by decide +kernel

theorem inV2m_iff : ∀ v : SpV, InV2m v ↔ Nat.beq (Nat.land (vc v) 6) 0 = true := by
  decide +kernel

theorem vc_actS6 (σ : Perm (Fin 6)) (v : SpV) : vc (actS6 σ v) = actK (enc σ) (vc v) := by
  have hr : ∀ i : Fin 6, rd (enc σ) i = σ i := rd_enc (by norm_num) σ
  have h0 : dK (enc σ) 0 = vc (duadPt (σ 0)) := by rw [dK, vc_duad, ← hr]; rfl
  have h1 : dK (enc σ) 1 = vc (duadPt (σ 1)) := by rw [dK, vc_duad, ← hr]; rfl
  have h2 : dK (enc σ) 2 = vc (duadPt (σ 2)) := by rw [dK, vc_duad, ← hr]; rfl
  have h3 : dK (enc σ) 3 = vc (duadPt (σ 3)) := by rw [dK, vc_duad, ← hr]; rfl
  have h4 : dK (enc σ) 4 = vc (duadPt (σ 4)) := by rw [dK, vc_duad, ← hr]; rfl
  have h5 : dK (enc σ) 5 = vc (duadPt (σ 5)) := by rw [dK, vc_duad, ← hr]; rfl
  rw [actK, h0, h1, h2, h3, h4, h5, ← vc_add, ← vc_add, ← vc_add, ← vc_add, actS6, vc_lin]

@[expose] noncomputable def stabK (c : ℕ) : Bool :=
  allK (fun x => !Nat.beq (Nat.land x 6) 0 || Nat.beq (Nat.land (actK c x) 6) 0) codes16

@[expose] noncomputable def lamK (c : ℕ) : Bool :=
  allK (fun x => Nat.beq (actK c (jK x)) (jK (actK c x))) codes16

@[expose] noncomputable def normK (p : ℕ) : Bool :=
  lamK (mulK 6 (mulK 6 (lo6 p) 4530960) (hi6 p)) &&
    lamK (mulK 6 (mulK 6 (lo6 p) 4411425) (hi6 p))

theorem enc_αS : enc αS = 4530960 := by decide +kernel

theorem enc_βS : enc βS = 4411425 := by decide +kernel

theorem stabS_iff_stabK (σ : Perm (Fin 6)) : σ ∈ stabS ↔ stabK (enc σ) = true := by
  rw [stabK, allK_iff, ← forall_vc (P := fun x =>
    (!Nat.beq (Nat.land x 6) 0 || Nat.beq (Nat.land (actK (enc σ) x) 6) 0) = true)]
  change (∀ v, InV2m v → InV2m (actS6 σ v)) ↔ _
  refine forall_congr' fun v => ?_
  rw [inV2m_iff, inV2m_iff, vc_actS6, Bool.or_eq_true, Bool.not_eq_true', ← Bool.not_eq_true]
  exact imp_iff_not_or

theorem lamS_iff_lamK (σ : Perm (Fin 6)) : σ ∈ lamS ↔ lamK (enc σ) = true := by
  rw [lamK, allK_iff, ← forall_vc (P := fun x =>
    Nat.beq (actK (enc σ) (jK x)) (jK (actK (enc σ) x)) = true)]
  change (∀ v, actS6 σ (hsJ v) = hsJ (actS6 σ v)) ↔ _
  refine forall_congr' fun v => ?_
  rw [Nat.beq_eq, ← vc_hsJ, ← vc_actS6, ← vc_actS6, ← vc_hsJ]
  exact ⟨congrArg vc, vc_inj _ _⟩

theorem normLamS_iff_normK (σ : Perm (Fin 6)) : NormLamS σ ↔ normK (pc6 σ) = true := by
  rw [normK, lo6_pc6, hi6_pc6, Bool.and_eq_true, ← enc_αS, ← enc_βS, ← enc_mul (by norm_num),
    ← enc_mul (by norm_num), ← enc_mul (by norm_num), ← enc_mul (by norm_num), ← lamS_iff_lamK,
    ← lamS_iff_lamK]
  rfl

theorem pin_of_check {R : Perm (Fin 6) → Prop} {t : ℕ → Bool} {L : List ℕ}
    (hR : ∀ ρ, R ρ ↔ t (pc6 ρ) = true)
    (hc : allK (fun p => t p == memK (lo6 p) L) allCodes6 = true) (ρ : Perm (Fin 6)) :
    R ρ ↔ memK (enc ρ) L = true := by
  have h := allK_iff.1 hc _ (memK_iff.1 (pc6_mem_all ρ))
  rw [lo6_pc6, beq_iff_eq] at h
  rw [hR, h]

theorem pin_stab : allK (fun p => stabK (lo6 p) == memK (lo6 p) stabCodes) allCodes6 = true := by
  decide +kernel

theorem pin_norm : allK (fun p => normK p == memK (lo6 p) normCodes) allCodes6 = true := by
  decide +kernel

theorem pin_lam : allK (fun p => lamK (lo6 p) == memK (lo6 p) lamCodes) allCodes6 = true := by
  decide +kernel

theorem mem_stabS_iff_code : ∀ σ : Perm (Fin 6), σ ∈ stabS ↔ memK (enc σ) stabCodes = true :=
  pin_of_check (fun ρ => by rw [lo6_pc6]; exact stabS_iff_stabK ρ) pin_stab

theorem normLamS_iff_code : ∀ σ : Perm (Fin 6), NormLamS σ ↔ memK (enc σ) normCodes = true :=
  pin_of_check normLamS_iff_normK pin_norm

theorem mem_lamS_iff_code : ∀ σ : Perm (Fin 6), σ ∈ lamS ↔ memK (enc σ) lamCodes = true :=
  pin_of_check (fun ρ => by rw [lo6_pc6]; exact lamS_iff_lamK ρ) pin_lam

theorem check_inv :
    allK (fun p => !memK (lo6 p) normCodes || memK (hi6 p) normCodes) allCodes6 = true := by
  decide +kernel

theorem normLamS_inv_code (σ : Perm (Fin 6)) (h : NormLamS σ) : NormLamS σ⁻¹ := by
  have h1 := allK_iff.1 check_inv _ (memK_iff.1 (pc6_mem_all σ))
  rw [lo6_pc6, hi6_pc6, (normLamS_iff_code σ).1 h, Bool.not_true, Bool.false_or] at h1
  exact (normLamS_iff_code _).2 h1

theorem check_even :
    allK (fun p => !memK (lo6 p) normCodes || memK (lo6 p) lamCodes) evenCodes6 = true := by
  decide +kernel

theorem mem_lamS_of_normLamS_code (σ : Perm (Fin 6)) (hs : Perm.sign σ = 1) (h : NormLamS σ) :
    σ ∈ lamS := by
  have h1 := allK_iff.1 check_even _ (memK_iff.1 (pc6_mem_even σ hs))
  rw [lo6_pc6, (normLamS_iff_code σ).1 h, Bool.not_true, Bool.false_or] at h1
  exact (mem_lamS_iff_code _).2 h1

theorem check_not : pairCheck6 (fun s => memK s stabCodes && !memK s normCodes)
    (fun s => !memK s normCodes) stabCodes normCodes = true := by
  decide +kernel

theorem check_norm : pairCheck6 (fun s => memK s stabCodes && memK s normCodes && !memK s lamCodes)
    (fun s => memK s normCodes && !memK s lamCodes) stabCodes lamCodes = true := by
  decide +kernel

theorem normLamS_inv_mul_of_not_code : ∀ σ τ : Perm (Fin 6), σ ∈ stabS ∧ ¬ NormLamS σ →
    τ ∈ stabS ∧ ¬ NormLamS τ → NormLamS (σ⁻¹ * τ) := by
  refine pair_of_check (fun σ h => ?_) (fun τ h => ?_) (fun ρ h => (normLamS_iff_code ρ).2 h)
    check_not
  · rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, ← mem_stabS_iff_code,
      ← normLamS_iff_code]
    exact h
  · rw [Bool.not_eq_true', ← Bool.not_eq_true, ← mem_stabS_iff_code, ← normLamS_iff_code]
    exact h

theorem inv_mul_mem_lamS_code : ∀ σ τ : Perm (Fin 6), σ ∈ stabS ∧ NormLamS σ ∧ σ ∉ lamS →
    τ ∈ stabS ∧ NormLamS τ ∧ τ ∉ lamS → σ⁻¹ * τ ∈ lamS := by
  refine pair_of_check (fun σ h => ?_) (fun τ h => ?_) (fun ρ h => (mem_lamS_iff_code ρ).2 h)
    check_norm
  · rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
      ← mem_stabS_iff_code, ← normLamS_iff_code, ← mem_lamS_iff_code]
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, ← mem_stabS_iff_code,
      ← normLamS_iff_code, ← mem_lamS_iff_code]
    exact ⟨h.1, h.2.1, h.2.2⟩

end CFSG.Quasithin.HSType.Pack154
