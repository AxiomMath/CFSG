module

public import CFSG.Quasithin.Recognition.HSTypeS6
public import CFSG.Permutation.FinPackInv

public section

namespace CFSG.Quasithin.HSType.Pack15a

open Equiv CFSG.Permutation.FinPack

theorem six_le : (6 : ℕ) ≤ 16 := by norm_num

@[expose] def vK (v : SpV) : ℕ := (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val

theorem vK_inj : ∀ v w : SpV, vK v = vK w → v = w := by decide +kernel

theorem vK_add : ∀ v w : SpV, vK (v + w) = Nat.xor (vK v) (vK w) := by decide +kernel

theorem vK_smul : ∀ (c : ZMod 2) (v : SpV), vK (c • v) = Nat.mul c.val (vK v) := by decide +kernel

theorem eq_iff_vK (v w : SpV) : v = w ↔ Nat.beq (vK v) (vK w) = true := by
  rw [Nat.beq_eq]
  exact ⟨congrArg vK, vK_inj v w⟩

@[expose] def bitN (u j : ℕ) : ℕ := Nat.land (Nat.shiftRight u j) 1

theorem val_eq_bitN : ∀ v : SpV, (v 0).val = bitN (vK v) 0 ∧ (v 1).val = bitN (vK v) 1 ∧
    (v 2).val = bitN (vK v) 2 ∧ (v 3).val = bitN (vK v) 3 := by
  decide +kernel

@[expose] def dpT : ℕ := 574838

theorem vK_duadPt : ∀ i : Fin 6, vK (duadPt i) = rd dpT i := by decide +kernel

@[expose] noncomputable def bK (c a b : ℕ) : ℕ := Nat.xor (rd dpT (rd c a)) (rd dpT (rd c b))

@[expose] noncomputable def actN (c u : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (Nat.mul (bitN u 0) (bK c 0 1)) (Nat.mul (bitN u 1) (bK c 1 2)))
    (Nat.mul (bitN u 2) (bK c 3 4))) (Nat.mul (bitN u 3) (bK c 4 5))

theorem vK_actS6 (σ : Perm (Fin 6)) (v : SpV) : vK (actS6 σ v) = actN (enc σ) (vK v) := by
  obtain ⟨h0, h1, h2, h3⟩ := val_eq_bitN v
  have r : ∀ i : Fin 6, rd (enc σ) i = σ i := rd_enc six_le σ
  have r0 : rd (enc σ) 0 = σ 0 := r 0
  have r1 : rd (enc σ) 1 = σ 1 := r 1
  have r2 : rd (enc σ) 2 = σ 2 := r 2
  have r3 : rd (enc σ) 3 = σ 3 := r 3
  have r4 : rd (enc σ) 4 = σ 4 := r 4
  have r5 : rd (enc σ) 5 = σ 5 := r 5
  rw [actS6, vK_add, vK_add, vK_add, vK_smul, vK_smul, vK_smul, vK_smul, vK_add, vK_add, vK_add,
    vK_add, vK_duadPt, vK_duadPt, vK_duadPt, vK_duadPt, vK_duadPt, vK_duadPt, h0, h1, h2, h3,
    actN, bK, bK, bK, bK, r0, r1, r2, r3, r4, r5]

@[expose] def hjT : ℕ := 4287247734968599680

@[expose] noncomputable def lamQ (c : ℕ) : Bool :=
  Nat.beq (actN c 8) (rd hjT (actN c 1)) && Nat.beq (actN c 4) (rd hjT (actN c 2)) &&
    Nat.beq (actN c 6) (rd hjT (actN c 4)) && Nat.beq (actN c 9) (rd hjT (actN c 8))

@[expose] noncomputable def stabQ (c : ℕ) : Bool :=
  Nat.beq (Nat.land (actN c 0) 6) 0 && Nat.beq (Nat.land (actN c 1) 6) 0 &&
    Nat.beq (Nat.land (actN c 8) 6) 0 && Nat.beq (Nat.land (actN c 9) 6) 0

@[expose] noncomputable def fixQ (c : ℕ) : Bool :=
  Nat.beq (actN c 0) 0 && Nat.beq (actN c 1) 1 && Nat.beq (actN c 8) 8 && Nat.beq (actN c 9) 9

@[expose] def oneC : ℕ := 5517840

theorem enc_one_six : enc (1 : Perm (Fin 6)) = oneC := by decide +kernel

@[expose] noncomputable def cubeK (c : ℕ) : ℕ := mulK 6 c (mulK 6 c c)

theorem enc_pow_three (σ : Perm (Fin 6)) : enc (σ ^ 3) = cubeK (enc σ) := by
  rw [pow_three, enc_mul six_le, enc_mul six_le, cubeK]

theorem cube_iff (σ : Perm (Fin 6)) : Nat.beq (cubeK (enc σ)) oneC = true ↔ σ ^ 3 = 1 := by
  rw [← enc_pow_three, ← enc_one_six, beq_enc_iff six_le]

theorem sq_iff (σ : Perm (Fin 6)) : Nat.beq (mulK 6 (enc σ) (enc σ)) oneC = true ↔ σ * σ = 1 := by
  rw [← enc_mul six_le, ← enc_one_six, beq_enc_iff six_le]

theorem lamQ_cnt : cntK 6 lamQ 6 0 0 0 = 60 := by decide +kernel

theorem stabQ_cnt : cntK 6 stabQ 6 0 0 0 = 48 := by decide +kernel

theorem lam0Q_cnt : cntK 6 (fun c => stabQ c && lamQ c) 6 0 0 0 = 12 := by decide +kernel

theorem kleinQ_cnt : cntK 6 (fun c => fixQ c && lamQ c) 6 0 0 0 = 4 := by decide +kernel

theorem fixQ_cnt : cntK 6 fixQ 6 0 0 0 = 8 := by decide +kernel

theorem stabQ_inv : walkK 6 (fun c => !stabQ c || stabQ (invCK 6 c)) 6 0 0 0 = true := by
  decide +kernel

theorem klein_walk : walkK 6 (fun c => !(stabQ c && lamQ c) || !Nat.beq (mulK 6 c c) oneC ||
    (fixQ c && lamQ c)) 6 0 0 0 = true := by
  decide +kernel

theorem pow3_walk : walkK 6 (fun c => !stabQ c || !Nat.beq (cubeK c) oneC || lamQ c) 6 0 0 0 =
    true := by
  decide +kernel

@[expose] def sigmaInvC : ℕ := 3280980

theorem pow3or_walk : walkK 6 (fun c => !(stabQ c && lamQ c) || Nat.beq (cubeK c) oneC ||
    Nat.beq (cubeK (mulK 6 sigmaInvC c)) oneC) 6 0 0 0 = true := by
  decide +kernel

@[expose] def alphaC : ℕ := 4530960

@[expose] def betaC : ℕ := 4411425

@[expose] noncomputable def evalABK (w : List Bool) : ℕ :=
  List.rec (motive := fun _ => ℕ) oneC
    (fun b _ r => mulK 6 (Bool.rec (motive := fun _ => ℕ) alphaC betaC b) r) w

@[expose] def wordC : List ℕ := [
    5517840, 4530960, 4411425, 3409185, 5390385, 3490050, 2425905, 5444610, 4206930, 2380035,
    267090, 4330755, 5251395, 3232320, 213525, 332355, 1254720, 3154965, 4260405, 2179920,
    152340, 1388580, 1318965, 1193040, 2110740, 5309220, 3280980, 144705, 1066275, 2294100,
    2118465, 87075, 2297925, 205905, 1070130, 2176005, 3277125, 3162705, 83250, 1196805,
    336180, 1377090, 3220740, 5247540, 5320770, 1266180, 274725, 1311315, 2364720, 5374995,
    4199205, 4268115, 4346160, 2441235, 3478560, 4392210, 5456160, 3428370, 5513985, 4534785]

theorem word_walk : walkK 6 (fun c => !lamQ c || memK c wordC) 6 0 0 0 = true := by
  decide +kernel

end CFSG.Quasithin.HSType.Pack15a
