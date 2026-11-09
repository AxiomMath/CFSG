module

public import Certificates.Data.Kernel.F2Set24Block
public import Certificates.Kernel.Co1KOrb.Data
public import CFSG.Certificates.Kernel.Co1PumpFixSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Pump

open CFSG.KC.F2Set24 CFSG.KD.Co1KOrb
open CFSG.KS.F2Set24 (Back OK stp pms24 img_bits img_lt opsApp_inj opsApp_lt opsApp_xor opsWF_ok
  withPms_eq opsOK_facts D testBit_D D_add cnt cnt_init popG popG_cons popAux_eq_popG pop_step
  popc_eq)
open CFSG.KS.Co1PumpFix (grayWs grayWs_lt)
open CFSG.Sporadic.SmallF2.Native (vecMulN)

universe u

@[expose] noncomputable def ch36909WB : List Nat :=
  [9676673, 4819714, 275588, 5088200, 4823440, 14928096]

@[expose] noncomputable def ch36909gray : List Nat :=
  [0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5,
   0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]

#kc_repo #kc_ktree CertificateChecks.KernelCo1Pump ch36909KY
  "Certificates/Kernel/Co1Pump/data/masksY.bin" 2097152 2 50331648 9432135914345256816

#kc_repo #kc_ktree CertificateChecks.KernelCo1Pump ch36909KT
  "Certificates/Kernel/Co1Pump/data/masksT.bin" 2097152 2 50331648 6821915243797900898

#kc_repo #kc_ktree CertificateChecks.KernelCo1Pump ch36909O
  "Certificates/Kernel/Co1Pump/data/orbit.bin" 2097152 2 16777216 332303643415655034

@[expose] noncomputable def ch36909P (ops : List (Nat × Nat)) : List (Nat × Nat) :=
  withPrep (withPms id) ops id

@[expose] noncomputable def ch36909R : Nat := (2 ^ W - 1) / (2 ^ 2 ^ 6 - 1)

@[expose] noncomputable def ch36909blk2 (opsM : List (Nat × Nat)) (A : Nat) : Bool :=
  withPms fun pms => withPrep pms opsM fun M => strict ch36909R fun R =>
    strict (popAux (pms.take 6) 1 (img M A)) fun c =>
      Nat.beq (((c + 118 * R) >>> 64) &&& (R <<< 7)) 0

@[expose] noncomputable def ch36909E : List Nat := [1, 2, 4, 8, 16, 32]

@[expose] noncomputable def ch36909M : List (Nat × Nat) :=
  [(6, 40), (7, 61), (8, 27), (9, 11), (10, 5), (11, 50), (12, 20), (13, 13), (14, 32), (15, 59),
   (16, 59), (17, 33), (18, 12), (19, 26), (20, 1), (21, 32), (22, 58), (23, 33)]

@[expose] noncomputable def ch36909Y : List (Nat × Nat) :=
  [(13, 328960), (21, 4603904), (4, 4480320), (8, 10825248), (16, 7906560), (1, 13009996),
   (2, 2431290), (14, 2498266), (5, 9984213), (19, 5530151), (23, 7906560), (3, 9515009),
   (20, 135279), (12, 1990656), (9, 2267200), (0, 7485794), (18, 1304845), (17, 328960),
   (6, 15906993), (15, 8653414), (11, 5018834), (7, 11617879), (10, 5656724), (22, 1159634)]

@[expose] noncomputable def ch36909T : List (Nat × Nat) :=
  [(14, 6653205), (15, 4211058), (2, 3238288), (6, 1199417), (22, 8716926), (1, 7093268),
   (12, 13790371), (10, 1577491), (18, 530745), (20, 812220), (23, 3805204), (3, 9012263),
   (21, 4971027), (17, 6312970), (4, 197838), (19, 10749973), (7, 2076672), (16, 1372217),
   (0, 16592054), (13, 8442721), (11, 4338302), (8, 2532570), (9, 12972165), (5, 12253896)]

@[expose] noncomputable def ch36909SY : List (Nat × Nat) :=
  [(8192, ch36909KY.L0), (2097152, ch36909KY.L1), (16, ch36909KY.L2), (256, ch36909KY.L3),
   (65536, ch36909KY.L4), (2, ch36909KY.L5), (4, ch36909KY.L6), (16384, ch36909KY.L7),
   (32, ch36909KY.L8), (524288, ch36909KY.L9), (8388608, ch36909KY.L10), (8, ch36909KY.L11),
   (1048576, ch36909KY.L12), (4096, ch36909KY.L13), (512, ch36909KY.L14), (1, ch36909KY.L15),
   (262144, ch36909KY.L16), (131072, ch36909KY.L17), (64, ch36909KY.L18), (32768, ch36909KY.L19),
   (2048, ch36909KY.L20), (128, ch36909KY.L21), (1024, ch36909KY.L22), (4194304, ch36909KY.L23)]

@[expose] noncomputable def ch36909ST : List (Nat × Nat) :=
  [(16384, ch36909KT.L0), (32768, ch36909KT.L1), (4, ch36909KT.L2), (64, ch36909KT.L3),
   (4194304, ch36909KT.L4), (2, ch36909KT.L5), (4096, ch36909KT.L6), (1024, ch36909KT.L7),
   (262144, ch36909KT.L8), (1048576, ch36909KT.L9), (8388608, ch36909KT.L10), (8, ch36909KT.L11),
   (2097152, ch36909KT.L12), (131072, ch36909KT.L13), (16, ch36909KT.L14),
   (524288, ch36909KT.L15), (128, ch36909KT.L16), (65536, ch36909KT.L17), (1, ch36909KT.L18),
   (8192, ch36909KT.L19), (2048, ch36909KT.L20), (256, ch36909KT.L21), (512, ch36909KT.L22),
   (32, ch36909KT.L23)]

@[expose] noncomputable def ch36909eqL (L : List (Nat × Nat)) : List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool)
    (fun M => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) M)
    (fun a _ ih M => List.rec (motive := fun _ => Bool) false
      (fun b M' _ => Nat.beq a.1 b.1 && Nat.beq a.2 b.2 && ih M') M) L

@[expose] noncomputable def ch36909sel (b : Bool) : List (Nat × Nat) :=
  Bool.rec ch36909ST ch36909SY b

@[expose] noncomputable def ch36909go (bs : List Bool) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun b _ ih S => strict (Nat.lor S (img (ch36909sel b) S)) ih) bs

@[expose] def ch36909I (S : Nat) : Prop :=
  S < 2 ^ 2 ^ 24 ∧ ∀ q < 2 ^ 24, S.testBit q = true →
    Back (vecMulN 24 cY.toArray) (vecMulN 24 cT.toArray) 2 q

theorem ch36909strict {α : Sort u} (y : Nat) (k : Nat → α) : strict y k = k y := by
  cases y <;> rfl

theorem ch36909mapRevK {α : Sort u} (f : Nat → Nat) :
    ∀ (xs acc : List Nat) (k : List Nat → α), mapRevK f xs acc k = k (mapRevK f xs acc id)
  | [], _, _ => rfl
  | x :: xs, acc, k => by
    change strict (f x) (fun y => mapRevK f xs (y :: acc) k) =
      k (strict (f x) fun y => mapRevK f xs (y :: acc) id)
    rw [ch36909strict, ch36909strict]
    exact ch36909mapRevK f xs _ k

theorem ch36909prepK {α : Sort u} (pms : List Nat) :
    ∀ (ops acc : List (Nat × Nat)) (k : List (Nat × Nat) → α),
      prepK pms ops acc k = k (prepK pms ops acc id)
  | [], _, _ => rfl
  | o :: ops, acc, k => by
    change strict (opMask pms o) (fun m => strict (Nat.shiftLeft 1 o.1) fun s =>
        prepK pms ops ((s, m) :: acc) k) =
      k (strict (opMask pms o) fun m => strict (Nat.shiftLeft 1 o.1) fun s =>
        prepK pms ops ((s, m) :: acc) id)
    rw [ch36909strict, ch36909strict, ch36909strict, ch36909strict]
    exact ch36909prepK pms ops _ k

theorem ch36909ctx1 {α : Sort u} (ops : List (Nat × Nat)) (F : List (Nat × Nat) → α) :
    (withPms fun pms => withPrep pms ops F) = F (ch36909P ops) :=
  (ch36909mapRevK _ _ _ _).trans (ch36909prepK _ _ _ _)

theorem ch36909P_eq (ops : List (Nat × Nat)) : ch36909P ops = ops.map stp := by
  have hp : withPms (id : List Nat → List Nat) = pms24 := withPms_eq id
  unfold ch36909P
  rw [hp, CFSG.KS.F2Set24.withPrep_eq]
  rfl

theorem ch36909eqL_eq : ∀ L M : List (Nat × Nat), ch36909eqL L M = true → L = M
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | a :: L, b :: M, h => by
    change (Nat.beq a.1 b.1 && Nat.beq a.2 b.2 && ch36909eqL L M) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [Prod.ext h1 h2, ch36909eqL_eq L M h3]

theorem ch36909S_eq {ops L : List (Nat × Nat)}
    (h : (withPms fun pms => withPrep pms ops fun P => ch36909eqL P L) = true) :
    L = ops.map stp := by
  rw [← ch36909P_eq]
  exact (ch36909eqL_eq _ _ ((ch36909ctx1 ops (fun P => ch36909eqL P L)).symm.trans h)).symm

theorem ch36909step {ops : List (Nat × Nat)} {c : List Nat} (hops : opsOK c ops = true)
    (hb : ∀ v, Back (vecMulN 24 cY.toArray) (vecMulN 24 cT.toArray) 2 (vecMulN 24 c.toArray v) →
      Back (vecMulN 24 cY.toArray) (vecMulN 24 cT.toArray) 2 v)
    {S : Nat} (hS : ch36909I S) : ch36909I (Nat.lor S (img (ops.map stp) S)) := by
  obtain ⟨hok, hF⟩ := opsOK_facts hops
  obtain ⟨hlt, hS⟩ := hS
  refine ⟨Nat.or_lt_two_pow hlt (img_lt hok hlt), fun q hq h => ?_⟩
  change (S ||| img (ops.map stp) S).testBit q = true at h
  rw [Nat.testBit_or, img_bits hok, ite_eq_left hq] at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact hS q hq h
  · have := hS _ (opsApp_lt hok hq) h
    rw [hF q hq] at this
    exact hb q this

theorem ch36909go_inv {bs : List Bool} (hY : ∀ S, ch36909I S → ch36909I (Nat.lor S (img ch36909SY S)))
    (hT : ∀ S, ch36909I S → ch36909I (Nat.lor S (img ch36909ST S))) :
    ∀ S, ch36909I S → ch36909I (ch36909go bs S) := by
  induction bs with
  | nil => exact fun S h => h
  | cons b bs ih =>
    intro S hS
    change ch36909I (strict (Nat.lor S (img (ch36909sel b) S)) (ch36909go bs))
    rw [ch36909strict]
    cases b
    · exact ih _ (hT S hS)
    · exact ih _ (hY S hS)

theorem ch36909I_init : ch36909I 4 := by
  refine ⟨lt_of_lt_of_le (by norm_num : 4 < 2 ^ 3)
    (Nat.pow_le_pow_right (by norm_num) (by norm_num)), fun q _ h => ?_⟩
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.testBit_two_pow, decide_eq_true_eq] at h
  subst h
  exact Back.base

theorem ch36909pc_sound {A : Nat} (h : (withPms fun pms => Nat.beq (popc pms A) 98280) = true) :
    popc pms24 A = 98280 := by
  rw [withPms_eq] at h
  exact Nat.eq_of_beq_eq_true h

theorem ch36909I_of {bs : List Bool} {A B : Nat}
    (hY : ∀ S, ch36909I S → ch36909I (Nat.lor S (img ch36909SY S)))
    (hT : ∀ S, ch36909I S → ch36909I (Nat.lor S (img ch36909ST S)))
    (hA : ch36909I A) (h : Nat.beq (ch36909go bs A) B = true) : ch36909I B :=
  Nat.eq_of_beq_eq_true h ▸ ch36909go_inv hY hT A hA

theorem ch36909transfer {ops : List (Nat × Nat)} (hok : ∀ o ∈ ops, OK o) {LE LB : List Nat}
    (hLE : ∀ w ∈ LE, w < 2 ^ 24) (hmap : LE.map (opsApp ops) = LB) {A : Nat}
    (h : ∀ x < 2 ^ 24, (img (ops.map stp) A).testBit x = true → x ∉ LE →
      (LE.countP fun w => (img (ops.map stp) A).testBit (x ^^^ w)) ≤ 9) :
    ∀ y < 2 ^ 24, A.testBit y = true → y ∉ LB → (LB.countP fun w => A.testBit (y ^^^ w)) ≤ 9 := by
  intro y hy hA hn
  have hinj := opsApp_inj hok
  have himg : (Finset.range (2 ^ 24)).image (opsApp ops) = Finset.range (2 ^ 24) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
      exact Finset.mem_range.2 (opsApp_lt hok (Finset.mem_range.1 hx))
    · rw [Finset.card_image_of_injective _ hinj]
  have hy' : y ∈ (Finset.range (2 ^ 24)).image (opsApp ops) := by
    rw [himg]
    exact Finset.mem_range.2 hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy'
  rw [Finset.mem_range] at hx
  have hbit : ∀ z < 2 ^ 24, (img (ops.map stp) A).testBit z = A.testBit (opsApp ops z) :=
    fun z hz => by simp only [img_bits hok, hz, ↓reduceIte]
  have h1 := h x hx (by rw [hbit x hx]; exact hA)
    (fun hm => hn (hmap ▸ List.mem_map_of_mem hm))
  rw [← hmap, List.countP_map]
  refine le_of_eq_of_le (List.countP_congr fun w hw => ?_) h1
  rw [Function.comp_apply, hbit _ (Nat.xor_lt_two_pow hx (hLE w hw)), opsApp_xor]

theorem ch36909D_one (w : ℕ) : ∀ M : ℕ, D w (fun _ => 1) M * (2 ^ w - 1) + 1 = 2 ^ (w * M)
  | 0 => by simp [D]
  | M + 1 => by
    have ih := ch36909D_one w M
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ w = t + 1 :=
      ⟨2 ^ w - 1, by have := Nat.one_le_two_pow (n := w); omega⟩
    change (1 + 2 ^ w * D w (fun _ => 1) M) * (2 ^ w - 1) + 1 = 2 ^ (w * (M + 1))
    rw [Nat.mul_succ, pow_add, ← ih, ht, Nat.add_sub_cancel]
    ring

theorem ch36909D_mul (w a : ℕ) :
    ∀ (M : ℕ) (f : ℕ → ℕ), a * D w f M = D w (fun j => a * f j) M
  | 0, f => by simp [D]
  | M + 1, f => by
    simp only [D]
    rw [← ch36909D_mul w a M (fun j => f (j + 1))]
    ring

theorem ch36909R_eq : ch36909R = D (2 ^ 6) (fun _ => 1) (2 ^ 18) := by
  have h := ch36909D_one (2 ^ 6) (2 ^ 18)
  have hW : W = 2 ^ 6 * 2 ^ 18 := by norm_num [W]
  unfold ch36909R
  rw [hW, ← h, Nat.add_sub_cancel]
  exact Nat.mul_div_cancel _ (by norm_num)

theorem ch36909take : pms24.take 6 = (List.range' 0 6).map pmask := rfl

theorem ch36909popG {M S : ℕ} (hM : ∀ q, M.testBit q = decide (q < 2 ^ 24)) :
    ∀ (L k c : ℕ), k + L ≤ 24 → c = D (2 ^ k) (cnt S k) (2 ^ (24 - k)) →
      popG M ((List.range' k L).map pmask) (2 ^ k) c =
        D (2 ^ (k + L)) (cnt S (k + L)) (2 ^ (24 - (k + L)))
  | 0, k, c, _, hc => hc
  | L + 1, k, c, hk, hc => by
    rw [List.range'_succ, List.map_cons, popG_cons, ← pow_succ',
      pop_step hM (by omega) c (by rw [hc, show 24 - k = 23 - k + 1 by omega, pow_succ']),
      show 23 - k = 24 - (k + 1) by omega, ch36909popG hM L (k + 1) _ (by omega) rfl,
      show k + 1 + L = k + (L + 1) by omega]

theorem ch36909cnt_le (S k j : ℕ) : cnt S k j ≤ 2 ^ k := by
  calc cnt S k j ≤ (Finset.Ico (2 ^ k * j) (2 ^ k * j + 2 ^ k)).card := by
        unfold cnt
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp ⊢
        obtain ⟨_, _, hpj⟩ := hp
        have h1 := Nat.div_add_mod p (2 ^ k)
        have h2 := Nat.mod_lt p (Nat.two_pow_pos k)
        rw [hpj] at h1
        generalize 2 ^ k * j = a at h1 ⊢
        generalize 2 ^ k = b at h1 h2 ⊢
        omega
    _ = 2 ^ k := by simp

theorem ch36909blk2_cnt {opsM : List (Nat × Nat)} {A : Nat} (hwf : opsWF opsM = true)
    (hA : A < 2 ^ 2 ^ 24) (h : ch36909blk2 opsM A = true) (j : ℕ) (hj : 1 ≤ j)
    (hjN : j < 2 ^ 18) : cnt (img (opsM.map stp) A) 6 j ≤ 9 := by
  have hok := opsWF_ok hwf
  generalize hS : img (opsM.map stp) A = S
  have hSlt : S < 2 ^ 2 ^ 24 := hS ▸ img_lt hok hA
  obtain ⟨M, hM, hpop⟩ := popAux_eq_popG
  have hc := ch36909popG (S := S) hM 6 0 S (by omega) (cnt_init hSlt)
  rw [pow_zero, Nat.zero_add, show 24 - 6 = 18 from rfl] at hc
  have h' : (((popAux (pms24.take 6) 1 S + 118 * ch36909R) >>> 64) &&&
      (ch36909R <<< 7)) = 0 := by
    unfold ch36909blk2 at h
    rw [withPms_eq, CFSG.KS.F2Set24.withPrep_eq, CFSG.KS.F2Set24.strict_eq,
      CFSG.KS.F2Set24.strict_eq, hS] at h
    exact Nat.eq_of_beq_eq_true h
  rw [hpop, ch36909take, hc, ch36909R_eq, ch36909D_mul, ← D_add] at h'
  have hbits := congrArg (fun z => z.testBit (64 * (j - 1) + 7)) h'
  have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have hF : ∀ i < 2 ^ 18, cnt S 6 i + 118 * 1 < 2 ^ 2 ^ 6 := fun i _ => by
    have := ch36909cnt_le S 6 i
    rw [h64] at this ⊢
    omega
  have h1 : ∀ i < 2 ^ 18, (fun _ => 1) i < 2 ^ 2 ^ 6 := fun i _ => by norm_num
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.zero_testBit,
    testBit_D (Nat.two_pow_pos 6) _ _ hF, testBit_D (Nat.two_pow_pos 6) _ _ h1, h64] at hbits
  have e1 : (64 + (64 * (j - 1) + 7)) / 64 = j := by omega
  have e2 : (64 + (64 * (j - 1) + 7)) % 64 = 7 := by omega
  have e3 : (64 * (j - 1) + 7 - 7) / 64 = j - 1 := by omega
  have e4 : (64 * (j - 1) + 7 - 7) % 64 = 0 := by omega
  have e5 : j - 1 < 2 ^ 18 := by omega
  simp only [e1, e2, e3, e4, e5, hjN, decide_true, Bool.true_and, Nat.testBit_zero,
    show 7 ≤ 64 * (j - 1) + 7 by omega, Bool.and_true] at hbits
  have hle := ch36909cnt_le S 6 j
  rw [Nat.testBit_eq_decide_div_mod_eq] at hbits
  simp only [decide_eq_false_iff_not] at hbits
  rw [h64] at hle
  omega

theorem ch36909countP_le {S x : ℕ} {L : List ℕ} (hL : L.Nodup) (h64 : ∀ w ∈ L, w < 64)
    (hx : x < 2 ^ 24) : (L.countP fun w => S.testBit (x ^^^ w)) ≤ cnt S 6 (x / 64) := by
  rw [List.countP_eq_length_filter]
  have hnd : ((L.filter fun w => S.testBit (x ^^^ w)).map (x ^^^ ·)).Nodup :=
    (hL.filter _).map (fun a b hab => by simpa using congrArg (x ^^^ ·) hab)
  rw [← List.length_map (f := (x ^^^ ·)), ← List.toFinset_card_of_nodup hnd]
  unfold cnt
  apply Finset.card_le_card
  intro v hv
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hv
  obtain ⟨w, ⟨hw, hSw⟩, rfl⟩ := hv
  have hw64 := h64 w hw
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.xor_lt_two_pow hx (by omega), by simpa using hSw, ?_⟩
  rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by norm_num; omega : w < 2 ^ 6), Nat.xor_zero]

theorem ch36909Eall : ∀ v < 64, v ∈ grayWs ch36909E ch36909gray 0 := by decide

theorem ch36909Elt : ∀ w ∈ grayWs ch36909E ch36909gray 0, w < 64 := by decide

theorem ch36909End : (grayWs ch36909E ch36909gray 0).Nodup := by decide

theorem ch36909blk2_sound {opsM : List (Nat × Nat)} {A : Nat} (hwf : opsWF opsM = true)
    (hA : A < 2 ^ 2 ^ 24) (h : ch36909blk2 opsM A = true) :
    ∀ x < 2 ^ 24, (img (opsM.map stp) A).testBit x = true →
      x ∉ grayWs ch36909E ch36909gray 0 → ((grayWs ch36909E ch36909gray 0).countP fun w =>
        (img (opsM.map stp) A).testBit (x ^^^ w)) ≤ 9 := by
  intro x hx _ hn
  have h64 : 64 ≤ x := by
    by_contra hlt
    exact hn (ch36909Eall x (by omega))
  have h24 : (2 : ℕ) ^ 24 = 64 * 2 ^ 18 := by norm_num
  exact (ch36909countP_le ch36909End ch36909Elt hx).trans
    (ch36909blk2_cnt hwf hA h _ (by omega) (by omega))

theorem ch36909bY : opsOK cY ch36909Y = true := by quickRfl

theorem ch36909bT : opsOK cT ch36909T = true := by quickRfl

theorem ch36909sY :
    (withPms fun pms => withPrep pms ch36909Y fun P => ch36909eqL P ch36909SY) = true := by
  quickRfl

theorem ch36909sT :
    (withPms fun pms => withPrep pms ch36909T fun P => ch36909eqL P ch36909ST) = true := by
  quickRfl

theorem ch36909o0 :
    Nat.beq (ch36909go [true, false, true, false, true] 4) ch36909O.L0 = true := by quickRfl

theorem ch36909o1 :
    Nat.beq (ch36909go [false, true, false, true, false] ch36909O.L0) ch36909O.L1 = true := by
  quickRfl

theorem ch36909o2 :
    Nat.beq (ch36909go [true, false, true, false, true] ch36909O.L1) ch36909O.L2 = true := by
  quickRfl

theorem ch36909o3 :
    Nat.beq (ch36909go [false, true, false, true, false] ch36909O.L2) ch36909O.L3 = true := by
  quickRfl

theorem ch36909o4 :
    Nat.beq (ch36909go [true, false, true, false, true] ch36909O.L3) ch36909O.L4 = true := by
  quickRfl

theorem ch36909o5 :
    Nat.beq (ch36909go [false, true, false, true] ch36909O.L4) ch36909O.L5 = true := by quickRfl

theorem ch36909o6 :
    Nat.beq (ch36909go [false, true, false, true] ch36909O.L5) ch36909O.L6 = true := by quickRfl

theorem ch36909o7 :
    Nat.beq (ch36909go [false, true, false, true] ch36909O.L6) ch36909O.L7 = true := by quickRfl

theorem ch36909pc : (withPms fun pms => Nat.beq (popc pms ch36909O.L7) 98280) = true := by
  quickRfl

theorem ch36909bm : ch36909blk2 ch36909M ch36909O.L7 = true := by quickRfl

theorem ch36909bwf : opsWF ch36909M = true := by quickRfl

theorem ch36909bmap : (grayWs ch36909E ch36909gray 0).map (opsApp ch36909M) =
    grayWs ch36909WB ch36909gray 0 := by decide

theorem ch36909bE : ∀ b ∈ ch36909E, b < 2 ^ 24 := by decide

theorem ch36909orb : ∃ S : Nat, ch36909I S ∧
    ((Finset.range (2 ^ 24)).filter (fun v => S.testBit v = true)).card = 98280 ∧
    ∀ x < 2 ^ 24, S.testBit x = true → x ∉ grayWs ch36909WB ch36909gray 0 →
      ((grayWs ch36909WB ch36909gray 0).countP fun w => S.testBit (x ^^^ w)) ≤ 9 := by
  have hY : ∀ S, ch36909I S → ch36909I (Nat.lor S (img ch36909SY S)) := fun S hS => by
    rw [ch36909S_eq ch36909sY]
    exact ch36909step ch36909bY (fun _ h => Back.sf h) hS
  have hT : ∀ S, ch36909I S → ch36909I (Nat.lor S (img ch36909ST S)) := fun S hS => by
    rw [ch36909S_eq ch36909sT]
    exact ch36909step ch36909bT (fun _ h => Back.sg h) hS
  have h0 := ch36909I_of hY hT ch36909I_init ch36909o0
  have h1 := ch36909I_of hY hT h0 ch36909o1
  have h2 := ch36909I_of hY hT h1 ch36909o2
  have h3 := ch36909I_of hY hT h2 ch36909o3
  have h4 := ch36909I_of hY hT h3 ch36909o4
  have h5 := ch36909I_of hY hT h4 ch36909o5
  have h6 := ch36909I_of hY hT h5 ch36909o6
  have h7 := ch36909I_of hY hT h6 ch36909o7
  refine ⟨_, h7, ?_, ch36909transfer (opsWF_ok ch36909bwf)
    (grayWs_lt ch36909bE ch36909gray 0 (by positivity)) ch36909bmap
    (ch36909blk2_sound ch36909bwf h7.1 ch36909bm)⟩
  exact (popc_eq h7.1).symm.trans (ch36909pc_sound ch36909pc)

end CertificateChecks.KernelCo1Pump

end
