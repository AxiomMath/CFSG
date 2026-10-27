module

public import Certificates.Data.CFSGNative.Co1K105.Check
public import Certificates.Data.Kernel.Co1K105.LettersCheck
public import Certificates.Kernel.Co1K105.LettersChecks
public import Certificates.Kernel.Co1Cover.Bridge
public import Certificates.Kernel.Co1B.C2044
import CFSG.Certificates.Kernel.Co1BInvSound

public section

set_option exponentiation.threshold 2048

namespace CFSG.KD.Co1K105

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.Loop CertificateChecks.KernelCo1Cover
  CFSG.KD.Co1B CertificateChecks.KernelCo1B.C2044
open CFSG.Sporadic.Co1Schreier.Native (mul inv one pow Rows)

theorem lkg_strictB (y : Nat) (k : Nat → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

theorem lkg_andB (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem lkg_mulWK (A B : Nat) : mulWK A B = mulK A B := CFSG.KC.F2W.mulW_eq 24 A B

theorem lkg_mul (A B : Nat) : mul (unpackR 24 A) (unpackR 24 B) = unpackR 24 (mulWK A B) := by
  rw [lkg_mulWK]
  exact mul_unpack A B

theorem lkg_inv {G GI : Nat} (h : Nat.beq (mulWK G GI) oneK = true) :
    inv (unpackR 24 G) = unpackR 24 GI :=
  CFSG.KC.F2W.inv_unpackR (by rw [← CFSG.KC.F2W.mulW_eq]; exact Nat.eq_of_beq_eq_true h)

theorem lkg_eqK_self (A : Nat) : eqK A A = true := Nat.beq_refl _

theorem lkg_unpack_eq {A B : Nat} (h : eqK A B = true) : unpackR 24 A = unpackR 24 B := by
  have h' := beq_unpack A B
  rw [h] at h'
  exact eq_of_beq h'

theorem lkg_sh : Nat.shiftLeft 1 576 = 2 ^ 576 := by
  change 1 <<< 576 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem lkg_rec (z : Nat) (s : Nat → Nat → Nat) (n : Nat) :
    Nat.rec (motive := fun _ => Nat) z s (n + 1) = s n (Nat.rec (motive := fun _ => Nat) z s n) :=
  rfl

theorem lkg_eqK_can {A B : Nat} (hA : A < 2 ^ 576) (hB : B < 2 ^ 576) : eqK A B = Nat.beq A B := by
  change Nat.beq (A % Nat.shiftLeft 1 576) (B % Nat.shiftLeft 1 576) = _
  rw [lkg_sh, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB]

theorem lkg_fget (X i w : Nat) : fget X i w = X / 2 ^ (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& ((1 <<< w) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem lkg_getLL : ∀ (L : List (List Nat)) (l : Nat), lkGetLL L l = L.getD l []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, l + 1 => lkg_getLL L l

theorem lkg_pair : ∀ (L : List (Nat × Nat)) (j : Nat), lkPair L j = L.getD j (0, 0)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, j + 1 => lkg_pair L j

theorem lkg_allN {f : Nat → Bool} : ∀ {n : Nat}, allN n f = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have h' : andB (f n) (allN n f) = true := h
    rw [lkg_andB, Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact lkg_allN h'.2 i hi
    · exact h'.1

theorem lkg_lane : ∀ (QL : List Nat), (∀ x ∈ QL, x < 2 ^ 576) →
    ∀ p, fget (lkPack QL) p 576 = getL 0 QL p
  | [], _, p => by
    rw [lkg_fget]
    change 0 / 2 ^ (p * 576) % 2 ^ 576 = 0
    rw [Nat.zero_div, Nat.zero_mod]
  | x :: t, h, p => by
    have hx := h x List.mem_cons_self
    have ht := lkg_lane t fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hp : lkPack (x :: t) = lkPack t * 2 ^ 576 + x := by
      change x ||| (lkPack t <<< 576) = _
      rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
    rw [lkg_fget, hp]
    cases p with
    | zero =>
      rw [Nat.zero_mul, Nat.pow_zero, Nat.div_one, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
      rfl
    | succ p =>
      have h2 : 2 ^ ((p + 1) * 576) = 2 ^ 576 * 2 ^ (p * 576) := by
        rw [← Nat.pow_add]
        congr 1
        ring
      rw [h2, ← Nat.div_div_eq_div_mul, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 576),
        Nat.div_eq_of_lt hx, Nat.zero_add, ← lkg_fget, ht p]
      rfl

theorem lkg_chunks (P : Nat → Nat → Bool) : ∀ (ch : List Nat) (c : Nat), lkChunks P ch c = true →
    ∀ i (hi : i < ch.length) k, k < 40 → 40 * (c + i) + k < 512 →
      P (40 * (c + i) + k) (fget ch[i] k 9) = true
  | [], _, _, i, hi, _, _, _ => absurd hi (Nat.not_lt_zero i)
  | x :: t, c, h, i, hi, k, hk, hp => by
    have h' : ((allN 40 fun k => Bool.rec (motive := fun _ => Bool) true (P (40 * c + k) (fget x k 9))
        (Nat.blt (40 * c + k) 512)) && lkChunks P t (c + 1)) = true := by
      rw [← lkg_andB]
      exact h
    rw [Bool.and_eq_true] at h'
    cases i with
    | zero =>
      have h1 := lkg_allN h'.1 k hk
      have hb : Nat.blt (40 * c + k) 512 = true := by
        rw [Nat.blt_eq]
        simpa using hp
      rw [hb] at h1
      simpa using h1
    | succ i =>
      have h2 := lkg_chunks P t (c + 1) h'.2 i (by simpa using hi) k hk (by
        have : 40 * (c + 1 + i) = 40 * (c + (i + 1)) := by ring
        omega)
      have : 40 * (c + 1 + i) = 40 * (c + (i + 1)) := by ring
      rw [this] at h2
      simpa using h2

theorem lkg_qElt (a : Nat) (QG : List Nat) (qs : List Rows)
    (hqs : ∀ j < 8, qs.getD j one = unpackR 24 (getL oneK QG j)) (i : Nat) :
    qElt one (unpackR 24 a) qs i = unpackR 24 (lkQ a QG i) := by
  have key : ∀ n ≤ 8, (List.range n).foldl
      (fun x j => if i.testBit j then mul x (qs.getD j one) else x) one =
      unpackR 24 (Nat.rec (motive := fun _ => Nat) oneK
        (fun j acc => strictN acc fun x => nIf(bit i j, mulWK x (getL oneK QG j), x)) n) := by
    intro n hn
    induction n with
    | zero => exact one_eq
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
      simp only [lkg_rec, CFSG.KC.F2W.strictN_eq, CFSG.KC.F2W.bit_eq]
      cases hb : i.testBit n
      · rw [if_neg (by simp)]
      · rw [if_pos rfl, hqs n (by omega), lkg_mul]
  unfold qElt lkQ
  simp only [key 8 le_rfl, CFSG.KC.F2W.strictN_eq, CFSG.KC.F2W.bit_eq]
  cases hb : i.testBit 8
  · rw [if_neg (by simp)]
    rfl
  · rw [if_pos rfl, lkg_mul]
    rfl

theorem lkg_word (x y len code : Nat) :
    wordRows one (unpackR 24 x) (unpackR 24 y) (wordOf len code) =
      unpackR 24 (lkWord x y len code) := by
  unfold wordRows wordOf lkWord
  induction len with
  | zero => exact one_eq
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [lkg_rec, CFSG.KC.F2W.strictN_eq, CFSG.KC.F2W.bit_eq, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil]
    cases hb : code.testBit n
    · rw [if_neg (by simp), lkg_mul]
    · rw [if_pos rfl, lkg_mul]

theorem lkg_rows (a : Nat) (QG : List Nat) : ∀ (QL : List Nat) (i0 : Nat), lkRows a QG QL i0 = true →
    ∀ k (hk : k < QL.length), QL[k] < 2 ^ 576 ∧ eqK QL[k] (lkQ a QG (i0 + k)) = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | x :: t, i0, h, k, hk => by
    have h' : CFSG.KC.M1F2.strictB i0 (fun i => andB (andB (canK x) (eqK x (lkQ a QG i)))
        (lkRows a QG t (Nat.succ i))) = true := h
    rw [lkg_strictB, lkg_andB, lkg_andB, Bool.and_eq_true, Bool.and_eq_true] at h'
    cases k with
    | zero =>
      refine ⟨?_, h'.1.2⟩
      have hc : Nat.blt x (Nat.shiftLeft 1 576) = true := h'.1.1
      rwa [lkg_sh, Nat.blt_eq] at hc
    | succ k =>
      have := lkg_rows a QG t (i0 + 1) h'.2 k (by simpa using hk)
      rw [Nat.add_assoc, Nat.add_comm 1 k] at this
      exact this

theorem lkg_ne (x : Nat) : ∀ t : List Nat, lkNe x t = true → x ∉ t
  | [], _ => List.not_mem_nil
  | y :: t, h => by
    have h' : andB (notB (Nat.beq x y)) (lkNe x t) = true := h
    rw [lkg_andB, Bool.and_eq_true] at h'
    have hxy : x ≠ y := by
      intro e
      have h1 := h'.1
      rw [e, Nat.beq_refl] at h1
      exact Bool.false_ne_true h1
    exact List.not_mem_cons_of_ne_of_not_mem hxy (lkg_ne x t h'.2)

theorem lkg_dist : ∀ QL : List Nat, lkDist QL = true → QL.Nodup
  | [], _ => List.nodup_nil
  | x :: t, h => by
    have h' : andB (lkNe x t) (lkDist t) = true := h
    rw [lkg_andB, Bool.and_eq_true] at h'
    exact List.nodup_cons.2 ⟨lkg_ne x t h'.1, lkg_dist t h'.2⟩

theorem lkg_qTable {QL QG : List Nat} {qs : List Rows} {Q : Array Rows} (hlen : QL.length = 512)
    (hcan : ∀ k < 512, getL 0 QL k < 2 ^ 576) (hnd : QL.Nodup)
    (hQ : ∀ i < 512, Q[i]! = unpackR 24 (getL 0 QL i))
    (hg : ∀ j < 8, eqK (getL 0 QL (2 ^ j)) (getL oneK QG j) = true)
    (hqs : ∀ j < 8, qs.getD j one = unpackR 24 (getL oneK QG j)) :
    qTableOK one Q qs = true := by
  unfold qTableOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun i hi => ⟨?_, fun j hj => ?_⟩, fun j hj => ?_⟩
  · rw [hQ i hi]
    exact validRows_unpackR _
  · rw [hQ i hi, hQ j (by omega), bne, beq_unpack, lkg_eqK_can (hcan i hi) (hcan j (by omega))]
    have hne : getL 0 QL i ≠ getL 0 QL j := by
      rw [getL_eq, getL_eq, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some, Option.getD_some]
      intro e
      have := (hnd.getElem_inj_iff).1 e
      omega
    cases hb : Nat.beq (getL 0 QL i) (getL 0 QL j)
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hne
  · have h2 : 2 ^ j < 512 := by
      have : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [hQ _ h2, hqs j hj, beq_unpack]
    exact hg j hj

theorem lkg_letter {QL : List Nat} (hcan : ∀ x ∈ QL, x < 2 ^ 576) {Q : Array Rows}
    (hQ : ∀ i < 512, Q[i]! = unpackR 24 (getL 0 QL i)) (l : Nat) {G GI : Nat}
    (h : lkLetter (lkPack QL) (lkGetLL letters l) G GI = true) :
    letterOK one Q L l (unpackR 24 G) = true := by
  unfold lkLetter at h
  rw [lkg_strictB, lkg_strictB, lkg_strictB, lkg_andB, lkg_andB, Bool.and_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hlen : (lkGetLL letters l).length = 13 := by
    rw [← lenL_eq]
    exact Nat.eq_of_beq_eq_true h2
  have hc := lkg_chunks _ _ 0 h3
  unfold letterOK
  simp only [lkg_inv h1, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  have hL : ∀ i, L l i < 512 := fun i => Nat.mod_lt _ (by decide)
  refine ⟨?_, fun i hi => ⟨hL i, ?_⟩⟩
  · rw [lkg_mul, one_eq, beq_unpack, Nat.eq_of_beq_eq_true h1]
    exact lkg_eqK_self _
  · rw [hQ i hi, hQ _ (hL i), lkg_mul, lkg_mul, beq_unpack]
    have hi40 : i / 40 < (lkGetLL letters l).length := by
      rw [hlen]
      omega
    have h4 := hc (i / 40) hi40 (i % 40) (Nat.mod_lt _ (by decide)) (by omega)
    have hp : 40 * (0 + i / 40) + i % 40 = i := by omega
    rw [hp, lkg_lane QL hcan, lkg_lane QL hcan] at h4
    have hLi : L l i = fget (lkGetLL letters l)[i / 40] (i % 40) 9 := by
      rw [lkg_fget, ← List.getD_eq_getElem _ 0 hi40, lkg_getLL]
      change ((letters.getD l []).getD (i / 40) 0 >>> (9 * (i % 40))) % 512 = _
      rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm 9]
      rfl
    rw [hLi]
    exact h4

theorem rr0 : CFSG.Sporadic.Co1.Cover.rrCov 0 = unpackR 24 R0 := by
  rw [CFSG.Sporadic.Co1.Cover.rrCov, regs_eq]
  rfl

theorem lkg_eps {i : Nat} (hi : i < 11) :
    CFSG.Sporadic.Co1.Cover.epsRows[i]! = unpackR 24 (getL oneK E i) := by
  have hl : E.length = 11 := rfl
  rw [epsRows_eq, getL_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp [hl, hi]

theorem lkQG_eq : lkQG = CertificateChecks.KernelCo1B.IQK := by decide +kernel

theorem lkCodes_eq : lkCodes = t24Codes := by decide +kernel

theorem lkg_qs {j : Nat} (hj : j < 8) :
    (CertificateChecks.KernelCo1B.IQK.map (unpackR 24)).getD j one = unpackR 24 (getL oneK lkQG j) := by
  have hl : CertificateChecks.KernelCo1B.IQK.length = 8 := by simp [CertificateChecks.KernelCo1B.IQK]
  rw [lkQG_eq, getL_eq, List.getElem?_eq_getElem (by omega), Option.getD_some,
    List.getD_eq_getElem _ _ (by simp [hl, hj]), List.getElem_map]

theorem lkg_ws {j : Nat} (hj : j < 4) :
    (t24Codes.map fun c => wordOf c.1 c.2).getD j [] = wordOf (lkPair lkCodes j).1 (lkPair lkCodes j).2 := by
  have hl : t24Codes.length = 4 := rfl
  rw [lkg_pair, lkCodes_eq, List.getD_eq_getElem _ _ (by simp [hl, hj]),
    List.getD_eq_getElem _ _ (by omega), List.getElem_map]

theorem lkg_bray {k : Nat} (hk : k < 8) :
    ((List.range CFSG.Sporadic.Co1Block.twoABray.length).map
      fun i => CFSG.KS.Raw.unpack 24 24 (D2.M i)).getD k one = unpackR 24 (D2.M k) := by
  have hl : CFSG.Sporadic.Co1Block.twoABray.length = 8 := rfl
  rw [List.getD_eq_getElem _ _ (by simp [hl, hk]), List.getElem_map, List.getElem_range,
    CFSG.KS.SporSch.M24.unpackR_eq_unpack]

theorem lkg_hz : CFSG.Sporadic.Co1.CoverNative.eprodRows CFSG.Sporadic.Co1.Cover.epsRows 3 =
    unpackR 24 (mulWK (mulWK oneK (getL oneK E 0)) (getL oneK E 1)) := by
  have h : ∀ eps : Array (Array Nat), CFSG.Sporadic.Co1.CoverNative.eprodRows eps 3 =
      mul (mul one eps[0]!) eps[1]! := fun _ => rfl
  rw [h, lkg_eps (by decide), lkg_eps (by decide), one_eq, lkg_mul, lkg_mul]

attribute [local irreducible] lkQL lkQG lkAI lkCI lkWI lkCodes IRS R0 R4 R5 E letters mulWK lkC
  lkPack D2.M D2.MI

theorem letters_k :
    co1KLettersCheck (CFSG.Sporadic.Co1.Cover.rrCov 0) (CFSG.Sporadic.Co1.Cover.rrCov 4)
      (CFSG.Sporadic.Co1.Cover.rrCov 5) CFSG.Sporadic.Co1Block.iotaARows
      CFSG.Sporadic.Co1.Cover.epsRows CFSG.Sporadic.Co1Block.twoAQRows
      (CFSG.Sporadic.Co1Block.Native.brayElts
        (CFSG.Sporadic.Co1Block.Native.brayRows CFSG.Sporadic.Co1Block.iotaARows
          CFSG.Sporadic.Co1Block.twoAD1) CFSG.Sporadic.Co1Block.twoABray)
      (t24Codes.map fun c => wordOf c.1 c.2) L = true := by
  rw [bray_eq, rr0, rr4, rr5, CertificateChecks.KernelCo1B.iotaA_eq, CertificateChecks.KernelCo1B.twoAQ_eq]
  have hh := lk_head
  unfold lkHead at hh
  rw [lkg_strictB, lkg_andB, lkg_andB, Bool.and_eq_true, Bool.and_eq_true] at hh
  obtain ⟨hA, hC, hZ⟩ := hh
  have hAi : inv (unpackR 24 R0) = unpackR 24 lkAI := lkg_inv hA
  have hC' : Nat.beq (mulWK lkCc lkCI) oneK = true := hC
  have hci : inv (unpackR 24 lkCc) = unpackR 24 lkCI := lkg_inv hC'
  have hc : mul (pow (mul (mul (mul (unpackR 24 R0)
      (CFSG.Sporadic.Co1.CoverNative.eprodRows CFSG.Sporadic.Co1.Cover.epsRows 3))
      (unpackR 24 lkAI)) (unpackR 24 (getL oneK IRS 23))) 2) (unpackR 24 R0) = unpackR 24 lkCc := by
    have hp : ∀ X, pow X 2 = mul (mul one X) X := fun _ => rfl
    rw [lkg_hz, lkg_mul, lkg_mul, lkg_mul, hp, one_eq, lkg_mul, lkg_mul, lkg_mul]
    unfold lkCc lkC
    simp only [CFSG.KC.F2W.strictN_eq]
  have hg := lk_gens
  unfold lkGens at hg
  rw [lkg_andB, Bool.and_eq_true] at hg
  have hlen : lkQL.length = 512 := by
    have h1 := Nat.eq_of_beq_eq_true hg.1
    rw [← lenL_eq, h1]
  have hrows := lkg_rows _ _ _ 0 lk_rows
  have hget : ∀ k (hk : k < 512), getL 0 lkQL k = lkQL[k]'(by rw [hlen]; exact hk) := fun k hk => by
    rw [getL_eq, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hcan' : ∀ k < 512, getL 0 lkQL k < 2 ^ 576 := fun k hk => by
    rw [hget k hk]
    exact (hrows k (by omega)).1
  have hcan : ∀ x ∈ lkQL, x < 2 ^ 576 := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    exact (hrows k hk).1
  have hQ : ∀ i < 512, ((Array.range 512).map (qElt one (unpackR 24 (getL oneK IRS 23))
      (CertificateChecks.KernelCo1B.IQK.map (unpackR 24))))[i]! = unpackR 24 (getL 0 lkQL i) := by
    intro i hi
    have hm : ((Array.range 512).map (qElt one (unpackR 24 (getL oneK IRS 23))
        (CertificateChecks.KernelCo1B.IQK.map (unpackR 24))))[i]! =
        qElt one (unpackR 24 (getL oneK IRS 23)) (CertificateChecks.KernelCo1B.IQK.map (unpackR 24)) i := by
      simp [hi]
    have hr := (hrows i (by omega)).2
    rw [Nat.zero_add] at hr
    rw [hm, lkg_qElt _ lkQG _ (fun j hj => lkg_qs hj), hget i hi]
    exact (lkg_unpack_eq hr).symm
  unfold co1KLettersCheck
  simp only [hAi, hc, hci, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [lkg_mul, one_eq, beq_unpack, Nat.eq_of_beq_eq_true hA]
    exact lkg_eqK_self _
  · rw [lkg_mul, one_eq, beq_unpack, Nat.eq_of_beq_eq_true hC']
    exact lkg_eqK_self _
  · rw [lkg_hz, lkg_mul, lkg_mul, beq_unpack]
    exact hZ
  · refine lkg_qTable hlen hcan' (lkg_dist _ lk_dist) hQ (fun j hj => ?_) (fun j hj => lkg_qs hj)
    have h := lkg_allN hg.2 j hj
    have hp : pw2 j = 2 ^ j := by
      change 1 <<< j = _
      rw [Nat.one_shiftLeft]
    rw [hp] at h
    exact h
  · intro i hi
    rw [lkg_eps hi, lkg_mul, lkg_mul]
    interval_cases i
    · exact lkg_letter hcan hQ _ lk_e0
    · exact lkg_letter hcan hQ _ lk_e1
    · exact lkg_letter hcan hQ _ lk_e2
    · exact lkg_letter hcan hQ _ lk_e3
    · exact lkg_letter hcan hQ _ lk_e4
    · exact lkg_letter hcan hQ _ lk_e5
    · exact lkg_letter hcan hQ _ lk_e6
    · exact lkg_letter hcan hQ _ lk_e7
    · exact lkg_letter hcan hQ _ lk_e8
    · exact lkg_letter hcan hQ _ lk_e9
    · exact lkg_letter hcan hQ _ lk_e10
  · intro j hj
    rw [lkg_ws hj, lkg_word, lkg_mul, lkg_mul]
    interval_cases j
    · exact lkg_letter hcan hQ _ lk_w0
    · exact lkg_letter hcan hQ _ lk_w1
    · exact lkg_letter hcan hQ _ lk_w2
    · exact lkg_letter hcan hQ _ lk_w3
  · rw [lkg_bray (by decide), lkg_bray (by decide), lkg_bray (by decide), lkg_mul, lkg_mul]
    exact lkg_letter hcan hQ _ lk_h
  · rw [lkg_bray (by decide)]
    exact lkg_letter hcan hQ _ lk_b0

end CFSG.KD.Co1K105

end
