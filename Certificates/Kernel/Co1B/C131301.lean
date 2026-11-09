module

public import Certificates.Data.E27.Co1S0
public import Certificates.Kernel.Co1B.Chk131301
public import Certificates.Kernel.Co1B.Scan131301
public import Certificates.Kernel.SporSch.Co1.Packed
public import CFSG.Certificates.Kernel.Co1BSpinSound
public import CFSG.Certificates.Kernel.Co1BPairSound
public import CFSG.Certificates.Kernel.Co1BTriKSound
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Co1BTriSortSound
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.S0131301

open CFSG.KC.Co1BS0 CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KLie.CT
  CFSG.KC.M1F2 CFSG.KC.StrNlSp CFSG.Sporadic.Co1.S0 CFSG.HardMathSupport.Foote.E27
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native

local notation "U" => unpackR 24

theorem isEmpty_ofList (p : List Char) : (String.ofList p).isEmpty = p.isEmpty := by
  cases p with
  | nil => rfl
  | cons c p =>
    simp only [List.isEmpty_cons]
    rw [Bool.eq_false_iff]
    intro h
    have h2 := congrArg String.toList (String.isEmpty_iff.1 h)
    simp at h2

theorem parseNats_ofList (cs : List Char) (h : goodNl cs = true) :
    parseNats (String.ofList cs) = (numsNl cs).toArray := by
  unfold parseNats numsNl
  have hr : (String.ofList cs).replace "\n" " " = String.ofList (cs.map nlSp) := by
    apply String.toList_injective
    rw [replace_nl_sp, String.toList_ofList, String.toList_ofList]
  have hsp : (" " : String) = String.singleton ' ' := by rw [String.singleton_eq_ofList]
  rw [hr, hsp, CFSG.KC.Str.splitOn_ofList, List.filter_map, List.map_toArray, List.map_map]
  congr 1
  have hf : ((fun t : String => !t.isEmpty) ∘ String.ofList) = fun p : List Char => !p.isEmpty := by
    funext p
    simp only [Function.comp_apply, isEmpty_ofList]
  rw [hf]
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
  have hne : p ≠ [] := by
    intro e
    subst e
    simp at hp2
  have hd : ∀ c ∈ p, c.isDigit = true := by
    have := List.all_eq_true.1 h p hp1
    exact fun c hc => List.all_eq_true.1 this c hc
  rw [Function.comp_apply, CFSG.KC.Str.toNat!_ofList hne hd]

theorem pairsL_length : ∀ l : List Nat, (pairsL l).length = l.length / 2
  | [] => by simp [pairsL]
  | [_] => by simp [pairsL]
  | a :: b :: t => by
    rw [pairsL, List.length_cons, pairsL_length t, List.length_cons, List.length_cons]
    omega

theorem pairsL_get : ∀ (l : List Nat) (i : Nat) (h : i < (pairsL l).length),
    (pairsL l)[i] = (l.getD (2 * i) 0, l.getD (2 * i + 1) 0)
  | [], _, h => absurd h (by simp [pairsL])
  | [_], _, h => absurd h (by simp [pairsL])
  | a :: b :: t, 0, _ => by simp [pairsL]
  | a :: b :: t, i + 1, h => by
    have h' : i < (pairsL t).length := by simpa [pairsL] using h
    simp only [pairsL, List.getElem_cons_succ]
    rw [pairsL_get t i h']
    have e1 : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
    have e2 : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by omega
    rw [e2, e1]
    simp only [List.getD_cons_succ]

theorem pairsOf_toArray (l : List Nat) : pairsOf l.toArray = (pairsL l).toArray := by
  unfold pairsOf
  apply Array.ext
  · simp [pairsL_length]
  · intro i h1 h2
    simp only [Array.getElem_ofFn, List.getElem_toArray]
    rw [pairsL_get l i (by simpa using h2), CFSG.KC.Co1BPair.get!_toArray,
      CFSG.KC.Co1BPair.get!_toArray]

@[expose] noncomputable def opsN : List Nat := numsNl OT.chars

@[expose] noncomputable def parN : List Nat := numsNl PT.chars

@[expose] noncomputable def LN : List Nat := numsNl LT.chars

theorem scans131 : (goodNl OT.chars = true ∧ opsN = nums131R OT.chars 0 false) ∧
    (goodNl PT.chars = true ∧ parN = nums131R PT.chars 0 false) ∧
    (goodNl LT.chars = true ∧ LN = nums131R LT.chars 0 false) := by
  have h := kGood
  simp only [Bool.and_eq_true] at h
  exact ⟨scan131 _ h.1.1, scan131 _ h.1.2, scan131 _ h.2⟩

theorem goods : goodNl OT.chars = true ∧ goodNl PT.chars = true ∧ goodNl LT.chars = true :=
  ⟨scans131.1.1, scans131.2.1.1, scans131.2.2.1⟩

theorem ops_eq : ops () = (pairsL opsN).toArray := by
  have h : ops () = pairsOf (parseNats opsStr) := rfl
  rw [h, OT.eq, parseNats_ofList _ goods.1, pairsOf_toArray]
  rfl

theorem par_eq : par () = (pairsL parN).toArray := by
  have h : par () = pairsOf (parseNats parStr) := rfl
  rw [h, PT.eq, parseNats_ofList _ goods.2.1, pairsOf_toArray]
  rfl

theorem L_eq : L () = Array.ofFn (n := 3) fun j => Array.ofFn (n := nS) fun i => LN.getD (j.val * nS + i.val) 0 := by
  have h : L () = Array.ofFn (n := 3) fun j => Array.ofFn (n := nS) fun i =>
      (parseNats LStr)[j.val * nS + i.val]! := rfl
  rw [h, LT.eq, parseNats_ofList _ goods.2.2]
  simp only [CFSG.KC.Co1BPair.get!_toArray]
  rfl

theorem L_get {j i : Nat} (hj : j < 3) (hi : i < nS) : ((L ())[j]!)[i]! = LN.getD (j * nS + i) 0 := by
  rw [L_eq]
  simp [hj, hi, getElem!_pos]

theorem opsK_sound {R : Nat → Nat} : ∀ {l : List (Nat × Nat)} {t : Nat}, opsK R l t = true →
    ∀ s (hs : s < l.length), l[s].1 < t + s + 3 ∧ l[s].2 < t + s + 3 ∧
      U (R (t + s + 3)) = U (mulWK (R l[s].1) (R l[s].2))
  | [], _, _ => fun s hs => absurd hs (Nat.not_lt_zero _)
  | o :: l, t, h => by
    change andB (Nat.blt o.1 (Nat.add t 3)) (andB (Nat.blt o.2 (Nat.add t 3))
      (andB (eqK (R (Nat.add t 3)) (mulWK (R o.1) (R o.2))) (strictB (Nat.succ t) (opsK R l)))) = true at h
    obtain ⟨h1, h⟩ := andB_true h
    obtain ⟨h2, h⟩ := andB_true h
    obtain ⟨h3, h4⟩ := andB_true h
    rw [strictB_eq'] at h4
    intro s hs
    cases s with
    | zero => exact ⟨Eq.mp Nat.blt_eq h1, Eq.mp Nat.blt_eq h2, beq_of_eqK h3⟩
    | succ s =>
      have := opsK_sound h4 s (by simpa using hs)
      have e : t + (s + 1) + 3 = Nat.succ t + s + 3 := by omega
      rw [List.getElem_cons_succ, e]
      exact this

theorem parK_sound {LG : Nat → Nat} : ∀ {l : List (Nat × Nat)} {i : Nat}, parK LG l i = true →
    ∀ s (hs : s < l.length), i + s ≠ 0 → l[s].1 < i + s ∧ l[s].2 < 3 ∧
      LG (l[s].2 * nSK + l[s].1) = i + s
  | [], _, _ => fun s hs => absurd hs (Nat.not_lt_zero _)
  | o :: l, i, h => by
    change andB (orB (Nat.beq i 0) (andB (Nat.blt o.1 i) (andB (Nat.blt o.2 3)
      (Nat.beq (LG (Nat.add (Nat.mul o.2 nSK) o.1)) i)))) (strictB (Nat.succ i) (parK LG l)) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    rw [strictB_eq'] at h2
    intro s hs hne
    cases s with
    | zero =>
      have hi : Nat.beq i 0 = false := by
        rw [Bool.eq_false_iff]
        intro e
        exact hne (by simpa using Nat.eq_of_beq_eq_true e)
      rw [hi] at h1
      change andB (Nat.blt o.1 i) (andB (Nat.blt o.2 3)
        (Nat.beq (LG (Nat.add (Nat.mul o.2 nSK) o.1)) i)) = true at h1
      obtain ⟨h3, h4⟩ := andB_true h1
      obtain ⟨h5, h6⟩ := andB_true h4
      exact ⟨Eq.mp Nat.blt_eq h3, Eq.mp Nat.blt_eq h5, Nat.eq_of_beq_eq_true h6⟩
    | succ s =>
      have e : i + (s + 1) = Nat.succ i + s := by omega
      have := parK_sound h2 s (by simpa using hs) (by omega)
      rw [List.getElem_cons_succ, e]
      exact this

theorem leftK_sound {R E LG : Nat → Nat} : ∀ {l : List Nat} {t : Nat}, leftK R E LG l t = true →
    ∀ s (hs : s < l.length), l[s] < nSK ∧ l[s] = LG (t + s) ∧
      U (mulWK (GK R ((t + s) / nSK)) (E ((t + s) % nSK))) = U (E l[s])
  | [], _, _ => fun s hs => absurd hs (Nat.not_lt_zero _)
  | v :: l, t, h => by
    change andB (Nat.blt v nSK) (andB (Nat.beq v (LG t))
      (andB (eqK (mulWK (GK R (Nat.div t nSK)) (E (Nat.mod t nSK))) (E v))
      (strictB (Nat.succ t) (leftK R E LG l)))) = true at h
    obtain ⟨h1, h⟩ := andB_true h
    obtain ⟨h0, h⟩ := andB_true h
    obtain ⟨h2, h3⟩ := andB_true h
    rw [strictB_eq'] at h3
    intro s hs
    cases s with
    | zero => exact ⟨Eq.mp Nat.blt_eq h1, Nat.eq_of_beq_eq_true h0, beq_of_eqK h2⟩
    | succ s =>
      have e : t + (s + 1) = Nat.succ t + s := by omega
      have := leftK_sound h3 s (by simpa using hs)
      rw [List.getElem_cons_succ, e]
      exact this

theorem mulU (A B : Nat) : mul (U A) (U B) = U (mulWK A B) := mul_unpackW A B

theorem opsF : (pairsL opsN).length = 1153 ∧ opsK RG (pairsL opsN) 0 = true := by
  have h := kOps
  rw [← scans131.1.2] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem parF : (pairsL parN).length = 19683 ∧ parK LG131 (pairsL parN) 0 = true := by
  have h := kPar
  rw [← scans131.2.1.2] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem leftF : LN.length = 59049 ∧ leftK RG EG LG131 LN 0 = true := by
  have h := kLeft
  rw [← scans131.2.2.2] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem par131S (s : Nat) (hs : s < (pairsL parN).length) (h0 : s ≠ 0) :
    (pairsL parN)[s].1 < s ∧ (pairsL parN)[s].2 < 3 ∧
      U (EG s) = U (mulWK (GK RG (pairsL parN)[s].2) (EG (pairsL parN)[s].1)) := by
  obtain ⟨h1, h2, h3⟩ := parK_sound parF.2 s hs (by omega)
  simp only [Nat.zero_add] at h1 h3
  refine ⟨h1, h2, ?_⟩
  have hn : nSK = 19683 := rfl
  have hl := parF.1
  have ht : (pairsL parN)[s].2 * nSK + (pairsL parN)[s].1 < LN.length := by
    rw [leftF.1, hn]
    have hle : ((pairsL parN)[s].2 + 1) * 19683 ≤ 3 * 19683 := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at hle
    omega
  obtain ⟨-, hL, hE⟩ := leftK_sound leftF.2 _ ht
  simp only [Nat.zero_add] at hL hE
  have hd : ((pairsL parN)[s].2 * nSK + (pairsL parN)[s].1) / nSK = (pairsL parN)[s].2 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hm : ((pairsL parN)[s].2 * nSK + (pairsL parN)[s].1) % nSK = (pairsL parN)[s].1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [hd, hm, hL, h3] at hE
  exact hE.symm

theorem invF : U (mulWK (RG 1) (RG 2)) = U oneK ∧ U (RG 2) = U (mulWK (RG 1) (RG 1)) := by
  have h := kInv
  simp only [Bool.and_eq_true] at h
  exact ⟨beq_of_eqK h.1, beq_of_eqK h.2⟩

theorem aRows_eq : aRows () = U (RG 0) := by
  have h : aRows () = aR := rfl
  rw [h, CertificateChecks.KernelSporSch.Co1Packed.aR_u, CFSG.KC.Co1T.unpack_eq_unpackR]
  rfl

theorem bRows_eq : bRows () = U (RG 1) := by
  have h : bRows () = bR := rfl
  rw [h, CertificateChecks.KernelSporSch.Co1Packed.bR_u, CFSG.KC.Co1T.unpack_eq_unpackR]
  rfl

theorem biRows_eq : biRows () = U (RG 2) := by
  have h : biRows () = mul (bRows ()) (bRows ()) := rfl
  rw [h, bRows_eq, mulU, invF.2]

theorem toArray_map_push (f : Nat → Array Nat) (n : Nat) :
    (((List.range n).map f).toArray).push (f n) = ((List.range (n + 1)).map f).toArray := by
  rw [List.range_succ, List.map_append, List.push_toArray]
  rfl

theorem get!_map_range (f : Nat → Array Nat) {n i : Nat} (hi : i < n) :
    (((List.range n).map f).toArray)[i]! = f i := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

theorem regs_build : ∀ n ≤ 1153, buildN #[aRows (), bRows (), biRows ()]
    (fun acc k => mul acc[((ops ())[k - 3]!).1]! acc[((ops ())[k - 3]!).2]!) n =
      ((List.range (n + 3)).map fun k => U (RG k)).toArray
  | 0, _ => by
    rw [buildN, aRows_eq, bRows_eq, biRows_eq]
    rfl
  | n + 1, hn => by
    rw [buildN]
    rw [regs_build n (by omega)]
    have hsz : (((List.range (n + 3)).map fun k => U (RG k)).toArray).size = n + 3 := by simp
    rw [hsz, Nat.add_sub_cancel, ops_eq]
    have hl := opsF.1
    have hn' : n < (pairsL opsN).length := by omega
    rw [getElem!_pos (pairsL opsN).toArray n (by simpa using hn'), List.getElem_toArray]
    obtain ⟨h1, h2, h3⟩ := opsK_sound opsF.2 n hn'
    simp only [Nat.zero_add] at h1 h2 h3
    rw [get!_map_range _ h1, get!_map_range _ h2, mulU, ← h3]
    exact toArray_map_push (fun k => U (RG k)) (n + 3)

theorem regsM_eq : regsM () = ((List.range 1156).map fun k => U (RG k)).toArray := by
  have h : regsM () = buildN #[aRows (), bRows (), biRows ()]
      (fun acc k => mul acc[((ops ())[k - 3]!).1]! acc[((ops ())[k - 3]!).2]!) (ops ()).size := rfl
  have hs : (ops ()).size = 1153 := by rw [ops_eq, List.size_toArray, opsF.1]
  rw [h, hs, regs_build 1153 le_rfl]

theorem genM_eq {j : Nat} (hj : j < 3) : genM j = U (GK RG j) := by
  have h : genM j = (regsM ())[gens[j]!]! := rfl
  rw [h, regsM_eq]
  interval_cases j
  · exact get!_map_range _ (by decide)
  · exact get!_map_range _ (by decide)
  · exact get!_map_range _ (by decide)

theorem one_eq' : one = U oneK := one_eq

theorem elts_build : ∀ n ≤ nS - 1, buildN #[one]
    (fun acc i => mul (genM ((par ())[i]!).2) (acc[((par ())[i]!).1]!)) n =
      ((List.range (n + 1)).map fun k => U (EG k)).toArray
  | 0, _ => by
    rw [buildN, one_eq', ← beq_of_eqK kE0]
    rfl
  | n + 1, hn => by
    rw [buildN]
    rw [elts_build n (by omega)]
    have hsz : (((List.range (n + 1)).map fun k => U (EG k)).toArray).size = n + 1 := by simp
    rw [hsz, par_eq]
    have hl := parF.1
    have hn' : n + 1 < (pairsL parN).length := by
      rw [hl]
      have : nS = 19683 := rfl
      omega
    rw [getElem!_pos (pairsL parN).toArray (n + 1) (by simpa using hn'), List.getElem_toArray]
    obtain ⟨h1, h2, h3⟩ := par131S (n + 1) hn' (by omega)
    rw [genM_eq h2, get!_map_range _ h1, mulU, ← h3]
    exact toArray_map_push (fun k => U (EG k)) (n + 1)

theorem eltsM_eq : eltsM () = ((List.range nS).map fun k => U (EG k)).toArray := by
  have h : eltsM () = buildN #[one]
      (fun acc i => mul (genM ((par ())[i]!).2) (acc[((par ())[i]!).1]!)) (nS - 1) := rfl
  rw [h, elts_build (nS - 1) le_rfl]
  rfl

theorem E_get {i : Nat} (hi : i < nS) : (eltsM ())[i]! = U (EG i) := by
  rw [eltsM_eq]
  exact get!_map_range _ hi

set_option exponentiation.threshold 1024 in
theorem sortF : (∀ t < nS - 1, EG (SG t) < EG (SG (t + 1))) ∧ (∀ t < nS, SG t < nS) ∧
    (∀ i < nS, EG i < 2 ^ 576) := by
  have h := kSort
  unfold sortK at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h3⟩ := andB_true h
  refine ⟨fun t ht => Eq.mp Nat.blt_eq (allN_true' h1 t ht), fun t ht => Eq.mp Nat.blt_eq
    (allN_true' h2 t ht), fun i hi => ?_⟩
  have := Eq.mp Nat.blt_eq (allN_true' h3 i hi)
  have e : Nat.shiftLeft 1 576 = 2 ^ 576 := by
    change 1 <<< 576 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.lt_of_lt_of_eq this e

theorem sort_mono {t₁ t₂ : Nat} (h : t₁ < t₂) (h2 : t₂ < nS) : EG (SG t₁) < EG (SG t₂) := by
  induction t₂ with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ t ih =>
    have hs := sortF.1 t (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · exact Nat.lt_trans (ih h' (by omega)) hs
    · exact hs

theorem SG_surj {i : Nat} (hi : i < nS) : ∃ t < nS, SG t = i := by
  let f : Fin nS → Fin nS := fun t => ⟨SG t, sortF.2.1 t t.isLt⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : SG a = SG b := congrArg Fin.val hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact absurd (congrArg EG e) (Nat.ne_of_lt (sort_mono h b.isLt))
    · exact absurd (congrArg EG e) (Nat.ne_of_gt (sort_mono h a.isLt))
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 hf) ⟨i, hi⟩
  exact ⟨t, t.isLt, congrArg Fin.val ht⟩

theorem EG_inj {i k : Nat} (hi : i < nS) (hk : k < nS) (h : EG i = EG k) : i = k := by
  obtain ⟨t, ht, rfl⟩ := SG_surj hi
  obtain ⟨t', ht', rfl⟩ := SG_surj hk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (fun e : t = t' => hne (e ▸ rfl)) with h' | h'
  · exact Nat.ne_of_lt (sort_mono h' ht') h
  · exact Nat.ne_of_gt (sort_mono h' ht) h

set_option exponentiation.threshold 1024 in
theorem U_inj {i k : Nat} (hi : i < nS) (hk : k < nS) (h : U (EG i) = U (EG k)) : i = k := by
  have e := beq_unpack (EG i) (EG k)
  rw [h, beq_self_eq_true] at e
  change true = Nat.beq (EG i % Nat.shiftLeft 1 576) (EG k % Nat.shiftLeft 1 576) at e
  have e2 := Nat.eq_of_beq_eq_true e.symm
  have s : Nat.shiftLeft 1 576 = 2 ^ 576 := by
    change 1 <<< 576 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [s, Nat.mod_eq_of_lt (sortF.2.2 i hi), Nat.mod_eq_of_lt (sortF.2.2 k hk)] at e2
  exact EG_inj hi hk e2

theorem mul_assoc' (X Y Z : Array Nat) : mul (mul X Y) Z = mul X (mul Y Z) := by
  change mulRows 24 (mulRows 24 X Y) Z = mulRows 24 X (mulRows 24 Y Z)
  unfold mulRows
  rw [Array.map_map]
  congr 1
  funext a
  exact vm_assoc Y Z a

theorem one_mul' (P : Nat) : mul one (U P) = U P := by
  change mulRows 24 (idRows 24) (U P) = U P
  unfold mulRows idRows
  rw [Array.map_ofFn]
  apply Array.ext
  · simp [unpackR]
  · intro i h1 h2
    simp only [Array.getElem_ofFn, Function.comp_apply]
    have hi : i < 24 := by simpa using h1
    rw [vm_one hi]
    simp [rw', unpackR, hi]

theorem par_get {a : Nat} (ha : a < nS) : (par ())[a]! = (pairsL parN)[a]'(by rw [parF.1]; exact ha) := by
  rw [par_eq, getElem!_pos (pairsL parN).toArray a (by rw [List.size_toArray, parF.1]; exact ha),
    List.getElem_toArray]

theorem tabMul_spec : ∀ a < nS, ∀ b < nS, tabMul (par ()) (L ()) a b < nS ∧
    U (EG (tabMul (par ()) (L ()) a b)) = mul (U (EG a)) (U (EG b)) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha b hb
    rw [tabMul]
    by_cases h0 : a = 0
    · subst h0
      rw [dite_eq_right (Nat.not_lt_zero _), beq_of_eqK kE0, ← one_eq', one_mul']
      exact ⟨hb, rfl⟩
    · have hpa : a < (pairsL parN).length := by rw [parF.1]; exact ha
      obtain ⟨h1, h2, h3⟩ := par131S a hpa h0
      rw [par_get ha, dite_eq_left h1]
      obtain ⟨hc, hcE⟩ := ih _ h1 (by omega) b hb
      set c := tabMul (par ()) (L ()) (pairsL parN)[a].1 b
      have hj := h2
      rw [L_get hj hc]
      have hs : (pairsL parN)[a].2 * nS + c < LN.length := by
        rw [leftF.1]
        have hle : ((pairsL parN)[a].2 + 1) * nS ≤ 3 * nS := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul] at hle
        have : nS = 19683 := rfl
        omega
      rw [List.getD_eq_getElem _ _ hs]
      obtain ⟨hv, -, hvE⟩ := leftK_sound leftF.2 _ hs
      simp only [Nat.zero_add] at hvE
      have hd : ((pairsL parN)[a].2 * nS + c) / nSK = (pairsL parN)[a].2 := by
        have : nSK = nS := rfl
        rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hc, Nat.zero_add]
      have hm : ((pairsL parN)[a].2 * nS + c) % nSK = c := by
        have : nSK = nS := rfl
        rw [this, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
      rw [hd, hm] at hvE
      refine ⟨hv, ?_⟩
      rw [← hvE, ← mulU, hcE, ← mul_assoc', mulU, ← h3]

theorem comm_iff {a b : Nat} (ha : a < nS) (hb : b < nS) :
    (tabMul (par ()) (L ()) a b == tabMul (par ()) (L ()) b a) =
      eqK (mulWK (EG a) (EG b)) (mulWK (EG b) (EG a)) := by
  obtain ⟨h1, e1⟩ := tabMul_spec a ha b hb
  obtain ⟨h2, e2⟩ := tabMul_spec b hb a ha
  rw [← beq_unpack, ← mulU, ← mulU, ← e1, ← e2]
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => h ▸ rfl, fun h => U_inj h1 h2 h⟩

theorem cube_iff {a : Nat} (ha : a < nS) :
    (tabMul (par ()) (L ()) a (tabMul (par ()) (L ()) a a) != 0) = !cubeK EG a := by
  obtain ⟨h1, e1⟩ := tabMul_spec a ha a ha
  obtain ⟨h2, e2⟩ := tabMul_spec a ha _ h1
  have hc : cubeK EG a = eqK (mulWK (EG a) (mulWK (EG a) (EG a))) oneK := by
    unfold cubeK
    rw [strictB_eq']
  rw [hc, ← beq_unpack, ← mulU, ← mulU, ← e1, ← e2, ← beq_of_eqK kE0]
  apply Bool.eq_iff_iff.2
  simp only [bne_iff_ne, ne_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
  exact ⟨fun h e => h (U_inj h2 (by decide) e), fun h e => h (e ▸ rfl)⟩

theorem wit_count {a : Nat} (ha : a < nS) (h : witK EG WG a = true) :
    81 ≤ tabComm (par ()) (L ()) nS a := by
  unfold witK at h
  have hk : ∀ k < 81, witAt WG a k < nS ∧ (k ≠ 0 → witAt WG a (k - 1) < witAt WG a k) ∧
      eqK (mulWK (EG a) (EG (witAt WG a k))) (mulWK (EG (witAt WG a k)) (EG a)) = true := by
    intro k hk
    have h' := allN_true' h k hk
    rw [strictB_eq'] at h'
    obtain ⟨h1, h⟩ := andB_true h'
    obtain ⟨h2, h3⟩ := andB_true h
    refine ⟨Eq.mp Nat.blt_eq h1, fun hk0 => ?_, h3⟩
    have hb : Nat.beq k 0 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact hk0 (Nat.eq_of_beq_eq_true e)
    rw [hb] at h2
    exact Eq.mp Nat.blt_eq h2
  have mono : ∀ k₁ k₂, k₁ < k₂ → k₂ < 81 → witAt WG a k₁ < witAt WG a k₂ := by
    intro k₁ k₂ h12 h2
    induction k₂ with
    | zero => exact absurd h12 (Nat.not_lt_zero _)
    | succ k ih =>
      have hs := (hk (k + 1) h2).2.1 (by omega)
      rw [Nat.add_sub_cancel] at hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 h12 with h' | rfl
      · exact Nat.lt_trans (ih h' (by omega)) hs
      · exact hs
  let ws := (List.range 81).map (witAt WG a)
  have hnd : ws.Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range
    have hx' := List.mem_range.1 hx
    have hy' := List.mem_range.1 hy
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact Nat.ne_of_lt (mono x y h' hy') hxy
    · exact Nat.ne_of_gt (mono y x h' hx') hxy
  have hsub : ws ⊆ (List.range nS).filter
      (fun b => tabMul (par ()) (L ()) a b == tabMul (par ()) (L ()) b a) := by
    intro b hb
    obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hb
    have hk'' := List.mem_range.1 hk'
    obtain ⟨hlt, -, hc⟩ := hk k hk''
    refine List.mem_filter.2 ⟨List.mem_range.2 hlt, ?_⟩
    rw [comm_iff ha hlt]
    exact hc
  have hlen := (List.Nodup.subperm hnd hsub).length_le
  rw [tabComm, List.countP_eq_length_filter]
  simpa [ws] using hlen

theorem mul_one131 (P : Nat) : mul (U P) one = U P := by
  change mulRows 24 (U P) (idRows 24) = U P
  unfold mulRows
  apply Array.ext
  · simp
  · intro i h1 h2
    rw [Array.getElem_map]
    exact vm_id (by simp [unpackR, Nat.mod_lt])

theorem comm_conj131 {b c : Nat} (hb : b < nS) (h : cj131K EG c b = true)
    (ih : ∀ p < b, p ≠ 0 → cubeK EG p = true → 81 ≤ tabComm (par ()) (L ()) nS p) :
    81 ≤ tabComm (par ()) (L ()) nS b := by
  unfold cj131K at h
  rw [strictB_eq', strictB_eq', strictB_eq'] at h
  generalize Nat.land c 32767 = p at h
  generalize Nat.land (Nat.shiftRight c 15) 32767 = k at h
  generalize Nat.shiftRight c 30 = k' at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h⟩ := andB_true h
  obtain ⟨h4, h⟩ := andB_true h
  obtain ⟨h5, h⟩ := andB_true h
  obtain ⟨h6, h⟩ := andB_true h
  obtain ⟨h7, h8⟩ := andB_true h
  have hpb : p < b := Eq.mp Nat.blt_eq h1
  have hp0 : p ≠ 0 := by
    intro e
    rw [e] at h2
    exact absurd h2 (by decide)
  have hk : k < nS := Eq.mp Nat.blt_eq h3
  have hk' : k' < nS := Eq.mp Nat.blt_eq h4
  have hp : p < nS := by omega
  have e5 : mul (U (EG k)) (U (EG k')) = one := by rw [mulU, one_eq']; exact beq_of_eqK h5
  have e6 : mul (U (EG k')) (U (EG k)) = one := by rw [mulU, one_eq']; exact beq_of_eqK h6
  have e7 : mul (U (EG b)) (U (EG k)) = mul (U (EG k)) (U (EG p)) := by
    rw [mulU, mulU]
    exact beq_of_eqK h7
  have hB : U (EG b) = mul (mul (U (EG k)) (U (EG p))) (U (EG k')) := by
    rw [← e7, mul_assoc', e5, mul_one131]
  have canc : ∀ A B, mul (U (EG k')) (mul (U (EG k)) (mul (U A) (U B))) = mul (U A) (U B) := by
    intro A B
    rw [← mul_assoc', e6, mulU, one_mul']
  let φ := fun y => tabMul (par ()) (L ()) (tabMul (par ()) (L ()) k y) k'
  have hφ : ∀ y < nS, φ y < nS ∧ U (EG (φ y)) = mul (mul (U (EG k)) (U (EG y))) (U (EG k')) := by
    intro y hy
    obtain ⟨a1, b1⟩ := tabMul_spec k hk y hy
    obtain ⟨a2, b2⟩ := tabMul_spec _ a1 k' hk'
    exact ⟨a2, by rw [b2, b1]⟩
  have hinj : ∀ y < nS, ∀ z < nS, φ y = φ z → y = z := by
    intro y hy z hz e
    have e' := congrArg (fun X => mul (mul (U (EG k')) X) (U (EG k))) (congrArg (fun i => U (EG i)) e)
    simp only [(hφ y hy).2, (hφ z hz).2, mul_assoc', e6, mul_one131] at e'
    rw [← mul_assoc', e6, one_mul', ← mul_assoc', e6, one_mul'] at e'
    exact U_inj hy hz e'
  let Sp := (List.range nS).filter (fun y => tabMul (par ()) (L ()) p y == tabMul (par ()) (L ()) y p)
  let Sb := (List.range nS).filter (fun y => tabMul (par ()) (L ()) b y == tabMul (par ()) (L ()) y b)
  have hnd : (Sp.map φ).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (List.nodup_range.filter _)
    exact hinj x (List.mem_range.1 (List.mem_filter.1 hx).1) y (List.mem_range.1 (List.mem_filter.1 hy).1) hxy
  have hsub : Sp.map φ ⊆ Sb := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hy
    have hyS := List.mem_range.1 hy1
    rw [comm_iff hp hyS] at hy2
    have hc : mul (U (EG p)) (U (EG y)) = mul (U (EG y)) (U (EG p)) := by
      rw [mulU, mulU]
      exact beq_of_eqK hy2
    refine List.mem_filter.2 ⟨List.mem_range.2 (hφ y hyS).1, ?_⟩
    rw [comm_iff hb (hφ y hyS).1, ← beq_unpack, ← mulU, ← mulU, (hφ y hyS).2, hB, beq_iff_eq]
    simp only [mul_assoc']
    rw [canc, canc, ← mul_assoc' (U (EG p)) (U (EG y)), hc]
    simp only [mul_assoc']
  have hlen := (List.Nodup.subperm hnd hsub).length_le
  have hcp := ih p hpb hp0 h8
  rw [tabComm, List.countP_eq_length_filter] at hcp ⊢
  rw [List.length_map] at hlen
  exact Nat.le_trans hcp hlen

theorem wf_unpack (P : Nat) : wf (U P) = true := by
  unfold wf
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by simp [unpackR], fun i hi => ?_⟩
  simp [unpackR, Nat.mod_lt]

theorem kill_cl : ∀ a < nS, orB (Nat.beq a 0) (orB (notB (cubeK EG a))
    (Bool.rec (motive := fun _ => Bool) (cj131K EG (CJG a) a) (witK EG WG a) (Nat.beq (CJG a) 0))) = true := by
  intro a ha
  have hb : ∀ lo n, kill131K EG WG CJG lo n = true → lo ≤ a → a < lo + n →
      orB (Nat.beq a 0) (orB (notB (cubeK EG a))
        (Bool.rec (motive := fun _ => Bool) (cj131K EG (CJG a) a) (witK EG WG a)
          (Nat.beq (CJG a) 0))) = true := by
    intro lo n h h1 h2
    have := allN_true' h (a - lo) (by omega)
    have e : Nat.add lo (a - lo) = a := Nat.add_sub_cancel' h1
    rw [strictB_eq', e] at this
    exact this
  have hK : ∀ c < 20, kill131K EG WG CJG (1024 * c) (if c = 19 then 227 else 1024) = true := by
    intro c hc
    interval_cases c
    exacts [kK0, kK1, kK2, kK3, kK4, kK5, kK6, kK7, kK8, kK9, kK10, kK11, kK12, kK13, kK14,
      kK15, kK16, kK17, kK18, kK19]
  have hn : nS = 19683 := rfl
  have hc : a / 1024 < 20 := by omega
  refine hb _ _ (hK _ hc) (Nat.mul_div_le a 1024) ?_
  by_cases h19 : a / 1024 = 19
  · rw [ite_eq_left h19]
    omega
  · rw [ite_eq_right h19]
    omega

theorem kill_all : ∀ a < nS, a ≠ 0 → cubeK EG a = true → 81 ≤ tabComm (par ()) (L ()) nS a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha h0 hcb
    have h := kill_cl a ha
    have hb : Nat.beq a 0 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact h0 (Nat.eq_of_beq_eq_true e)
    rw [hb, hcb] at h
    change Bool.rec (motive := fun _ => Bool) (cj131K EG (CJG a) a) (witK EG WG a)
      (Nat.beq (CJG a) 0) = true at h
    cases hc : Nat.beq (CJG a) 0
    · rw [hc] at h
      exact comm_conj131 ha h fun p hp hp0 hpc => ih p hp (by omega) hp0 hpc
    · rw [hc] at h
      exact wit_count ha h

open Certificates in
theorem c131301 : CFSG.Sporadic.Co1.S0.co1S0Check () = true := by
  have hn : nS = 19683 := rfl
  have hinv : invOK () = true := by
    unfold invOK
    rw [bRows_eq, biRows_eq, mulU, invF.1, one_eq']
    exact beq_self_eq_true _
  have hshape : shapeOK () = true := by
    unfold shapeOK
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨⟨⟨by rw [ops_eq, List.size_toArray, opsF.1], rfl⟩, by rw [par_eq, List.size_toArray, parF.1]; rfl⟩,
      by rw [L_eq]; rfl⟩, ?_⟩, ?_⟩, ?_⟩
    · intro t ht
      have ht' : t < (pairsL opsN).length := by
        rw [ops_eq, List.size_toArray] at ht
        exact ht
      rw [ops_eq, getElem!_pos (pairsL opsN).toArray t (by simpa using ht'), List.getElem_toArray]
      obtain ⟨h1, h2, -⟩ := opsK_sound opsF.2 t ht'
      simp only [Nat.zero_add] at h1 h2
      simp [h1, h2]
    · intro j hj
      have hs : (ops ()).size = 1153 := by rw [ops_eq, List.size_toArray, opsF.1]
      rw [hs]
      have : j < 3 := hj
      interval_cases j <;> decide
    · intro i hi
      by_cases h0 : i = 0
      · simp [h0]
      · have hi' : i < (pairsL parN).length := by rw [parF.1]; exact hi
        obtain ⟨h1, h2, -⟩ := par131S i hi' h0
        rw [par_get hi]
        simp [h1, h2]
  have hkill : killOK () = true := by
    unfold killOK
    rw [List.all_eq_true]
    intro a ha
    have ha' := List.mem_range.1 ha
    rw [cube_iff ha']
    by_cases h0 : a = 0
    · simp [h0]
    · cases hcb : cubeK EG a
      · simp
      · simp [kill_all a ha' h0 hcb]
  have hcanon : canonOK () = true := by
    unfold canonOK
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
    refine ⟨by rw [eltsM_eq]; simp, fun i hi => ?_⟩
    rw [E_get hi, wf_unpack]
  have hleft : leftOK () = true := by
    unfold leftOK
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    intro j hj i hi
    rw [L_get hj hi]
    have hs : j * nS + i < LN.length := by
      rw [leftF.1]
      have hle : (j + 1) * nS ≤ 3 * nS := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at hle
      omega
    rw [List.getD_eq_getElem _ _ hs]
    obtain ⟨hv, -, hvE⟩ := leftK_sound leftF.2 _ hs
    simp only [Nat.zero_add] at hvE
    have hd : (j * nS + i) / nSK = j := by
      have : nSK = nS := rfl
      rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hi, Nat.zero_add]
    have hm : (j * nS + i) % nSK = i := by
      have : nSK = nS := rfl
      rw [this, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    rw [hd, hm] at hvE
    refine ⟨hv, ?_⟩
    rw [genM_eq hj, E_get hi, E_get hv, mulU, hvE]
    exact beq_self_eq_true _
  have hdist : distinctOK () = true := by
    unfold distinctOK
    simp only [List.all_eq_true, List.mem_range]
    intro i hi k hk
    rw [E_get hi, E_get (by omega), bne_iff_ne, ne_eq]
    intro e
    exact absurd (U_inj hi (by omega) e) (by omega)
  rw [co1S0Check, hinv, hshape, hkill, hcanon, hleft, hdist]
  rfl

end CertificateChecks.KernelCo1B.S0131301

end
