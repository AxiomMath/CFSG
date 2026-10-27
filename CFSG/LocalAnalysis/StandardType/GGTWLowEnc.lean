module

public import Certificates.Data.TwoDepSmallLow
public import CFSG.LocalAnalysis.StandardType.GGTWNatSolve
public import CFSG.LocalAnalysis.StandardType.GGTWNatWord

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nLN_cast_neg_mod {p k : ℕ} (hp : 3 ≤ p) (hk : k < p) :
    (((p - k % p) % p : ℕ) : ZMod p) = -((k : ℕ) : ZMod p) := by
  rw [Nat.mod_eq_of_lt hk]
  exact l05nND_cast_neg p k (le_of_lt hk)

private lemma l05nLN_nat_eq_of_cast {p : ℕ} {x y : ℕ} (hx : x < p) (hy : y < p)
    (h : (x : ZMod p) = (y : ZMod p)) : x = y := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hv

private lemma l05nLN_dot_cast {p N : ℕ} [Fact p.Prime] {a b : List ℕ}
    (ha : a.length = N - 1) (hb : b.length = N - 1) :
    ((ggDepANDot p a b : ℕ) : ZMod p) =
      ggTWdot (ggTWNToZ p N a) (ggTWNToZ p N b) := by
  have h := ggDepANDot_cast (p := p) (N := N - 1) a b ha hb
  simpa only [ggTWNToZ, ggTWdot] using h

theorem ggTWLEnc1 {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N) (pos : GGTWPos)
    (c0 : Fin (N - 1)) (mi ni : ℕ) (hmi : mi = 1 ∨ mi = 2) (hni : ni = 1 ∨ ni = 2)
    (ha αa : GGTWE p N)
    (hpair : GGTWPairs1 p N pos c0 (-(mi : ℤ)) (-(ni : ℤ)) ha αa)
    (hdot : ggTWdot αa ha = 2) (hx : ggTWdot αa (ggTWx p N) ≠ 0) :
    ∃ lh la : List ℕ,
      lh ∈ ggTWNSolH p N (ggTWPosNat pos) (fun c => if c = c0.val then (p - ni % p) % p else 0) ∧
      la ∈ ggTWNSolA p N (ggTWPosNat pos) (fun c => if c = c0.val then (p - mi % p) % p else 0) ∧
      ggDepANDot p la lh = 2 % p ∧ ggDepANDot p la (ggTWNX N) ≠ 0 ∧
      GGTWNValid p N (lh, la) ∧ ggTWNNews p N [(lh, la)] = {(ha, αa)} := by
  have hni_lt : ni < p := by rcases hni with rfl | rfl <;> omega
  have hmi_lt : mi < p := by rcases hmi with rfl | rfl <;> omega
  have hvH : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggTWdot (ggTWα p N c) ha =
        (((if c.val = c0.val then (p - ni % p) % p else 0 : ℕ)) : ZMod p) := by
    intro c hcJ
    have h2 := (hpair c hcJ).2
    by_cases hcc : c = c0
    · subst hcc
      rw [if_pos rfl] at h2
      rw [if_pos rfl]
      rw [h2, l05nLN_cast_neg_mod hp hni_lt]
      simp only [Int.cast_neg, Int.cast_natCast]
    · rw [if_neg hcc] at h2
      have hne : c.val ≠ c0.val := fun hh => hcc (Fin.ext hh)
      rw [if_neg hne]
      rw [h2]
      simp
  have hvA : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggTWdot αa (ggTWh p N c) =
        (((if c.val = c0.val then (p - mi % p) % p else 0 : ℕ)) : ZMod p) := by
    intro c hcJ
    have h2 := (hpair c hcJ).1
    by_cases hcc : c = c0
    · subst hcc
      rw [if_pos rfl] at h2
      rw [if_pos rfl]
      rw [h2, l05nLN_cast_neg_mod hp hmi_lt]
      simp only [Int.cast_neg, Int.cast_natCast]
    · rw [if_neg hcc] at h2
      have hne : c.val ≠ c0.val := fun hh => hcc (Fin.ext hh)
      rw [if_neg hne]
      rw [h2]
      simp
  obtain ⟨lh, hlh_mem, hlh_eq, hlh_len⟩ :=
    ggTWNSolH_complete (p := p) (N := N) pos
      (fun x => if x = c0.val then (p - ni % p) % p else 0) ha hvH
  obtain ⟨la, hla_mem, hla_eq, hla_len⟩ :=
    ggTWNSolA_complete (p := p) (N := N) pos
      (fun x => if x = c0.val then (p - mi % p) % p else 0) αa hvA
  have hd : ggDepANDot p la lh = 2 % p := by
    refine l05nLN_nat_eq_of_cast (p := p) (x := ggDepANDot p la lh) (y := 2 % p) ?_ ?_ ?_
    · simp only [ggDepANDot]; exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · rw [l05nLN_dot_cast (p := p) (N := N) (a := la) (b := lh) hla_len hlh_len,
        hla_eq, hlh_eq]
      rw [Nat.mod_eq_of_lt (by omega : 2 < p)]
      exact hdot
  have hz : ggDepANDot p la (ggTWNX N) ≠ 0 := by
    intro h0
    apply hx
    have hcast := l05nLN_dot_cast (p := p) (N := N) (a := la) (b := ggTWNX N) hla_len
      (ggTWNX_length N)
    rw [h0, Nat.cast_zero, hla_eq, ggTWNX_toZ] at hcast
    exact hcast.symm
  have hnews_eq : ggTWNNews p N [(lh, la)] = {(ha, αa)} := by
    ext t
    constructor
    · rintro ⟨q, hq, ht⟩
      rw [List.mem_singleton] at hq
      subst hq
      rw [ht]
      simp [hlh_eq, hla_eq]
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact ⟨(lh, la), by simp, by simp [hlh_eq, hla_eq]⟩
  exact ⟨lh, la, hlh_mem, hla_mem, hd, hz, ⟨hlh_len, hla_len, hd⟩, hnews_eq⟩

private lemma l05nLN_cast_neg_one {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) :
    ((p - 1 : ℕ) : ZMod p) = (-1 : ZMod p) := by
  have hlt : p - 1 < p := by omega
  have h := l05nND_cast_neg p 1 (by omega : 1 ≤ p)
  rw [Nat.mod_eq_of_lt hlt] at h
  simpa using h

private lemma l05nLN_form_apply {p N : ℕ} (f v : GGTWE p N) : ggTWform f v = ggTWdot f v := by
  simp [ggTWform, ggTWdot, ggDepAform, ggDepAdot]

private lemma l05nLN_dot_add {p N : ℕ} (a v w : GGTWE p N) :
    ggTWdot a (v + w) = ggTWdot a v + ggTWdot a w := by
  rw [← l05nLN_form_apply a (v + w), map_add, l05nLN_form_apply a v, l05nLN_form_apply a w]

private lemma l05nLN_dot_smul {p N : ℕ} (a : GGTWE p N) (k : ZMod p) (v : GGTWE p N) :
    ggTWdot a (k • v) = k * ggTWdot a v := by
  rw [← l05nLN_form_apply a (k • v), map_smul, l05nLN_form_apply a v]
  simp

private lemma l05nLN_h1s_cast {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) {N : ℕ}
    (c c0 : Fin (N - 1)) :
    (((fun x : ℕ => if x = c0.val then (p - 1) % p else 0) c.val : ℕ) : ZMod p) =
      (if c = c0 then (-1 : ZMod p) else 0) := by
  by_cases h : c = c0
  · subst h
    simp [l05nLN_cast_neg_one hp]
  · have hne : c.val ≠ c0.val := fun hh => h (Fin.ext hh)
    rw [if_neg h]
    simp [hne]

private lemma l05nLN_tgt2_eq {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) {N : ℕ}
    (c₂ : Option (Fin (N - 1))) (c' : Fin (N - 1)) :
    ((ggTWNTgt2 p (c₂.map Fin.val) c'.val : ℕ) : ZMod p) =
      (if some c' = c₂ then (-1 : ZMod p) else 0) := by
  cases c₂ with
  | none => simp [ggTWNTgt2]
  | some c0 =>
      by_cases h : c' = c0
      · subst h
        simp [ggTWNTgt2, l05nLN_cast_neg_one hp]
      · have hne : c'.val ≠ c0.val := fun hh => h (Fin.ext hh)
        have hcond : ¬ (some c' = (some c0 : Option (Fin (N - 1)))) :=
          fun hh => h (Option.some.inj hh)
        simp only [Option.map_some, ggTWNTgt2]
        rw [if_neg hne, if_neg hcond]
        simp

private lemma l05nLN_nb_eq {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (c₂ : Option (Fin (N - 1))) :
    ((match c₂.map Fin.val with | none => (p - 1) % p | some _ => 0 : ℕ) : ZMod p) =
      (if c₂ = none then (-1 : ZMod p) else 0) := by
  cases c₂ with
  | none => simp [l05nLN_cast_neg_one hp]
  | some c => simp

private lemma l05nLN_nb_lt {p : ℕ} [Fact p.Prime] (c2 : Option ℕ) :
    (match c2 with | none => (p - 1) % p | some _ => 0) < p := by
  cases c2 with
  | none => exact Nat.mod_lt _ (Fact.out : p.Prime).pos
  | some c => exact Nat.pos_of_ne_zero (Fact.out : p.Prime).ne_zero

private lemma l05nLN_det_of_kernel {p : ℕ} [Fact p.Prime]
    (a1x a1z a2x a2z lam mu : ZMod p) (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (h1 : lam * a1x + mu * a1z = 0) (h2 : lam * a2x + mu * a2z = 0) :
    a1x * a2z = a1z * a2x := by
  have hD1 : lam * (a1x * a2z - a1z * a2x) = 0 := by
    have h : a2z * (lam * a1x + mu * a1z) - a1z * (lam * a2x + mu * a2z) = 0 := by
      rw [h1, h2, mul_zero, mul_zero, sub_zero]
    have heq : lam * (a1x * a2z - a1z * a2x) =
        a2z * (lam * a1x + mu * a1z) - a1z * (lam * a2x + mu * a2z) := by
      ring
    rw [heq, h]
  have hD2 : mu * (a1x * a2z - a1z * a2x) = 0 := by
    have h : a1x * (lam * a2x + mu * a2z) - a2x * (lam * a1x + mu * a1z) = 0 := by
      rw [h2, h1, mul_zero, mul_zero, sub_zero]
    have heq : mu * (a1x * a2z - a1z * a2x) =
        a1x * (lam * a2x + mu * a2z) - a2x * (lam * a1x + mu * a1z) := by
      ring
    rw [heq, h]
  have hD : a1x * a2z - a1z * a2x = 0 := by
    rcases hlm with hl | hm
    · exact (mul_eq_zero.mp hD1).resolve_left hl
    · exact (mul_eq_zero.mp hD2).resolve_left hm
  exact sub_eq_zero.mp hD

theorem ggTWLEnc2 {p N : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N) (pos : GGTWPos)
    (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1))) (ha1 αa1 ha2 αa2 : GGTWE p N)
    (hP : GGTWPairs2 p N pos c c₂ ha1 αa1 ha2 αa2)
    (hx : ggTWdot αa1 (ggTWx p N) ≠ 0 ∨ ggTWdot αa2 (ggTWx p N) ≠ 0) (lam mu : ZMod p)
    (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (h1 : ggTWdot αa1 (lam • ggTWx p N + mu • ggTWz p N pos) = 0)
    (h2 : ggTWdot αa2 (lam • ggTWx p N + mu • ggTWz p N pos) = 0) :
    ∃ lh1 la1 lh2 la2 : List ℕ,
      lh1 ∈ ggTWNSolH p N (ggTWPosNat pos) (fun c' => if c' = c.val then (p - 1) % p else 0) ∧
      la1 ∈ ggTWNSolA p N (ggTWPosNat pos) (fun c' => if c' = c.val then (p - 1) % p else 0) ∧
      lh2 ∈ ggTWNSolH p N (ggTWPosNat pos) (ggTWNTgt2 p (c₂.map Fin.val)) ∧
      la2 ∈ ggTWNSolA p N (ggTWPosNat pos) (ggTWNTgt2 p (c₂.map Fin.val)) ∧
      ggDepANDot p la1 lh1 = 2 % p ∧
      ggDepANDot p la1 lh2 = (match c₂.map Fin.val with | none => (p - 1) % p | some _ => 0) ∧
      ggDepANDot p la2 lh2 = 2 % p ∧
      ggDepANDot p la2 lh1 = (match c₂.map Fin.val with | none => (p - 1) % p | some _ => 0) ∧
      (ggDepANDot p la1 (ggTWNX N) ≠ 0 ∨ ggDepANDot p la2 (ggTWNX N) ≠ 0) ∧
      (ggDepANDot p la1 (ggTWNX N) * ggDepANDot p la2 (ggTWNZ p N (ggTWPosNat pos))) % p =
        (ggDepANDot p la1 (ggTWNZ p N (ggTWPosNat pos)) * ggDepANDot p la2 (ggTWNX N)) % p ∧
      GGTWNValid p N (lh1, la1) ∧ GGTWNValid p N (lh2, la2) ∧
      ggTWNNews p N [(lh1, la1), (lh2, la2)] = {(ha1, αa1), (ha2, αa2)} := by
  have hvH1 : ∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggTWdot (ggTWα p N c') ha1 =
        (((fun x => if x = c.val then (p - 1) % p else 0) c'.val : ℕ) : ZMod p) := by
    intro c' hcJ
    have hB := (hP.1 c' hcJ).2.1
    rw [hB, l05nLN_h1s_cast hp c' c]
  have hvA1 : ∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggTWdot αa1 (ggTWh p N c') =
        (((fun x => if x = c.val then (p - 1) % p else 0) c'.val : ℕ) : ZMod p) := by
    intro c' hcJ
    have hA := (hP.1 c' hcJ).1
    rw [hA, l05nLN_h1s_cast hp c' c]
  have hvH2 : ∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggTWdot (ggTWα p N c') ha2 =
        (((ggTWNTgt2 p (c₂.map Fin.val)) c'.val : ℕ) : ZMod p) := by
    intro c' hcJ
    have hD := (hP.1 c' hcJ).2.2.2
    rw [hD, l05nLN_tgt2_eq hp c₂ c']
  have hvA2 : ∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggTWdot αa2 (ggTWh p N c') =
        (((ggTWNTgt2 p (c₂.map Fin.val)) c'.val : ℕ) : ZMod p) := by
    intro c' hcJ
    have hC := (hP.1 c' hcJ).2.2.1
    rw [hC, l05nLN_tgt2_eq hp c₂ c']
  obtain ⟨lh1, hlh1_mem, hlh1_eq, hlh1_len⟩ :=
    ggTWNSolH_complete (p := p) (N := N) pos
      (fun x => if x = c.val then (p - 1) % p else 0) ha1 hvH1
  obtain ⟨la1, hla1_mem, hla1_eq, hla1_len⟩ :=
    ggTWNSolA_complete (p := p) (N := N) pos
      (fun x => if x = c.val then (p - 1) % p else 0) αa1 hvA1
  obtain ⟨lh2, hlh2_mem, hlh2_eq, hlh2_len⟩ :=
    ggTWNSolH_complete (p := p) (N := N) pos
      (ggTWNTgt2 p (c₂.map Fin.val)) ha2 hvH2
  obtain ⟨la2, hla2_mem, hla2_eq, hla2_len⟩ :=
    ggTWNSolA_complete (p := p) (N := N) pos
      (ggTWNTgt2 p (c₂.map Fin.val)) αa2 hvA2
  have hd1 : ggDepANDot p la1 lh1 = 2 % p := by
    refine l05nLN_nat_eq_of_cast (p := p) (x := ggDepANDot p la1 lh1) (y := 2 % p) ?_ ?_ ?_
    · simp only [ggDepANDot]; exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · rw [l05nLN_dot_cast (p := p) (N := N) (a := la1) (b := lh1) hla1_len hlh1_len,
        hla1_eq, hlh1_eq]
      rw [Nat.mod_eq_of_lt (by omega : 2 < p)]
      exact hP.2.2.2.1
  have hd3 : ggDepANDot p la2 lh2 = 2 % p := by
    refine l05nLN_nat_eq_of_cast (p := p) (x := ggDepANDot p la2 lh2) (y := 2 % p) ?_ ?_ ?_
    · simp only [ggDepANDot]; exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · rw [l05nLN_dot_cast (p := p) (N := N) (a := la2) (b := lh2) hla2_len hlh2_len,
        hla2_eq, hlh2_eq]
      rw [Nat.mod_eq_of_lt (by omega : 2 < p)]
      exact hP.2.2.2.2
  have hd2 : ggDepANDot p la1 lh2 =
      (match c₂.map Fin.val with | none => (p - 1) % p | some _ => 0) := by
    refine l05nLN_nat_eq_of_cast (p := p) (x := ggDepANDot p la1 lh2)
      (y := (match c₂.map Fin.val with | none => (p - 1) % p | some _ => 0)) ?_ ?_ ?_
    · simp only [ggDepANDot]; exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact l05nLN_nb_lt (c₂.map Fin.val)
    · rw [l05nLN_dot_cast (p := p) (N := N) (a := la1) (b := lh2) hla1_len hlh2_len,
        hla1_eq, hlh2_eq]
      rw [hP.2.1, l05nLN_nb_eq hp c₂]
  have hd4 : ggDepANDot p la2 lh1 =
      (match c₂.map Fin.val with | none => (p - 1) % p | some _ => 0) := by
    refine l05nLN_nat_eq_of_cast (p := p) (x := ggDepANDot p la2 lh1)
      (y := (match c₂.map Fin.val with | none => (p - 1) % p | some _ => 0)) ?_ ?_ ?_
    · simp only [ggDepANDot]; exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact l05nLN_nb_lt (c₂.map Fin.val)
    · rw [l05nLN_dot_cast (p := p) (N := N) (a := la2) (b := lh1) hla2_len hlh1_len,
        hla2_eq, hlh1_eq]
      rw [hP.2.2.1, l05nLN_nb_eq hp c₂]
  have hx_list : ggDepANDot p la1 (ggTWNX N) ≠ 0 ∨ ggDepANDot p la2 (ggTWNX N) ≠ 0 := by
    rcases hx with hx1 | hx2
    · left
      intro h0
      apply hx1
      have hcast := l05nLN_dot_cast (p := p) (N := N) (a := la1) (b := ggTWNX N) hla1_len
        (ggTWNX_length N)
      rw [h0, Nat.cast_zero, hla1_eq, ggTWNX_toZ] at hcast
      exact hcast.symm
    · right
      intro h0
      apply hx2
      have hcast := l05nLN_dot_cast (p := p) (N := N) (a := la2) (b := ggTWNX N) hla2_len
        (ggTWNX_length N)
      rw [h0, Nat.cast_zero, hla2_eq, ggTWNX_toZ] at hcast
      exact hcast.symm
  have hA1x : ((ggDepANDot p la1 (ggTWNX N) : ℕ) : ZMod p) = ggTWdot αa1 (ggTWx p N) := by
    rw [l05nLN_dot_cast (p := p) (N := N) (a := la1) (b := ggTWNX N) hla1_len
      (ggTWNX_length N), hla1_eq, ggTWNX_toZ]
  have hA1z : ((ggDepANDot p la1 (ggTWNZ p N (ggTWPosNat pos)) : ℕ) : ZMod p) =
      ggTWdot αa1 (ggTWz p N pos) := by
    rw [l05nLN_dot_cast (p := p) (N := N) (a := la1) (b := ggTWNZ p N (ggTWPosNat pos))
      hla1_len (ggTWNZ_length p N (ggTWPosNat pos)), hla1_eq, ggTWNZ_toZ]
  have hA2x : ((ggDepANDot p la2 (ggTWNX N) : ℕ) : ZMod p) = ggTWdot αa2 (ggTWx p N) := by
    rw [l05nLN_dot_cast (p := p) (N := N) (a := la2) (b := ggTWNX N) hla2_len
      (ggTWNX_length N), hla2_eq, ggTWNX_toZ]
  have hA2z : ((ggDepANDot p la2 (ggTWNZ p N (ggTWPosNat pos)) : ℕ) : ZMod p) =
      ggTWdot αa2 (ggTWz p N pos) := by
    rw [l05nLN_dot_cast (p := p) (N := N) (a := la2) (b := ggTWNZ p N (ggTWPosNat pos))
      hla2_len (ggTWNZ_length p N (ggTWPosNat pos)), hla2_eq, ggTWNZ_toZ]
  have h1' : lam * ggTWdot αa1 (ggTWx p N) + mu * ggTWdot αa1 (ggTWz p N pos) = 0 := by
    have h := h1
    rw [l05nLN_dot_add, l05nLN_dot_smul, l05nLN_dot_smul] at h
    exact h
  have h2' : lam * ggTWdot αa2 (ggTWx p N) + mu * ggTWdot αa2 (ggTWz p N pos) = 0 := by
    have h := h2
    rw [l05nLN_dot_add, l05nLN_dot_smul, l05nLN_dot_smul] at h
    exact h
  have hdet_zmod : ggTWdot αa1 (ggTWx p N) * ggTWdot αa2 (ggTWz p N pos) =
      ggTWdot αa1 (ggTWz p N pos) * ggTWdot αa2 (ggTWx p N) :=
    l05nLN_det_of_kernel (ggTWdot αa1 (ggTWx p N)) (ggTWdot αa1 (ggTWz p N pos))
      (ggTWdot αa2 (ggTWx p N)) (ggTWdot αa2 (ggTWz p N pos)) lam mu hlm h1' h2'
  have hdet_nat : (ggDepANDot p la1 (ggTWNX N) *
        ggDepANDot p la2 (ggTWNZ p N (ggTWPosNat pos))) % p =
      (ggDepANDot p la1 (ggTWNZ p N (ggTWPosNat pos)) *
        ggDepANDot p la2 (ggTWNX N)) % p := by
    apply (ZMod.natCast_eq_natCast_iff'
      (ggDepANDot p la1 (ggTWNX N) * ggDepANDot p la2 (ggTWNZ p N (ggTWPosNat pos)))
      (ggDepANDot p la1 (ggTWNZ p N (ggTWPosNat pos)) * ggDepANDot p la2 (ggTWNX N)) p).mp
    rw [Nat.cast_mul, Nat.cast_mul, hA1x, hA2z, hA1z, hA2x]
    exact hdet_zmod
  have hnews_eq : ggTWNNews p N [(lh1, la1), (lh2, la2)] =
      {(ha1, αa1), (ha2, αa2)} := by
    ext t
    constructor
    · rintro ⟨q, hq, ht⟩
      rcases List.mem_cons.mp hq with hq | hq
      · subst hq
        rw [ht]
        simp [hlh1_eq, hla1_eq]
      · rcases List.mem_cons.mp hq with hq | hq
        · subst hq
          rw [ht]
          simp [hlh2_eq, hla2_eq]
        · simp at hq
    · intro ht
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with ht | ht
      · subst ht
        exact ⟨(lh1, la1), by simp, by simp [hlh1_eq, hla1_eq]⟩
      · subst ht
        exact ⟨(lh2, la2), by simp, by simp [hlh2_eq, hla2_eq]⟩
  exact ⟨lh1, la1, lh2, la2, hlh1_mem, hla1_mem, hlh2_mem, hla2_mem, hd1, hd2, hd3, hd4,
    hx_list, hdet_nat, ⟨hlh1_len, hla1_len, hd1⟩, ⟨hlh2_len, hla2_len, hd3⟩, hnews_eq⟩

end CFSG.StandardType

end
