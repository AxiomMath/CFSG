module

public import CFSG.LocalAnalysis.StandardType.GGDepELNatBase
public import CFSG.LocalAnalysis.StandardType.GGTWLowOutE6Aux

public section

namespace CFSG.StandardType

open Certificates.DepED4Low Certificates.TwoDepSmall Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nEE_dot_add {p N : ℕ} (a v w : GGDepAE p N) :
    ggDepAdot a (v + w) = ggDepAdot a v + ggDepAdot a w := by
  rw [← l05nL6_form_apply a (v + w), map_add, l05nL6_form_apply a v, l05nL6_form_apply a w]

private lemma l05nEE_two_cast : (2 : ZMod 3) = (-1 : ZMod 3) := by decide

private lemma l05nEE_tgt_cast {c c0 : Fin 6} :
    (if c = c0 then (-1 : ZMod 3) else 0) =
      ((if c.val = c0.val then 2 else 0 : ℕ) : ZMod 3) := by
  by_cases h : c = c0
  · subst h
    simp [l05nEE_two_cast]
  · have hne : ¬ c.val = c0.val := fun hh => h (Fin.ext hh)
    rw [if_neg h, if_neg hne]
    simp

private lemma l05nEE_det_of_kernel {p : ℕ} [Fact p.Prime]
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

theorem ggDepELEnc1 (c0 : Fin 6) (hc0 : GGDepED4Leaf c0) (ha αa : GGDepAE 3 6)
    (hpair : GGDepELPairs1 c0 ha αa) (hdot : ggDepAdot αa ha = 2)
    (hx : ggDepAdot αa ggDepELx ≠ 0) :
    ∃ lh la : List ℕ,
      lh ∈ ggDepELSolH (fun c => if c = c0.val then 2 else 0) ∧
      la ∈ ggDepELSolA (fun c => if c = c0.val then 2 else 0) ∧
      ggDepANDot 3 la lh = 2 ∧ ggDepANDot 3 la ggDepELNX ≠ 0 ∧
      GGDepELNValid (lh, la) ∧ ggDepELNNews [(lh, la)] = {(ha, αa)} := by
  have hvH : ∀ c : Fin 6, GGDepED4In c →
      ggDepAdot (ggDepELα c) ha =
        (((fun x : ℕ => if x = c0.val then 2 else 0) c.val : ℕ) : ZMod 3) := by
    intro c hc
    rw [(hpair c hc).2, l05nEE_tgt_cast]
  have hvA : ∀ c : Fin 6, GGDepED4In c →
      ggDepAdot αa (ggDepELh c) =
        (((fun x : ℕ => if x = c0.val then 2 else 0) c.val : ℕ) : ZMod 3) := by
    intro c hc
    rw [(hpair c hc).1, l05nEE_tgt_cast]
  obtain ⟨lh, hlh_mem, hlh_eq, hlh_len⟩ :=
    ggDepELSolH_complete (fun x : ℕ => if x = c0.val then 2 else 0) ha hvH
  obtain ⟨la, hla_mem, hla_eq, hla_len⟩ :=
    ggDepELSolA_complete (fun x : ℕ => if x = c0.val then 2 else 0) αa hvA
  have hd : ggDepANDot 3 la lh = 2 := by
    have hmod : ggDepANDot 3 la lh % 3 = 2 % 3 :=
      (ZMod.natCast_eq_natCast_iff' (ggDepANDot 3 la lh) 2 3).mp (by
        rw [ggDepELDot_cast (a := la) (b := lh) hla_len hlh_len, hla_eq, hlh_eq]
        simpa using hdot)
    have hlt : ggDepANDot 3 la lh < 3 := by
      simp only [ggDepANDot]; exact Nat.mod_lt _ (by norm_num : 0 < 3)
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 2 < 3)] at hmod
  have hz : ggDepANDot 3 la ggDepELNX ≠ 0 := by
    intro h0
    apply hx
    have hcast := ggDepELDot_cast (a := la) (b := ggDepELNX) hla_len ggDepELNX_length
    rw [h0, Nat.cast_zero, hla_eq, ggDepELNX_toZ] at hcast
    exact hcast.symm
  have hnews_eq : ggDepELNNews [(lh, la)] = {(ha, αa)} := by
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

theorem ggDepELEnc2 (c c' : Fin 6) (hc : GGDepED4Leaf c) (hc' : GGDepED4Leaf c')
    (ha1 αa1 ha2 αa2 : GGDepAE 3 6) (hP : GGDepELPairs2 c c' ha1 αa1 ha2 αa2)
    (hx : ggDepAdot αa1 ggDepELx ≠ 0 ∨ ggDepAdot αa2 ggDepELx ≠ 0) (lam mu : ZMod 3)
    (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (h1 : ggDepAdot αa1 (lam • ggDepELx + mu • ggDepELz) = 0)
    (h2 : ggDepAdot αa2 (lam • ggDepELx + mu • ggDepELz) = 0) :
    ∃ lh1 la1 lh2 la2 : List ℕ,
      lh1 ∈ ggDepELSolH (fun d => if d = c.val then 2 else 0) ∧
      la1 ∈ ggDepELSolA (fun d => if d = c.val then 2 else 0) ∧
      lh2 ∈ ggDepELSolH (fun d => if d = c'.val then 2 else 0) ∧
      la2 ∈ ggDepELSolA (fun d => if d = c'.val then 2 else 0) ∧
      ggDepANDot 3 la1 lh1 = 2 ∧ ggDepANDot 3 la1 lh2 = 0 ∧
      ggDepANDot 3 la2 lh2 = 2 ∧ ggDepANDot 3 la2 lh1 = 0 ∧
      (ggDepANDot 3 la1 ggDepELNX ≠ 0 ∨ ggDepANDot 3 la2 ggDepELNX ≠ 0) ∧
      (ggDepANDot 3 la1 ggDepELNX * ggDepANDot 3 la2 ggDepELNZ) % 3 =
        (ggDepANDot 3 la1 ggDepELNZ * ggDepANDot 3 la2 ggDepELNX) % 3 ∧
      GGDepELNValid (lh1, la1) ∧ GGDepELNValid (lh2, la2) ∧
      ggDepELNNews [(lh1, la1), (lh2, la2)] = {(ha1, αa1), (ha2, αa2)} := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hvH1 : ∀ d : Fin 6, GGDepED4In d →
      ggDepAdot (ggDepELα d) ha1 =
        (((fun x : ℕ => if x = c.val then 2 else 0) d.val : ℕ) : ZMod 3) := by
    intro d hd
    rw [(hP.1 d hd).2.1, l05nEE_tgt_cast]
  have hvA1 : ∀ d : Fin 6, GGDepED4In d →
      ggDepAdot αa1 (ggDepELh d) =
        (((fun x : ℕ => if x = c.val then 2 else 0) d.val : ℕ) : ZMod 3) := by
    intro d hd
    rw [(hP.1 d hd).1, l05nEE_tgt_cast]
  have hvH2 : ∀ d : Fin 6, GGDepED4In d →
      ggDepAdot (ggDepELα d) ha2 =
        (((fun x : ℕ => if x = c'.val then 2 else 0) d.val : ℕ) : ZMod 3) := by
    intro d hd
    rw [(hP.1 d hd).2.2.2, l05nEE_tgt_cast]
  have hvA2 : ∀ d : Fin 6, GGDepED4In d →
      ggDepAdot αa2 (ggDepELh d) =
        (((fun x : ℕ => if x = c'.val then 2 else 0) d.val : ℕ) : ZMod 3) := by
    intro d hd
    rw [(hP.1 d hd).2.2.1, l05nEE_tgt_cast]
  obtain ⟨lh1, hlh1_mem, hlh1_eq, hlh1_len⟩ :=
    ggDepELSolH_complete (fun x : ℕ => if x = c.val then 2 else 0) ha1 hvH1
  obtain ⟨la1, hla1_mem, hla1_eq, hla1_len⟩ :=
    ggDepELSolA_complete (fun x : ℕ => if x = c.val then 2 else 0) αa1 hvA1
  obtain ⟨lh2, hlh2_mem, hlh2_eq, hlh2_len⟩ :=
    ggDepELSolH_complete (fun x : ℕ => if x = c'.val then 2 else 0) ha2 hvH2
  obtain ⟨la2, hla2_mem, hla2_eq, hla2_len⟩ :=
    ggDepELSolA_complete (fun x : ℕ => if x = c'.val then 2 else 0) αa2 hvA2
  have hd1 : ggDepANDot 3 la1 lh1 = 2 := by
    have hmod : ggDepANDot 3 la1 lh1 % 3 = 2 % 3 :=
      (ZMod.natCast_eq_natCast_iff' (ggDepANDot 3 la1 lh1) 2 3).mp (by
        rw [ggDepELDot_cast (a := la1) (b := lh1) hla1_len hlh1_len, hla1_eq, hlh1_eq]
        simpa using hP.2.2.2.1)
    have hlt : ggDepANDot 3 la1 lh1 < 3 := by
      simp only [ggDepANDot]; exact Nat.mod_lt _ (by norm_num : 0 < 3)
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 2 < 3)] at hmod
  have hd3 : ggDepANDot 3 la2 lh2 = 2 := by
    have hmod : ggDepANDot 3 la2 lh2 % 3 = 2 % 3 :=
      (ZMod.natCast_eq_natCast_iff' (ggDepANDot 3 la2 lh2) 2 3).mp (by
        rw [ggDepELDot_cast (a := la2) (b := lh2) hla2_len hlh2_len, hla2_eq, hlh2_eq]
        simpa using hP.2.2.2.2)
    have hlt : ggDepANDot 3 la2 lh2 < 3 := by
      simp only [ggDepANDot]; exact Nat.mod_lt _ (by norm_num : 0 < 3)
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 2 < 3)] at hmod
  have hd2 : ggDepANDot 3 la1 lh2 = 0 := by
    have hmod : ggDepANDot 3 la1 lh2 % 3 = 0 % 3 :=
      (ZMod.natCast_eq_natCast_iff' (ggDepANDot 3 la1 lh2) 0 3).mp (by
        rw [ggDepELDot_cast (a := la1) (b := lh2) hla1_len hlh2_len, hla1_eq, hlh2_eq]
        simpa using hP.2.1)
    have hlt : ggDepANDot 3 la1 lh2 < 3 := by
      simp only [ggDepANDot]; exact Nat.mod_lt _ (by norm_num : 0 < 3)
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 0 < 3)] at hmod
  have hd4 : ggDepANDot 3 la2 lh1 = 0 := by
    have hmod : ggDepANDot 3 la2 lh1 % 3 = 0 % 3 :=
      (ZMod.natCast_eq_natCast_iff' (ggDepANDot 3 la2 lh1) 0 3).mp (by
        rw [ggDepELDot_cast (a := la2) (b := lh1) hla2_len hlh1_len, hla2_eq, hlh1_eq]
        simpa using hP.2.2.1)
    have hlt : ggDepANDot 3 la2 lh1 < 3 := by
      simp only [ggDepANDot]; exact Nat.mod_lt _ (by norm_num : 0 < 3)
    rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num : 0 < 3)] at hmod
  have hx_list : ggDepANDot 3 la1 ggDepELNX ≠ 0 ∨ ggDepANDot 3 la2 ggDepELNX ≠ 0 := by
    rcases hx with hx1 | hx2
    · left
      intro h0
      apply hx1
      have hcast := ggDepELDot_cast (a := la1) (b := ggDepELNX) hla1_len ggDepELNX_length
      rw [h0, Nat.cast_zero, hla1_eq, ggDepELNX_toZ] at hcast
      exact hcast.symm
    · right
      intro h0
      apply hx2
      have hcast := ggDepELDot_cast (a := la2) (b := ggDepELNX) hla2_len ggDepELNX_length
      rw [h0, Nat.cast_zero, hla2_eq, ggDepELNX_toZ] at hcast
      exact hcast.symm
  have hA1x : ((ggDepANDot 3 la1 ggDepELNX : ℕ) : ZMod 3) = ggDepAdot αa1 ggDepELx := by
    rw [ggDepELDot_cast (a := la1) (b := ggDepELNX) hla1_len ggDepELNX_length, hla1_eq,
      ggDepELNX_toZ]
  have hA1z : ((ggDepANDot 3 la1 ggDepELNZ : ℕ) : ZMod 3) = ggDepAdot αa1 ggDepELz := by
    rw [ggDepELDot_cast (a := la1) (b := ggDepELNZ) hla1_len ggDepELNZ_length, hla1_eq,
      ggDepELNZ_toZ]
  have hA2x : ((ggDepANDot 3 la2 ggDepELNX : ℕ) : ZMod 3) = ggDepAdot αa2 ggDepELx := by
    rw [ggDepELDot_cast (a := la2) (b := ggDepELNX) hla2_len ggDepELNX_length, hla2_eq,
      ggDepELNX_toZ]
  have hA2z : ((ggDepANDot 3 la2 ggDepELNZ : ℕ) : ZMod 3) = ggDepAdot αa2 ggDepELz := by
    rw [ggDepELDot_cast (a := la2) (b := ggDepELNZ) hla2_len ggDepELNZ_length, hla2_eq,
      ggDepELNZ_toZ]
  have h1' : lam * ggDepAdot αa1 ggDepELx + mu * ggDepAdot αa1 ggDepELz = 0 := by
    have h := h1
    rw [l05nEE_dot_add, l05nL6_dot_smul, l05nL6_dot_smul] at h
    exact h
  have h2' : lam * ggDepAdot αa2 ggDepELx + mu * ggDepAdot αa2 ggDepELz = 0 := by
    have h := h2
    rw [l05nEE_dot_add, l05nL6_dot_smul, l05nL6_dot_smul] at h
    exact h
  have hdet_zmod : ggDepAdot αa1 ggDepELx * ggDepAdot αa2 ggDepELz =
      ggDepAdot αa1 ggDepELz * ggDepAdot αa2 ggDepELx :=
    l05nEE_det_of_kernel (ggDepAdot αa1 ggDepELx) (ggDepAdot αa1 ggDepELz)
      (ggDepAdot αa2 ggDepELx) (ggDepAdot αa2 ggDepELz) lam mu hlm h1' h2'
  have hdet_nat : (ggDepANDot 3 la1 ggDepELNX * ggDepANDot 3 la2 ggDepELNZ) % 3 =
      (ggDepANDot 3 la1 ggDepELNZ * ggDepANDot 3 la2 ggDepELNX) % 3 := by
    apply (ZMod.natCast_eq_natCast_iff'
      (ggDepANDot 3 la1 ggDepELNX * ggDepANDot 3 la2 ggDepELNZ)
      (ggDepANDot 3 la1 ggDepELNZ * ggDepANDot 3 la2 ggDepELNX) 3).mp
    rw [Nat.cast_mul, Nat.cast_mul, hA1x, hA2z, hA1z, hA2x]
    exact hdet_zmod
  have hnews_eq : ggDepELNNews [(lh1, la1), (lh2, la2)] =
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
