module

public import CFSG.LocalAnalysis.StandardType.GGTWLowEnc
public import CFSG.LocalAnalysis.StandardType.GGTWLowLine
public import CFSG.LocalAnalysis.StandardType.GGTWLowHK
public import CFSG.LocalAnalysis.StandardType.GGTWLowPZB
public import CFSG.LocalAnalysis.StandardType.GGTWLowOutE8
public import CFSG.LocalAnalysis.StandardType.GGTWLowOutE6

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l05nLC_check_one {p N allow : ℕ} (d : GGTWLData)
    (h : ggTWLCheck p N allow d = true) (posn c0 mi ni : ℕ)
    (hpat : ggTWNPat1B N posn c0 mi ni = true)
    (hpos : posn ∈ [0, 1]) (hc0 : c0 ∈ List.range (N - 1))
    (hmi : mi = 1 ∨ mi = 2) (hni : ni = 1 ∨ ni = 2) :
    ∃ wits, d.one.lookup (posn, c0, mi, ni) = some wits ∧
      (∀ w ∈ wits, ggTWNKillValid N N w = true) ∧
      ggTWLCases1 p N posn allow c0 mi ni (ggTWNRoots p N) wits
        ((d.excOne.lookup (posn, c0, mi, ni)).getD []) = true := by
  have hh := h
  rw [ggTWLCheck] at hh
  have h1 := Bool.and_eq_true_iff.mp hh
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have h3 := Bool.and_eq_true_iff.mp h2.1
  have hone : d.one.all (fun e => e.2.all (ggTWNKillValid N N)) = true := h3.2
  have hall := List.all_eq_true.mp h1.2 posn hpos
  have ha := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hall).1 c0 hc0
  have hmi' : mi ∈ [1, 2] := by rcases hmi with rfl | rfl <;> simp
  have hni' : ni ∈ [1, 2] := by rcases hni with rfl | rfl <;> simp
  have hb := List.all_eq_true.mp ha mi hmi'
  have hd := List.all_eq_true.mp hb ni hni'
  rw [if_pos hpat] at hd
  cases hlook : d.one.lookup (posn, c0, mi, ni) with
  | none => rw [hlook] at hd; simp at hd
  | some wits =>
      rw [hlook] at hd
      obtain ⟨l₁, l₂, hdata, -⟩ := List.lookup_eq_some_iff.mp hlook
      have hentry : ((posn, c0, mi, ni), wits) ∈ d.one := by
        rw [hdata]; simp
      have hwv : ∀ w ∈ wits, ggTWNKillValid N N w = true := by
        intro w hw
        exact List.all_eq_true.mp
          (List.all_eq_true.mp hone (((posn, c0, mi, ni), wits)) hentry) w hw
      exact ⟨wits, rfl, hwv, hd⟩

theorem l05nLC_check_two {p N allow : ℕ} (d : GGTWLData)
    (h : ggTWLCheck p N allow d = true) (posn c : ℕ) (c2 : Option ℕ)
    (hpat : ggTWNPat2B N posn c c2 = true)
    (hpos : posn ∈ [0, 1]) (hc : c ∈ List.range (N - 1))
    (hc2 : c2 ∈ none :: (List.range (N - 1)).map some) :
    ∃ wits, d.two.lookup (posn, c, ggTWNCode c2) = some wits ∧
      (∀ w ∈ wits, ggTWNKillValid N (N + 1) w = true) ∧
      ggTWLCases2 p N posn allow c c2 (ggTWNRoots p N) wits
        ((d.excTwo.lookup (posn, c, ggTWNCode c2)).getD []) = true := by
  have hh := h
  rw [ggTWLCheck] at hh
  have h1 := Bool.and_eq_true_iff.mp hh
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have htwo : d.two.all (fun e => e.2.all (ggTWNKillValid N (N + 1))) = true := h2.2
  have hall := List.all_eq_true.mp h1.2 posn hpos
  have ha := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hall).2 c hc
  have hb := List.all_eq_true.mp ha c2 hc2
  rw [if_pos hpat] at hb
  cases hlook : d.two.lookup (posn, c, ggTWNCode c2) with
  | none => rw [hlook] at hb; simp at hb
  | some wits =>
      rw [hlook] at hb
      obtain ⟨l₁, l₂, hdata, -⟩ := List.lookup_eq_some_iff.mp hlook
      have hentry : ((posn, c, ggTWNCode c2), wits) ∈ d.two := by
        rw [hdata]; simp
      have hwv : ∀ w ∈ wits, ggTWNKillValid N (N + 1) w = true := by
        intro w hw
        exact List.all_eq_true.mp
          (List.all_eq_true.mp htwo (((posn, c, ggTWNCode c2), wits)) hentry) w hw
      exact ⟨wits, rfl, hwv, hb⟩

theorem l05nLC_cases1_extract {p N allow : ℕ} (posn c0 mi ni : ℕ)
    (R : List (List ℕ)) (wits : List GGTWNKill)
    (exc : List ((List ℕ × List ℕ) × GGTWLReason))
    (h : ggTWLCases1 p N posn allow c0 mi ni R wits exc = true)
    {lh la : List ℕ}
    (hlh : lh ∈ ggTWNSolH p N posn (fun c => if c = c0 then (p - ni % p) % p else 0))
    (hla : la ∈ ggTWNSolA p N posn (fun c => if c = c0 then (p - mi % p) % p else 0))
    (hd : ggDepANDot p la lh = 2 % p)
    (hz : ggDepANDot p la (ggTWNX N) ≠ 0) :
    (∃ w ∈ wits, ggTWNKillTest p N [(lh, la)] R w = true) ∨
      (∃ e ∈ exc, ggTWLVecEq p e.1.1 lh = true ∧ ggTWLVecEq p e.1.2 la = true ∧
        ggTWLReasonTest p N posn allow [(lh, la)] e.2 = true) := by
  simp only [ggTWLCases1] at h
  have h1 := List.all_eq_true.mp h lh hlh
  have h2 := List.all_eq_true.mp h1 la hla
  have hc : (ggDepANDot p la lh == 2 % p && ggDepANDot p la (ggTWNX N) != 0) = true := by
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr hd, bne_iff_ne.mpr hz⟩
  rw [if_pos hc] at h2
  cases hfind : exc.find?
      (fun e => ggTWLVecEq p e.1.1 lh && ggTWLVecEq p e.1.2 la) with
  | none =>
      rw [hfind] at h2
      exact Or.inl (List.any_eq_true.mp h2)
  | some e =>
      rw [hfind] at h2
      have hmem : e ∈ exc := List.mem_of_find?_eq_some hfind
      have hpred : (ggTWLVecEq p e.1.1 lh && ggTWLVecEq p e.1.2 la) = true :=
        List.find?_some (p := fun e => ggTWLVecEq p e.1.1 lh && ggTWLVecEq p e.1.2 la)
          (a := e) hfind
      rw [Bool.and_eq_true] at hpred
      exact Or.inr ⟨e, hmem, hpred.1, hpred.2, h2⟩

theorem l05nLC_cases2_extract {p N allow : ℕ} (posn c : ℕ) (c2 : Option ℕ)
    (R : List (List ℕ)) (wits : List GGTWNKill)
    (exc : List ((List ℕ × List ℕ × List ℕ × List ℕ) × GGTWLReason))
    (h : ggTWLCases2 p N posn allow c c2 R wits exc = true)
    {lh1 la1 lh2 la2 : List ℕ}
    (hlh1 : lh1 ∈ ggTWNSolH p N posn (fun c' => if c' = c then (p - 1) % p else 0))
    (hla1 : la1 ∈ ggTWNSolA p N posn (fun c' => if c' = c then (p - 1) % p else 0))
    (hlh2 : lh2 ∈ ggTWNSolH p N posn (ggTWNTgt2 p c2))
    (hla2 : la2 ∈ ggTWNSolA p N posn (ggTWNTgt2 p c2))
    (hd1 : ggDepANDot p la1 lh1 = 2 % p)
    (hd2 : ggDepANDot p la1 lh2 = (match c2 with | none => (p - 1) % p | some _ => 0))
    (hd3 : ggDepANDot p la2 lh2 = 2 % p)
    (hd4 : ggDepANDot p la2 lh1 = (match c2 with | none => (p - 1) % p | some _ => 0))
    (hx : ggDepANDot p la1 (ggTWNX N) ≠ 0 ∨ ggDepANDot p la2 (ggTWNX N) ≠ 0)
    (hdet : (ggDepANDot p la1 (ggTWNX N) * ggDepANDot p la2 (ggTWNZ p N posn)) % p =
      (ggDepANDot p la1 (ggTWNZ p N posn) * ggDepANDot p la2 (ggTWNX N)) % p) :
    (∃ w ∈ wits, ggTWNKillTest p N [(lh1, la1), (lh2, la2)] R w = true) ∨
      (∃ e ∈ exc, ggTWLVecEq p e.1.1 lh1 = true ∧ ggTWLVecEq p e.1.2.1 la1 = true ∧
        ggTWLVecEq p e.1.2.2.1 lh2 = true ∧ ggTWLVecEq p e.1.2.2.2 la2 = true ∧
        ggTWLReasonTest p N posn allow [(lh1, la1), (lh2, la2)] e.2 = true) := by
  cases c2 with
  | none =>
      simp only [ggTWLCases2] at h
      have e1 := List.all_eq_true.mp h lh1 hlh1
      have e2 := List.all_eq_true.mp e1 la1 hla1
      rw [if_pos (beq_iff_eq.mpr hd1)] at e2
      have e3 := List.all_eq_true.mp e2 lh2 hlh2
      rw [if_pos (beq_iff_eq.mpr hd2)] at e3
      have e4 := List.all_eq_true.mp e3 la2 hla2
      have hor : (ggDepANDot p la1 (ggTWNX N) != 0 ||
          ggDepANDot p la2 (ggTWNX N) != 0) = true := by
        rw [Bool.or_eq_true_iff]
        exact hx.imp (fun h => bne_iff_ne.mpr h) (fun h => bne_iff_ne.mpr h)
      have hcond : (ggDepANDot p la2 lh2 == 2 % p && ggDepANDot p la2 lh1 == (p - 1) % p &&
          (ggDepANDot p la1 (ggTWNX N) != 0 || ggDepANDot p la2 (ggTWNX N) != 0) &&
          (ggDepANDot p la1 (ggTWNX N) * ggDepANDot p la2 (ggTWNZ p N posn)) % p ==
            (ggDepANDot p la1 (ggTWNZ p N posn) * ggDepANDot p la2 (ggTWNX N)) % p) = true := by
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨⟨beq_iff_eq.mpr hd3, beq_iff_eq.mpr hd4⟩, hor⟩, beq_iff_eq.mpr hdet⟩
      rw [if_pos hcond] at e4
      cases hfind : exc.find? (fun e => ggTWLVecEq p e.1.1 lh1 && ggTWLVecEq p e.1.2.1 la1 &&
          ggTWLVecEq p e.1.2.2.1 lh2 && ggTWLVecEq p e.1.2.2.2 la2) with
      | none => rw [hfind] at e4; exact Or.inl (List.any_eq_true.mp e4)
      | some e =>
          rw [hfind] at e4
          have hmem : e ∈ exc := List.mem_of_find?_eq_some hfind
          have hpred := List.find?_some (p := fun e => ggTWLVecEq p e.1.1 lh1 &&
            ggTWLVecEq p e.1.2.1 la1 && ggTWLVecEq p e.1.2.2.1 lh2 &&
            ggTWLVecEq p e.1.2.2.2 la2) (a := e) hfind
          simp only [Bool.and_eq_true] at hpred
          exact Or.inr ⟨e, hmem, hpred.1.1.1, hpred.1.1.2, hpred.1.2, hpred.2, e4⟩
  | some c2' =>
      simp only [ggTWLCases2] at h
      have e1 := List.all_eq_true.mp h lh1 hlh1
      have e2 := List.all_eq_true.mp e1 la1 hla1
      rw [if_pos (beq_iff_eq.mpr hd1)] at e2
      have e3 := List.all_eq_true.mp e2 lh2 hlh2
      rw [if_pos (beq_iff_eq.mpr hd2)] at e3
      have e4 := List.all_eq_true.mp e3 la2 hla2
      have hor : (ggDepANDot p la1 (ggTWNX N) != 0 ||
          ggDepANDot p la2 (ggTWNX N) != 0) = true := by
        rw [Bool.or_eq_true_iff]
        exact hx.imp (fun h => bne_iff_ne.mpr h) (fun h => bne_iff_ne.mpr h)
      have hcond : (ggDepANDot p la2 lh2 == 2 % p && ggDepANDot p la2 lh1 == 0 &&
          (ggDepANDot p la1 (ggTWNX N) != 0 || ggDepANDot p la2 (ggTWNX N) != 0) &&
          (ggDepANDot p la1 (ggTWNX N) * ggDepANDot p la2 (ggTWNZ p N posn)) % p ==
            (ggDepANDot p la1 (ggTWNZ p N posn) * ggDepANDot p la2 (ggTWNX N)) % p) = true := by
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨⟨beq_iff_eq.mpr hd3, beq_iff_eq.mpr hd4⟩, hor⟩, beq_iff_eq.mpr hdet⟩
      rw [if_pos hcond] at e4
      cases hfind : exc.find? (fun e => ggTWLVecEq p e.1.1 lh1 && ggTWLVecEq p e.1.2.1 la1 &&
          ggTWLVecEq p e.1.2.2.1 lh2 && ggTWLVecEq p e.1.2.2.2 la2) with
      | none => rw [hfind] at e4; exact Or.inl (List.any_eq_true.mp e4)
      | some e =>
          rw [hfind] at e4
          have hmem : e ∈ exc := List.mem_of_find?_eq_some hfind
          have hpred := List.find?_some (p := fun e => ggTWLVecEq p e.1.1 lh1 &&
            ggTWLVecEq p e.1.2.1 la1 && ggTWLVecEq p e.1.2.2.1 lh2 &&
            ggTWLVecEq p e.1.2.2.2 la2) (a := e) hfind
          simp only [Bool.and_eq_true] at hpred
          exact Or.inr ⟨e, hmem, hpred.1.1.1, hpred.1.1.2, hpred.1.2, hpred.2, e4⟩

end CFSG.StandardType

end
