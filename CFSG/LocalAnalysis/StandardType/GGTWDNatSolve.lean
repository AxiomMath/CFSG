module

public import CFSG.LocalAnalysis.StandardType.GGTWDCells
public import CFSG.LocalAnalysis.StandardType.GGTWNatBase
public import CFSG.LocalAnalysis.StandardType.GGDepASmallNat
public import Certificates.Data.TwoDepSmallN

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmallN Certificates.DepASmall Certificates.TwoDepSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nD1_getD_map_range {α : Type*} (f : ℕ → α) (d : α) {n c : ℕ} (hc : c < n) :
    (((List.range n).map f).getD c d) = f c := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hc),
    List.getElem_map, List.getElem_range]

private lemma l05nD1_NA_toZ {p N : ℕ} [Fact p.Prime] (i : Fin (N - 1)) :
    ggDepANToZ p N (ggDepANA p N i.val) = ggDepAα p N i := by
  rw [l05nNC_toZ_A (p := p) (N := N) (i := i.val) (by omega)]

theorem ggTWDSolH_complete {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) (tgt : ℕ → ℕ)
    (v : GGDepAE p N)
    (hv : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggDepAdot (ggDepAα p N c) v = ((tgt c.val : ℕ) : ZMod p)) :
    ∃ l ∈ ggTWDSolH p N (ggTWPosNat pos) tgt, ggDepANToZ p N l = v ∧ l.length = N := by
  obtain ⟨k, hk, hsurj⟩ := ggTWNDecode_surj (p := p) (n := N) v
  refine ⟨ggTWNDecode p N k, ?_, hsurj, ggTWNDecode_length p N k⟩
  unfold ggTWDSolH
  dsimp only
  apply List.mem_filterMap.mpr
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  have htest : (List.range (N - 1)).all (fun c =>
      !ggTWNInJ N (ggTWPosNat pos) c ||
        ggDepANDot p (((List.range (N - 1)).map fun c => ggDepANA p N c).getD c [])
          (ggTWNDecode p N k) == tgt c % p) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    rw [Bool.or_eq_true]
    by_cases hb : ggTWNInJ N (ggTWPosNat pos) c = true
    · right
      have hJ : ggTWInJ N pos c := (ggTWNInJ_iff pos c).mp hb
      have hclt : c < N - 1 := List.mem_range.mp hc
      rw [l05nD1_getD_map_range (fun c => ggDepANA p N c) [] hclt]
      apply beq_iff_eq.mpr
      have hv' := hv ⟨c, hclt⟩ hJ
      have hcast := ggDepANDot_cast (p := p) (N := N) (ggDepANA p N c)
        (ggTWNDecode p N k) (l05nNC_A_length p N c) (ggTWNDecode_length p N k)
      rw [l05nD1_NA_toZ (p := p) (N := N) ⟨c, hclt⟩, hsurj] at hcast
      have hz : ((ggDepANDot p (ggDepANA p N c) (ggTWNDecode p N k) : ℕ) : ZMod p)
          = ((tgt c : ℕ) : ZMod p) := by
        rw [hcast]
        exact hv'
      have h' := (ZMod.natCast_eq_natCast_iff' (ggDepANDot p (ggDepANA p N c)
        (ggTWNDecode p N k)) (tgt c) p).mp hz
      unfold ggDepANDot at h' ⊢
      rwa [Nat.mod_mod] at h'
    · left
      cases hbg : ggTWNInJ N (ggTWPosNat pos) c with
      | false => rfl
      | true => exact absurd hbg hb
  rw [if_pos htest]

theorem ggTWDSolH_sound {p N : ℕ} [Fact p.Prime] {pos : GGTWPos} {tgt : ℕ → ℕ} {l : List ℕ}
    (hl : l ∈ ggTWDSolH p N (ggTWPosNat pos) tgt) :
    l.length = N ∧ ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggDepAdot (ggDepAα p N c) (ggDepANToZ p N l) = ((tgt c.val : ℕ) : ZMod p) := by
  unfold ggTWDSolH at hl
  dsimp only at hl
  simp only [List.mem_filterMap, List.mem_range] at hl
  obtain ⟨k, hk, hfk⟩ := hl
  have htest : (List.range (N - 1)).all (fun c =>
      !ggTWNInJ N (ggTWPosNat pos) c ||
        ggDepANDot p (((List.range (N - 1)).map fun c => ggDepANA p N c).getD c [])
          (ggTWNDecode p N k) == tgt c % p) = true := by
    by_contra h
    rw [if_neg h] at hfk
    cases hfk
  rw [if_pos htest] at hfk
  simp only [Option.some.injEq] at hfk
  rw [← hfk]
  refine ⟨ggTWNDecode_length p N k, ?_⟩
  intro c hJ
  have hclt : c.val < N - 1 := c.isLt
  have hcond := List.all_eq_true.mp htest c.val (List.mem_range.mpr hclt)
  rw [Bool.or_eq_true] at hcond
  rcases hcond with hnot | heq
  · have hb : ggTWNInJ N (ggTWPosNat pos) c.val = true := (ggTWNInJ_iff pos c.val).mpr hJ
    rw [hb] at hnot
    simp at hnot
  · have hmod : ggDepANDot p (ggDepANA p N c.val) (ggTWNDecode p N k)
        = tgt c.val % p := by
      have h := beq_iff_eq.mp heq
      rwa [l05nD1_getD_map_range (fun c => ggDepANA p N c) [] hclt] at h
    have hz : ((ggDepANDot p (ggDepANA p N c.val) (ggTWNDecode p N k) : ℕ) : ZMod p)
        = ((tgt c.val : ℕ) : ZMod p) := by
      rw [hmod, ZMod.natCast_mod]
    have hcast := ggDepANDot_cast (p := p) (N := N) (ggDepANA p N c.val)
      (ggTWNDecode p N k) (l05nNC_A_length p N c.val) (ggTWNDecode_length p N k)
    rw [hcast, l05nD1_NA_toZ (p := p) (N := N) c] at hz
    show ggDepAdot (ggDepAα p N c) (ggDepANToZ p N (ggTWNDecode p N k))
        = ((tgt c.val : ℕ) : ZMod p)
    exact hz

private lemma l05nD1_NH_toZ {p N : ℕ} [Fact p.Prime] (i : Fin (N - 1)) :
    ggDepANToZ p N (ggDepANH p N i.val) = ggDepAh p N i := by
  rw [l05nNC_toZ_H (p := p) (N := N) (i := i.val) (by omega)]

theorem ggTWDSolA_complete {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) (tgt : ℕ → ℕ)
    (v : GGDepAE p N)
    (hv : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggDepAdot v (ggDepAh p N c) = ((tgt c.val : ℕ) : ZMod p)) :
    ∃ l ∈ ggTWDSolA p N (ggTWPosNat pos) tgt, ggDepANToZ p N l = v ∧ l.length = N := by
  obtain ⟨k, hk, hsurj⟩ := ggTWNDecode_surj (p := p) (n := N) v
  refine ⟨ggTWNDecode p N k, ?_, hsurj, ggTWNDecode_length p N k⟩
  unfold ggTWDSolA
  dsimp only
  apply List.mem_filterMap.mpr
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  have htest : (List.range (N - 1)).all (fun c =>
      !ggTWNInJ N (ggTWPosNat pos) c ||
        ggDepANDot p (ggTWNDecode p N k)
          (((List.range (N - 1)).map fun c => ggDepANH p N c).getD c []) == tgt c % p) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    rw [Bool.or_eq_true]
    by_cases hb : ggTWNInJ N (ggTWPosNat pos) c = true
    · right
      have hJ : ggTWInJ N pos c := (ggTWNInJ_iff pos c).mp hb
      have hclt : c < N - 1 := List.mem_range.mp hc
      rw [l05nD1_getD_map_range (fun c => ggDepANH p N c) [] hclt]
      apply beq_iff_eq.mpr
      have hv' := hv ⟨c, hclt⟩ hJ
      have hcast := ggDepANDot_cast (p := p) (N := N) (ggTWNDecode p N k)
        (ggDepANH p N c) (ggTWNDecode_length p N k) (l05nNC_H_length p N c)
      rw [hsurj, l05nD1_NH_toZ (p := p) (N := N) ⟨c, hclt⟩] at hcast
      have hz : ((ggDepANDot p (ggTWNDecode p N k) (ggDepANH p N c) : ℕ) : ZMod p)
          = ((tgt c : ℕ) : ZMod p) := by
        rw [hcast]
        exact hv'
      have h' := (ZMod.natCast_eq_natCast_iff' (ggDepANDot p (ggTWNDecode p N k)
        (ggDepANH p N c)) (tgt c) p).mp hz
      unfold ggDepANDot at h' ⊢
      rwa [Nat.mod_mod] at h'
    · left
      cases hbg : ggTWNInJ N (ggTWPosNat pos) c with
      | false => rfl
      | true => exact absurd hbg hb
  rw [if_pos htest]

theorem ggTWDSolA_sound {p N : ℕ} [Fact p.Prime] {pos : GGTWPos} {tgt : ℕ → ℕ} {l : List ℕ}
    (hl : l ∈ ggTWDSolA p N (ggTWPosNat pos) tgt) :
    l.length = N ∧ ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggDepAdot (ggDepANToZ p N l) (ggDepAh p N c) = ((tgt c.val : ℕ) : ZMod p) := by
  unfold ggTWDSolA at hl
  dsimp only at hl
  simp only [List.mem_filterMap, List.mem_range] at hl
  obtain ⟨k, hk, hfk⟩ := hl
  have htest : (List.range (N - 1)).all (fun c =>
      !ggTWNInJ N (ggTWPosNat pos) c ||
        ggDepANDot p (ggTWNDecode p N k)
          (((List.range (N - 1)).map fun c => ggDepANH p N c).getD c []) == tgt c % p) = true := by
    by_contra h
    rw [if_neg h] at hfk
    cases hfk
  rw [if_pos htest] at hfk
  simp only [Option.some.injEq] at hfk
  rw [← hfk]
  refine ⟨ggTWNDecode_length p N k, ?_⟩
  intro c hJ
  have hclt : c.val < N - 1 := c.isLt
  have hcond := List.all_eq_true.mp htest c.val (List.mem_range.mpr hclt)
  rw [Bool.or_eq_true] at hcond
  rcases hcond with hnot | heq
  · have hb : ggTWNInJ N (ggTWPosNat pos) c.val = true := (ggTWNInJ_iff pos c.val).mpr hJ
    rw [hb] at hnot
    simp at hnot
  · have hmod : ggDepANDot p (ggTWNDecode p N k) (ggDepANH p N c.val)
        = tgt c.val % p := by
      have h := beq_iff_eq.mp heq
      rwa [l05nD1_getD_map_range (fun c => ggDepANH p N c) [] hclt] at h
    have hz : ((ggDepANDot p (ggTWNDecode p N k) (ggDepANH p N c.val) : ℕ) : ZMod p)
        = ((tgt c.val : ℕ) : ZMod p) := by
      rw [hmod, ZMod.natCast_mod]
    have hcast := ggDepANDot_cast (p := p) (N := N) (ggTWNDecode p N k)
      (ggDepANH p N c.val) (ggTWNDecode_length p N k) (l05nNC_H_length p N c.val)
    rw [hcast, l05nD1_NH_toZ (p := p) (N := N) c] at hz
    show ggDepAdot (ggDepANToZ p N (ggTWNDecode p N k)) (ggDepAh p N c)
        = ((tgt c.val : ℕ) : ZMod p)
    exact hz

end CFSG.StandardType

end
