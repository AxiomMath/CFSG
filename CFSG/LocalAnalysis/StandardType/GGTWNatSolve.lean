module

public import CFSG.LocalAnalysis.StandardType.GGTWNatBase

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nE2_getD_map_range {α : Type*} (f : ℕ → α) (d : α) {n c : ℕ} (hc : c < n) :
    (((List.range n).map f).getD c d) = f c := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hc),
    List.getElem_map, List.getElem_range]

private lemma l05nE2_NA_toZ {p N : ℕ} [Fact p.Prime] (i : Fin (N - 1)) :
    ggDepANToZ p (N - 1) (ggTWNA p N i.val) = ggTWα p N i :=
  ggTWNA_toZ (p := p) (N := N) i

private lemma l05nE2_NH_toZ {p N : ℕ} [Fact p.Prime] (i : Fin (N - 1)) :
    ggDepANToZ p (N - 1) (ggTWNH p N i.val) = ggTWh p N i :=
  ggTWNH_toZ (p := p) (N := N) i

theorem ggTWNSolH_complete {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) (tgt : ℕ → ℕ)
    (v : GGTWE p N)
    (hv : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggTWdot (ggTWα p N c) v = ((tgt c.val : ℕ) : ZMod p)) :
    ∃ l ∈ ggTWNSolH p N (ggTWPosNat pos) tgt, ggTWNToZ p N l = v ∧ l.length = N - 1 := by
  obtain ⟨k, hk, hsurj⟩ := ggTWNDecode_surj (p := p) (n := N - 1) v
  refine ⟨ggTWNDecode p (N - 1) k, ?_, hsurj, ggTWNDecode_length p (N - 1) k⟩
  unfold ggTWNSolH
  dsimp only
  apply List.mem_filterMap.mpr
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  have htest : (List.range (N - 1)).all (fun c =>
      !ggTWNInJ N (ggTWPosNat pos) c ||
        ggDepANDot p (((List.range (N - 1)).map fun c => ggTWNA p N c).getD c [])
          (ggTWNDecode p (N - 1) k) == tgt c % p) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    rw [Bool.or_eq_true]
    by_cases hb : ggTWNInJ N (ggTWPosNat pos) c = true
    · right
      have hJ : ggTWInJ N pos c := (ggTWNInJ_iff pos c).mp hb
      have hclt : c < N - 1 := List.mem_range.mp hc
      rw [l05nE2_getD_map_range (fun c => ggTWNA p N c) [] hclt]
      apply beq_iff_eq.mpr
      have hv' := hv ⟨c, hclt⟩ hJ
      have hcast := ggDepANDot_cast (p := p) (N := N - 1) (ggTWNA p N c)
        (ggTWNDecode p (N - 1) k) (ggTWNA_length p N c) (ggTWNDecode_length p (N - 1) k)
      rw [l05nE2_NA_toZ (p := p) (N := N) ⟨c, hclt⟩, hsurj] at hcast
      have hz : ((ggDepANDot p (ggTWNA p N c) (ggTWNDecode p (N - 1) k) : ℕ) : ZMod p)
          = ((tgt c : ℕ) : ZMod p) := by
        rw [hcast]
        exact hv'
      have h' := (ZMod.natCast_eq_natCast_iff' (ggDepANDot p (ggTWNA p N c)
        (ggTWNDecode p (N - 1) k)) (tgt c) p).mp hz
      unfold ggDepANDot at h' ⊢
      rwa [Nat.mod_mod] at h'
    · left
      cases hbg : ggTWNInJ N (ggTWPosNat pos) c with
      | false => rfl
      | true => exact absurd hbg hb
  rw [if_pos htest]

theorem ggTWNSolH_sound {p N : ℕ} [Fact p.Prime] {pos : GGTWPos} {tgt : ℕ → ℕ} {l : List ℕ}
    (hl : l ∈ ggTWNSolH p N (ggTWPosNat pos) tgt) :
    l.length = N - 1 ∧ ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggTWdot (ggTWα p N c) (ggTWNToZ p N l) = ((tgt c.val : ℕ) : ZMod p) := by
  unfold ggTWNSolH at hl
  dsimp only at hl
  simp only [List.mem_filterMap, List.mem_range] at hl
  obtain ⟨k, hk, hfk⟩ := hl
  have htest : (List.range (N - 1)).all (fun c =>
      !ggTWNInJ N (ggTWPosNat pos) c ||
        ggDepANDot p (((List.range (N - 1)).map fun c => ggTWNA p N c).getD c [])
          (ggTWNDecode p (N - 1) k) == tgt c % p) = true := by
    by_contra h
    rw [if_neg h] at hfk
    cases hfk
  rw [if_pos htest] at hfk
  simp only [Option.some.injEq] at hfk
  rw [← hfk]
  refine ⟨ggTWNDecode_length p (N - 1) k, ?_⟩
  intro c hJ
  have hclt : c.val < N - 1 := c.isLt
  have hcond := List.all_eq_true.mp htest c.val (List.mem_range.mpr hclt)
  rw [Bool.or_eq_true] at hcond
  rcases hcond with hnot | heq
  · have hb : ggTWNInJ N (ggTWPosNat pos) c.val = true := (ggTWNInJ_iff pos c.val).mpr hJ
    rw [hb] at hnot
    simp at hnot
  · have hmod : ggDepANDot p (ggTWNA p N c.val) (ggTWNDecode p (N - 1) k)
        = tgt c.val % p := by
      have h := beq_iff_eq.mp heq
      rwa [l05nE2_getD_map_range (fun c => ggTWNA p N c) [] hclt] at h
    have hz : ((ggDepANDot p (ggTWNA p N c.val) (ggTWNDecode p (N - 1) k) : ℕ) : ZMod p)
        = ((tgt c.val : ℕ) : ZMod p) := by
      rw [hmod, ZMod.natCast_mod]
    have hcast := ggDepANDot_cast (p := p) (N := N - 1) (ggTWNA p N c.val)
      (ggTWNDecode p (N - 1) k) (ggTWNA_length p N c.val) (ggTWNDecode_length p (N - 1) k)
    rw [hcast, l05nE2_NA_toZ (p := p) (N := N) c] at hz
    show ggDepAdot (ggTWα p N c) (ggDepANToZ p (N - 1) (ggTWNDecode p (N - 1) k))
        = ((tgt c.val : ℕ) : ZMod p)
    exact hz

theorem ggTWNSolA_complete {p N : ℕ} [Fact p.Prime] (pos : GGTWPos) (tgt : ℕ → ℕ)
    (v : GGTWE p N)
    (hv : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggTWdot v (ggTWh p N c) = ((tgt c.val : ℕ) : ZMod p)) :
    ∃ l ∈ ggTWNSolA p N (ggTWPosNat pos) tgt, ggTWNToZ p N l = v ∧ l.length = N - 1 := by
  obtain ⟨k, hk, hsurj⟩ := ggTWNDecode_surj (p := p) (n := N - 1) v
  refine ⟨ggTWNDecode p (N - 1) k, ?_, hsurj, ggTWNDecode_length p (N - 1) k⟩
  unfold ggTWNSolA
  dsimp only
  apply List.mem_filterMap.mpr
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  have htest : (List.range (N - 1)).all (fun c =>
      !ggTWNInJ N (ggTWPosNat pos) c ||
        ggDepANDot p (ggTWNDecode p (N - 1) k)
          (((List.range (N - 1)).map fun c => ggTWNH p N c).getD c []) == tgt c % p) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    rw [Bool.or_eq_true]
    by_cases hb : ggTWNInJ N (ggTWPosNat pos) c = true
    · right
      have hJ : ggTWInJ N pos c := (ggTWNInJ_iff pos c).mp hb
      have hclt : c < N - 1 := List.mem_range.mp hc
      rw [l05nE2_getD_map_range (fun c => ggTWNH p N c) [] hclt]
      apply beq_iff_eq.mpr
      have hv' := hv ⟨c, hclt⟩ hJ
      have hcast := ggDepANDot_cast (p := p) (N := N - 1) (ggTWNDecode p (N - 1) k)
        (ggTWNH p N c) (ggTWNDecode_length p (N - 1) k) (ggTWNH_length p N c)
      rw [hsurj, l05nE2_NH_toZ (p := p) (N := N) ⟨c, hclt⟩] at hcast
      have hz : ((ggDepANDot p (ggTWNDecode p (N - 1) k) (ggTWNH p N c) : ℕ) : ZMod p)
          = ((tgt c : ℕ) : ZMod p) := by
        rw [hcast]
        exact hv'
      have h' := (ZMod.natCast_eq_natCast_iff' (ggDepANDot p (ggTWNDecode p (N - 1) k)
        (ggTWNH p N c)) (tgt c) p).mp hz
      unfold ggDepANDot at h' ⊢
      rwa [Nat.mod_mod] at h'
    · left
      cases hbg : ggTWNInJ N (ggTWPosNat pos) c with
      | false => rfl
      | true => exact absurd hbg hb
  rw [if_pos htest]

theorem ggTWNSolA_sound {p N : ℕ} [Fact p.Prime] {pos : GGTWPos} {tgt : ℕ → ℕ} {l : List ℕ}
    (hl : l ∈ ggTWNSolA p N (ggTWPosNat pos) tgt) :
    l.length = N - 1 ∧ ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggTWdot (ggTWNToZ p N l) (ggTWh p N c) = ((tgt c.val : ℕ) : ZMod p) := by
  unfold ggTWNSolA at hl
  dsimp only at hl
  simp only [List.mem_filterMap, List.mem_range] at hl
  obtain ⟨k, hk, hfk⟩ := hl
  have htest : (List.range (N - 1)).all (fun c =>
      !ggTWNInJ N (ggTWPosNat pos) c ||
        ggDepANDot p (ggTWNDecode p (N - 1) k)
          (((List.range (N - 1)).map fun c => ggTWNH p N c).getD c []) == tgt c % p) = true := by
    by_contra h
    rw [if_neg h] at hfk
    cases hfk
  rw [if_pos htest] at hfk
  simp only [Option.some.injEq] at hfk
  rw [← hfk]
  refine ⟨ggTWNDecode_length p (N - 1) k, ?_⟩
  intro c hJ
  have hclt : c.val < N - 1 := c.isLt
  have hcond := List.all_eq_true.mp htest c.val (List.mem_range.mpr hclt)
  rw [Bool.or_eq_true] at hcond
  rcases hcond with hnot | heq
  · have hb : ggTWNInJ N (ggTWPosNat pos) c.val = true := (ggTWNInJ_iff pos c.val).mpr hJ
    rw [hb] at hnot
    simp at hnot
  · have hmod : ggDepANDot p (ggTWNDecode p (N - 1) k) (ggTWNH p N c.val)
        = tgt c.val % p := by
      have h := beq_iff_eq.mp heq
      rwa [l05nE2_getD_map_range (fun c => ggTWNH p N c) [] hclt] at h
    have hz : ((ggDepANDot p (ggTWNDecode p (N - 1) k) (ggTWNH p N c.val) : ℕ) : ZMod p)
        = ((tgt c.val : ℕ) : ZMod p) := by
      rw [hmod, ZMod.natCast_mod]
    have hcast := ggDepANDot_cast (p := p) (N := N - 1) (ggTWNDecode p (N - 1) k)
      (ggTWNH p N c.val) (ggTWNDecode_length p (N - 1) k) (ggTWNH_length p N c.val)
    rw [hcast, l05nE2_NH_toZ (p := p) (N := N) c] at hz
    show ggDepAdot (ggDepANToZ p (N - 1) (ggTWNDecode p (N - 1) k)) (ggTWh p N c)
        = ((tgt c.val : ℕ) : ZMod p)
    exact hz

end CFSG.StandardType
