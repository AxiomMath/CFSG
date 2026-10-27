module

public import CFSG.LocalAnalysis.StandardType.GGDepELNatTool
public import CFSG.LocalAnalysis.StandardType.GGTWNatBase

public section

namespace CFSG.StandardType

open Certificates.DepED4Low Certificates.TwoDepSmall Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nBB_mem_J {c : ℕ} (hc : c ∈ ggDepELNJ) :
    ∃ h : c < 6, GGDepED4In ⟨c, h⟩ := by
  simp [ggDepELNJ] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by unfold GGDepED4In; decide⟩

theorem ggDepELNX_length : ggDepELNX.length = 6 := by
  decide

theorem ggDepELNH_length {i : ℕ} (hi : i < 6) : (ggDepELNH i).length = 6 := by
  interval_cases i <;> decide

theorem ggDepELNA_length {i : ℕ} (hi : i < 6) : (ggDepELNA i).length = 6 := by
  interval_cases i <;> decide

theorem ggDepELNZ_length : ggDepELNZ.length = 6 := by
  decide

theorem ggDepELNX_toZ : ggDepELToZ ggDepELNX = ggDepELx := by
  funext j
  fin_cases j <;> decide

theorem ggDepELNH_toZ (i : Fin 6) : ggDepELToZ (ggDepELNH i.val) = ggDepELh i := by
  fin_cases i <;> funext j <;> fin_cases j <;> decide

theorem ggDepELNA_toZ (i : Fin 6) : ggDepELToZ (ggDepELNA i.val) = ggDepELα i := by
  fin_cases i <;> funext j <;> fin_cases j <;> decide

theorem ggDepELNZ_toZ : ggDepELToZ ggDepELNZ = ggDepELz := by
  funext j
  fin_cases j <;> decide

theorem ggDepELNFrame_valid {g : ℕ} (hg : g < 6) :
    GGDepELNValid (ggDepELNH g, ggDepELNA g) := by
  interval_cases g <;> (unfold GGDepELNValid; decide)

theorem ggDepELNInJ_iff (c : Fin 6) : ggDepELNInJ c.val = true ↔ GGDepED4In c := by
  fin_cases c <;> (unfold GGDepED4In ggDepELNInJ; decide)

theorem ggDepELNInJ_lt {c : ℕ} (h : ggDepELNInJ c = true) : c < 6 := by
  simp [ggDepELNInJ, Bool.and_eq_true, decide_eq_true_iff] at h
  omega

theorem ggDepELNLeaves_iff (c : Fin 6) : c.val ∈ ggDepELNLeaves ↔ GGDepED4Leaf c := by
  fin_cases c <;> (unfold GGDepED4Leaf; decide)

theorem ggDepELSolH_complete (tgt : ℕ → ℕ) (v : GGDepAE 3 6)
    (hv : ∀ c : Fin 6, GGDepED4In c →
      ggDepAdot (ggDepELα c) v = ((tgt c.val : ℕ) : ZMod 3)) :
    ∃ l ∈ ggDepELSolH tgt, ggDepELToZ l = v ∧ l.length = 6 := by
  obtain ⟨k, hk, hsurj⟩ := ggTWNDecode_surj (p := 3) (n := 6) v
  refine ⟨ggTWNDecode 3 6 k, ?_, hsurj, ggTWNDecode_length 3 6 k⟩
  unfold ggDepELSolH
  dsimp only
  apply List.mem_filterMap.mpr
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  have htest : ggDepELNJ.all (fun c =>
      ggDepANDot 3 (ggDepELNA c) (ggTWNDecode 3 6 k) == tgt c % 3) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨hc6, hIn⟩ := l05nBB_mem_J hc
    apply beq_iff_eq.mpr
    have hv' := hv ⟨c, hc6⟩ hIn
    have hsurj' : ggDepELToZ (ggTWNDecode 3 6 k) = v := hsurj
    have hcast := ggDepELDot_cast (a := ggDepELNA c) (b := ggTWNDecode 3 6 k)
      (ggDepELNA_length hc6) (ggTWNDecode_length 3 6 k)
    rw [ggDepELNA_toZ ⟨c, hc6⟩, hsurj'] at hcast
    have hz : ((ggDepANDot 3 (ggDepELNA c) (ggTWNDecode 3 6 k) : ℕ) : ZMod 3)
        = ((tgt c : ℕ) : ZMod 3) := by
      rw [hcast, hv']
    have h' := (ZMod.natCast_eq_natCast_iff' (ggDepANDot 3 (ggDepELNA c)
      (ggTWNDecode 3 6 k)) (tgt c) 3).mp hz
    unfold ggDepANDot at h' ⊢
    rwa [Nat.mod_mod] at h'
  rw [if_pos htest]

theorem ggDepELSolH_sound {tgt : ℕ → ℕ} {l : List ℕ} (hl : l ∈ ggDepELSolH tgt) :
    l.length = 6 ∧ ∀ c : Fin 6, GGDepED4In c →
      ggDepAdot (ggDepELα c) (ggDepELToZ l) = ((tgt c.val : ℕ) : ZMod 3) := by
  unfold ggDepELSolH at hl
  dsimp only at hl
  simp only [List.mem_filterMap, List.mem_range] at hl
  obtain ⟨k, hk, hfk⟩ := hl
  have htest : ggDepELNJ.all (fun c =>
      ggDepANDot 3 (ggDepELNA c) (ggTWNDecode 3 6 k) == tgt c % 3) = true := by
    by_contra h
    rw [if_neg h] at hfk
    exact absurd hfk (by simp)
  rw [if_pos htest] at hfk
  simp only [Option.some.injEq] at hfk
  rw [← hfk]
  refine ⟨ggTWNDecode_length 3 6 k, ?_⟩
  intro c hIn
  have hmem : c.val ∈ ggDepELNJ := by
    have h0 : c.val ≠ 0 := fun h => hIn.1 (Fin.ext h)
    have h5 : c.val ≠ 5 := fun h => hIn.2 (Fin.ext h)
    simp only [ggDepELNJ, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false]
    omega
  have hcond := List.all_eq_true.mp htest c.val hmem
  have hmod := beq_iff_eq.mp hcond
  have hz : ((ggDepANDot 3 (ggDepELNA c.val) (ggTWNDecode 3 6 k) : ℕ) : ZMod 3)
      = ((tgt c.val : ℕ) : ZMod 3) := by
    rw [hmod, ZMod.natCast_mod]
  have hcast := ggDepELDot_cast (a := ggDepELNA c.val) (b := ggTWNDecode 3 6 k)
    (ggDepELNA_length c.isLt) (ggTWNDecode_length 3 6 k)
  rw [hcast, ggDepELNA_toZ c] at hz
  exact hz

theorem ggDepELSolA_complete (tgt : ℕ → ℕ) (v : GGDepAE 3 6)
    (hv : ∀ c : Fin 6, GGDepED4In c →
      ggDepAdot v (ggDepELh c) = ((tgt c.val : ℕ) : ZMod 3)) :
    ∃ l ∈ ggDepELSolA tgt, ggDepELToZ l = v ∧ l.length = 6 := by
  obtain ⟨k, hk, hsurj⟩ := ggTWNDecode_surj (p := 3) (n := 6) v
  refine ⟨ggTWNDecode 3 6 k, ?_, hsurj, ggTWNDecode_length 3 6 k⟩
  unfold ggDepELSolA
  dsimp only
  apply List.mem_filterMap.mpr
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  have htest : ggDepELNJ.all (fun c =>
      ggDepANDot 3 (ggTWNDecode 3 6 k) (ggDepELNH c) == tgt c % 3) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨hc6, hIn⟩ := l05nBB_mem_J hc
    apply beq_iff_eq.mpr
    have hv' := hv ⟨c, hc6⟩ hIn
    have hsurj' : ggDepELToZ (ggTWNDecode 3 6 k) = v := hsurj
    have hcast := ggDepELDot_cast (a := ggTWNDecode 3 6 k) (b := ggDepELNH c)
      (ggTWNDecode_length 3 6 k) (ggDepELNH_length hc6)
    rw [ggDepELNH_toZ ⟨c, hc6⟩, hsurj'] at hcast
    have hz : ((ggDepANDot 3 (ggTWNDecode 3 6 k) (ggDepELNH c) : ℕ) : ZMod 3)
        = ((tgt c : ℕ) : ZMod 3) := by
      rw [hcast, hv']
    have h' := (ZMod.natCast_eq_natCast_iff' (ggDepANDot 3 (ggTWNDecode 3 6 k)
      (ggDepELNH c)) (tgt c) 3).mp hz
    unfold ggDepANDot at h' ⊢
    rwa [Nat.mod_mod] at h'
  rw [if_pos htest]

theorem ggDepELSolA_sound {tgt : ℕ → ℕ} {l : List ℕ} (hl : l ∈ ggDepELSolA tgt) :
    l.length = 6 ∧ ∀ c : Fin 6, GGDepED4In c →
      ggDepAdot (ggDepELToZ l) (ggDepELh c) = ((tgt c.val : ℕ) : ZMod 3) := by
  unfold ggDepELSolA at hl
  dsimp only at hl
  simp only [List.mem_filterMap, List.mem_range] at hl
  obtain ⟨k, hk, hfk⟩ := hl
  have htest : ggDepELNJ.all (fun c =>
      ggDepANDot 3 (ggTWNDecode 3 6 k) (ggDepELNH c) == tgt c % 3) = true := by
    by_contra h
    rw [if_neg h] at hfk
    exact absurd hfk (by simp)
  rw [if_pos htest] at hfk
  simp only [Option.some.injEq] at hfk
  rw [← hfk]
  refine ⟨ggTWNDecode_length 3 6 k, ?_⟩
  intro c hIn
  have hmem : c.val ∈ ggDepELNJ := by
    have h0 : c.val ≠ 0 := fun h => hIn.1 (Fin.ext h)
    have h5 : c.val ≠ 5 := fun h => hIn.2 (Fin.ext h)
    simp only [ggDepELNJ, List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false]
    omega
  have hcond := List.all_eq_true.mp htest c.val hmem
  have hmod := beq_iff_eq.mp hcond
  have hz : ((ggDepANDot 3 (ggTWNDecode 3 6 k) (ggDepELNH c.val) : ℕ) : ZMod 3)
      = ((tgt c.val : ℕ) : ZMod 3) := by
    rw [hmod, ZMod.natCast_mod]
  have hcast := ggDepELDot_cast (a := ggTWNDecode 3 6 k) (b := ggDepELNH c.val)
    (ggTWNDecode_length 3 6 k) (ggDepELNH_length c.isLt)
  rw [hcast, ggDepELNH_toZ c] at hz
  exact hz

end CFSG.StandardType

end
