module

public import CFSG.LocalAnalysis.StandardType.GGDepED4Defs
public import CFSG.LocalAnalysis.StandardType.GGDepECheck

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


open Certificates.DepASmall

@[expose] def ggDepED4Cases (p c0 : Nat) (wits : List GGDepANWit) : Bool :=
  let m := (p - 1) % p
  let n := (p - 1) % p
  let HS := (ggDepEAllVecs p 7).filter fun ha =>
    (List.range 6).all fun c => c == 0 || c == 5 || ha.getD c 0 == (if c == c0 then n else 0)
  let AS := (ggDepEAllVecs p 7).filter fun aa =>
    (List.range 6).all fun c =>
      c == 0 || c == 5 || ggDepANDot p aa (ggDepEH p c) == (if c == c0 then m else 0)
  HS.all fun ha => AS.all fun aa =>
    if ggDepANDot p aa ha == 2 % p && aa.getD 6 0 % p != 0 then
      wits.any (fun w => ggDepEWitTest p w ha aa)
    else true

@[expose] def ggDepED4Check (data : List (Nat × List GGDepANWit)) : Bool :=
  data.all (fun e => e.2.all (ggDepANWitValid 7)) && [1, 2, 4].all fun c0 =>
    match data.lookup c0 with
    | none => false
    | some wits => ggDepED4Cases 3 c0 wits

@[expose] def ggDepED4Data : List (Nat × List GGDepANWit) := [
  (1, [⟨6, [], 6, [5]⟩, ⟨1, [3], 1, [6, 2, 0, 6, 2, 3]⟩,
    ⟨0, [], 0, [6]⟩, ⟨0, [2], 0, [6, 5, 6, 4, 5, 6]⟩, ⟨0, [4, 1, 3, 2], 1, [6, 5, 3, 4, 2, 3]⟩,
    ⟨0, [], 2, [6, 5, 4, 3]⟩, ⟨0, [1, 6], 1, [3, 4, 5, 6, 2, 3]⟩]),
  (2, [⟨0, [], 0, [2, 6, 5, 6, 2]⟩, ⟨6, [], 6, [0]⟩,
    ⟨2, [3], 2, [6, 4, 5, 6, 4, 3]⟩, ⟨6, [], 6, [5]⟩, ⟨2, [], 2, [6, 0, 6]⟩,
    ⟨0, [], 1, [2, 6, 3, 4, 2, 3]⟩, ⟨0, [5, 3, 4, 1, 3, 2], 1, [6, 4, 5, 2, 6, 3, 4, 2, 3]⟩]),
  (4, [⟨6, [], 6, [5]⟩, ⟨5, [], 4, [4, 6, 0, 6, 5]⟩,
    ⟨2, [5, 4, 3], 0, [0, 6, 5, 4, 3, 2]⟩, ⟨1, [], 2, [3, 4, 6, 5, 4, 3]⟩,
    ⟨4, [], 5, [6, 0, 6, 2, 0, 6]⟩, ⟨0, [2, 3, 4, 1, 3, 2], 1, [5, 6, 4, 0, 6, 3, 4, 2, 3]⟩])]

private lemma l05nD4C_mem_allVecs {p : Nat} (l : List Nat) (h : ∀ a ∈ l, a < p) :
    l ∈ ggDepEAllVecs p l.length := by
  induction l with
  | nil => simp [ggDepEAllVecs]
  | cons a t ih =>
      have ha : a ∈ List.range p := List.mem_range.mpr (h a (by simp))
      have ht : ∀ b ∈ t, b < p := fun b hb => h b (by simp [hb])
      have hmap : a :: t ∈ (ggDepEAllVecs p t.length).map (a :: ·) :=
        List.mem_map.mpr ⟨t, ih ht, rfl⟩
      show a :: t ∈ ggDepEAllVecs p (t.length + 1)
      simp only [ggDepEAllVecs]
      exact List.mem_flatMap.mpr ⟨a, ha, hmap⟩

private lemma l05nD4C_allVecs_three (n : Nat) (v : Fin n → ZMod 3) :
    ∃ l ∈ ggDepEAllVecs 3 n, l.length = n ∧ (∀ a ∈ l, a < 3) ∧ ggDepANToZ 3 n l = v := by
  set l : List Nat := (List.range n).map fun j => if h : j < n then (v ⟨j, h⟩).val else 0
    with hl_def
  have hl_len : l.length = n := by simp [hl_def]
  have hl_lt : ∀ a ∈ l, a < 3 := by
    intro a ha
    rw [hl_def, List.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    by_cases h : j < n
    · rw [dif_pos h]; exact ZMod.val_lt _
    · rw [dif_neg h]; omega
  have hl_getD : ∀ j : Fin n, l.getD j.val 0 = (v j).val := by
    intro j
    have hj : j.val < l.length := by rw [hl_len]; exact j.isLt
    rw [List.getD_eq_getElem l 0 hj]
    simp only [hl_def, List.getElem_map, List.getElem_range]
    rw [dif_pos j.isLt]
  have hl_toZ : ggDepANToZ 3 n l = v := by
    funext j
    rw [ggDepANToZ, hl_getD j, ZMod.natCast_zmod_val]
  exact ⟨l, by rw [← hl_len]; exact l05nD4C_mem_allVecs l hl_lt, hl_len, hl_lt, hl_toZ⟩

private lemma l05nD4C_cartan_cast (j i : Fin 6) :
    ((ggDepAThreeE6Res 3 j.val i.val : Nat) : ZMod 3) =
      ((CartanMatrix.E 6 j i : ℤ) : ZMod 3) := by
  fin_cases i <;> fin_cases j <;> decide
private lemma l05nD4C_toZ_EH (i : Nat) (hi : i < 6) :
    ggDepANToZ 3 7 (ggDepEH 3 i) = ggDepEh 3 ⟨i, hi⟩ := by
  funext j
  rw [ggDepANToZ]
  have hjlen : j.val < (ggDepEH 3 i).length := by simpa [ggDepEH] using j.isLt
  rw [List.getD_eq_getElem (ggDepEH 3 i) 0 hjlen]
  simp only [ggDepEH, List.getElem_map, List.getElem_range]
  by_cases hj : j.val < 6
  · rw [if_pos hj, ggDepEh, dif_pos hj]
    exact l05nD4C_cartan_cast ⟨j.val, hj⟩ ⟨i, hi⟩
  · rw [if_neg hj, ggDepEh, dif_neg hj]
    rfl
private lemma l05nD4C_toZ_EA (i : Nat) (hi : i < 6) :
    ggDepANToZ 3 7 (ggDepEA i) = ggDepEα 3 ⟨i, hi⟩ := by
  funext j
  rw [ggDepANToZ]
  have hjlen : j.val < (ggDepEA i).length := by simpa [ggDepEA] using j.isLt
  rw [List.getD_eq_getElem (ggDepEA i) 0 hjlen]
  simp only [ggDepEA, List.getElem_map, List.getElem_range]
  rw [ggDepEα]
  by_cases h : j.val = i
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]; simp
private lemma l05nD4C_dot_alpha_self (i : Fin 6) :
    ggDepAdot (ggDepEα 3 i) (ggDepEh 3 i) = 2 := by
  fin_cases i <;> decide +kernel

private lemma l05nD4C_dot_alpha (p : Nat) (i : Fin 6) (v : GGDepAE p 7) :
    ggDepAdot (ggDepEα p i) v = v ⟨i.val, by omega⟩ := by
  rw [ggDepAdot]
  rw [Finset.sum_eq_single ⟨i.val, by omega⟩]
  · simp [ggDepEα]
  · intro j _ hj
    simp only [ggDepEα]
    rw [if_neg]
    · simp
    · intro hh; exact hj (Fin.ext hh)
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma l05nD4C_dot_ex (p : Nat) (v : GGDepAE p 7) :
    ggDepAdot v (ggDepEx p) = v ⟨6, by omega⟩ := by
  rw [ggDepAdot]
  rw [Finset.sum_eq_single ⟨6, by omega⟩]
  · simp [ggDepEx]
  · intro j _ hj
    simp only [ggDepEx]
    rw [if_neg]
    · simp
    · intro hh; exact hj (Fin.ext hh)
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma l05nD4C_zmod_eq_of_lt {x y : Nat} (hx : x < 3) (hy : y < 3)
    (h : (x : ZMod 3) = (y : ZMod 3)) : x = y := by
  have h2 := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2
  exact h2
private lemma l05nD4C_gen_length1 {p : Nat} {ha aa : List Nat} (hha : ha.length = 7)
    (haa : aa.length = 7) (g : Nat) : (ggDepEGen p ha aa g).1.length = 7 := by
  unfold ggDepEGen
  split_ifs with h
  · simp [ggDepEH]
  · exact hha
private lemma l05nD4C_gen_length2 {p : Nat} {ha aa : List Nat} (hha : ha.length = 7)
    (haa : aa.length = 7) (g : Nat) : (ggDepEGen p ha aa g).2.length = 7 := by
  unfold ggDepEGen
  split_ifs with h
  · simp [ggDepEA]
  · exact haa
private lemma l05nD4C_gen_dot {ha aa : List Nat} (hha : ha.length = 7)
    (haa : aa.length = 7) (hdot : ggDepANDot 3 aa ha = 2 % 3) (g : Nat) :
    ggDepAdot (ggDepANToZ 3 7 (ggDepEGen 3 ha aa g).2)
      (ggDepANToZ 3 7 (ggDepEGen 3 ha aa g).1) = 2 := by
  by_cases h : g < 6
  · simp only [ggDepEGen, if_pos h]
    rw [l05nD4C_toZ_EH g h, l05nD4C_toZ_EA g h]
    exact l05nD4C_dot_alpha_self ⟨g, h⟩
  · simp only [ggDepEGen, if_neg h]
    rw [← ggDepANDot_cast (p := 3) (N := 7) aa ha haa hha, hdot, ZMod.natCast_mod]
    rfl
private lemma l05nD4C_gen_mem {ha aa : List Nat} (g : Nat) :
    ggDepARefl (ggDepANToZ 3 7 (ggDepEGen 3 ha aa g).1)
      (ggDepANToZ 3 7 (ggDepEGen 3 ha aa g).2) ∈
      Submonoid.closure (Set.range (fun i : Fin 6 =>
        ggDepARefl (ggDepEh 3 i) (ggDepEα 3 i)) ∪
        {ggDepARefl (ggDepANToZ 3 7 ha) (ggDepANToZ 3 7 aa)}) := by
  by_cases h : g < 6
  · simp only [ggDepEGen, if_pos h]
    rw [l05nD4C_toZ_EH g h, l05nD4C_toZ_EA g h]
    exact Submonoid.subset_closure (Or.inl ⟨⟨g, h⟩, rfl⟩)
  · simp only [ggDepEGen, if_neg h]
    exact Submonoid.subset_closure (Or.inr rfl)

private lemma l05nD4C_word_length {p : Nat} {ha aa : List Nat} (hha : ha.length = 7)
    (haa : aa.length = 7) (w : List Nat) (q : GGDepANPair) (hq1 : q.1.length = 7)
    (hq2 : q.2.length = 7) :
    (ggDepEWord p q w ha aa).1.length = 7 ∧ (ggDepEWord p q w ha aa).2.length = 7 := by
  induction w generalizing q with
  | nil => simpa [ggDepEWord] using ⟨hq1, hq2⟩
  | cons g w ih =>
      simp only [ggDepEWord, List.foldr_cons]
      exact l05nNC_conj_length (ih q hq1 hq2).1 (ih q hq1 hq2).2
        (l05nD4C_gen_length1 hha haa g) (l05nD4C_gen_length2 hha haa g)

private lemma l05nD4C_word {p : Nat} [Fact p.Prime] (ha aa : List Nat) (hha : ha.length = 7)
    (haa : aa.length = 7) (S : Submonoid (Module.End (ZMod p) (GGDepAE p 7)))
    (hdg : ∀ g : Nat, ggDepAdot (ggDepANToZ p 7 (ggDepEGen p ha aa g).2)
      (ggDepANToZ p 7 (ggDepEGen p ha aa g).1) = 2)
    (hmem : ∀ g : Nat, ggDepARefl (ggDepANToZ p 7 (ggDepEGen p ha aa g).1)
      (ggDepANToZ p 7 (ggDepEGen p ha aa g).2) ∈ S)
    (w : List Nat) (q : GGDepANPair) (hq1 : q.1.length = 7) (hq2 : q.2.length = 7)
    (hdq : ggDepAdot (ggDepANToZ p 7 q.2) (ggDepANToZ p 7 q.1) = 2)
    (hq : ggDepARefl (ggDepANToZ p 7 q.1) (ggDepANToZ p 7 q.2) ∈ S) :
    ggDepAdot (ggDepANToZ p 7 (ggDepEWord p q w ha aa).2)
        (ggDepANToZ p 7 (ggDepEWord p q w ha aa).1) = 2 ∧
      ggDepARefl (ggDepANToZ p 7 (ggDepEWord p q w ha aa).1)
        (ggDepANToZ p 7 (ggDepEWord p q w ha aa).2) ∈ S := by
  induction w generalizing q with
  | nil => exact ⟨by simpa [ggDepEWord] using hdq, by simpa [ggDepEWord] using hq⟩
  | cons g w ih =>
      have hw : ggDepEWord p q (g :: w) ha aa =
          ggDepANConj p (ggDepEWord p q w ha aa) (ggDepEGen p ha aa g) := rfl
      rw [hw]
      have hQ1 : (ggDepEWord p q w ha aa).1.length = 7 :=
        (l05nD4C_word_length hha haa w q hq1 hq2).1
      have hQ2 : (ggDepEWord p q w ha aa).2.length = 7 :=
        (l05nD4C_word_length hha haa w q hq1 hq2).2
      have hG1 : (ggDepEGen p ha aa g).1.length = 7 := l05nD4C_gen_length1 hha haa g
      have hG2 : (ggDepEGen p ha aa g).2.length = 7 := l05nD4C_gen_length2 hha haa g
      obtain ⟨ihd, ihm⟩ := ih q hq1 hq2 hdq hq
      obtain ⟨hc1, hc2⟩ := l05nNC_toZ_conj (p := p) (N := 7)
        (q := ggDepEWord p q w ha aa) (g := ggDepEGen p ha aa g) hQ1 hQ2 hG1 hG2
      rw [hc1, hc2]
      refine ⟨l05nNC_conj_dot _ _ _ _ ihd (hdg g), ?_⟩
      rw [← l05nNC_refl_conj (ggDepANToZ p 7 (ggDepEWord p q w ha aa).1)
        (ggDepANToZ p 7 (ggDepEWord p q w ha aa).2)
        (ggDepANToZ p 7 (ggDepEGen p ha aa g).1)
        (ggDepANToZ p 7 (ggDepEGen p ha aa g).2) (hdg g)]
      exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hmem g) ihm) (hmem g)

private lemma l05nD4C_H_mem {ha : GGDepAE 3 7} (lh : List Nat) (hlh_len : lh.length = 7)
    (hlh_lt : ∀ a ∈ lh, a < 3) (hlh_toZ : ggDepANToZ 3 7 lh = ha) (c0 : Fin 6)
    (hpairs : ∀ c : Fin 6, c ≠ 0 → c ≠ 5 →
      ggDepAdot (ggDepEα 3 c) ha = (if c = c0 then (-1 : ZMod 3) else 0)) :
    lh ∈ (ggDepEAllVecs 3 7).filter (fun ha =>
      (List.range 6).all fun c =>
        c == 0 || c == 5 || ha.getD c 0 == (if c == c0.val then (3 - 1) % 3 else 0)) := by
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [← hlh_len]; exact l05nD4C_mem_allVecs lh hlh_lt
  · rw [List.all_eq_true]
    intro c hc
    rw [List.mem_range] at hc
    by_cases hc0 : c = 0
    · simp [hc0]
    · by_cases hc5 : c = 5
      · simp [hc5]
      · have hcfin0 : (⟨c, hc⟩ : Fin 6) ≠ 0 := by
          intro hh; exact hc0 (by simpa using congrArg Fin.val hh)
        have hcfin5 : (⟨c, hc⟩ : Fin 6) ≠ 5 := by
          intro hh; exact hc5 (by simpa using congrArg Fin.val hh)
        have hp := hpairs ⟨c, hc⟩ hcfin0 hcfin5
        have hdotc : ggDepAdot (ggDepEα 3 ⟨c, hc⟩) ha = (lh.getD c 0 : ZMod 3) := by
          rw [l05nD4C_dot_alpha, ← hlh_toZ]
          rfl
        rw [hdotc] at hp
        have hlt : lh.getD c 0 < 3 := by
          rw [List.getD_eq_getElem lh 0 (by rw [hlh_len]; omega)]
          exact hlh_lt _ (List.getElem_mem _)
        have hcoord : lh.getD c 0 = (if c == c0.val then 2 else 0) := by
          refine l05nD4C_zmod_eq_of_lt hlt (by split <;> omega) ?_
          rw [hp]
          by_cases hcc : c = c0.val
          · have hfin : (⟨c, hc⟩ : Fin 6) = c0 := Fin.ext hcc
            rw [if_pos hfin, if_pos (beq_iff_eq.mpr hcc)]
            decide
          · have hfin : (⟨c, hc⟩ : Fin 6) ≠ c0 := by
              intro hh; exact hcc (congrArg Fin.val hh)
            rw [if_neg hfin, if_neg (by simp [beq_iff_eq, hcc])]
            rfl
        rw [show (c == 0) = false by simp [hc0],
          show (c == 5) = false by simp [hc5], hcoord]
        simp [show (3 - 1) % 3 = 2 by norm_num]

private lemma l05nD4C_A_mem {aa : GGDepAE 3 7} (la : List Nat) (hla_len : la.length = 7)
    (hla_lt : ∀ a ∈ la, a < 3) (hla_toZ : ggDepANToZ 3 7 la = aa) (c0 : Fin 6)
    (hpairs : ∀ c : Fin 6, c ≠ 0 → c ≠ 5 →
      ggDepAdot aa (ggDepEh 3 c) = (if c = c0 then (-1 : ZMod 3) else 0)) :
    la ∈ (ggDepEAllVecs 3 7).filter (fun aa =>
      (List.range 6).all fun c =>
        c == 0 || c == 5 ||
          ggDepANDot 3 aa (ggDepEH 3 c) == (if c == c0.val then (3 - 1) % 3 else 0)) := by
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [← hla_len]; exact l05nD4C_mem_allVecs la hla_lt
  · rw [List.all_eq_true]
    intro c hc
    rw [List.mem_range] at hc
    by_cases hc0 : c = 0
    · simp [hc0]
    · by_cases hc5 : c = 5
      · simp [hc5]
      · have hcfin0 : (⟨c, hc⟩ : Fin 6) ≠ 0 := by
          intro hh; exact hc0 (by simpa using congrArg Fin.val hh)
        have hcfin5 : (⟨c, hc⟩ : Fin 6) ≠ 5 := by
          intro hh; exact hc5 (by simpa using congrArg Fin.val hh)
        have hp := hpairs ⟨c, hc⟩ hcfin0 hcfin5
        have hdotc : (ggDepANDot 3 la (ggDepEH 3 c) : ZMod 3) =
            ggDepAdot aa (ggDepEh 3 ⟨c, hc⟩) := by
          rw [ggDepANDot_cast (p := 3) (N := 7) la (ggDepEH 3 c) hla_len
            (by simp [ggDepEH])]
          rw [hla_toZ, l05nD4C_toZ_EH c hc]
        have hcoord : ggDepANDot 3 la (ggDepEH 3 c) =
            (if c == c0.val then 2 else 0) := by
          refine l05nD4C_zmod_eq_of_lt (by rw [ggDepANDot]; exact Nat.mod_lt _ (by omega))
            (by split <;> omega) ?_
          rw [hdotc, hp]
          by_cases hcc : c = c0.val
          · have hfin : (⟨c, hc⟩ : Fin 6) = c0 := Fin.ext hcc
            rw [if_pos hfin, if_pos (beq_iff_eq.mpr hcc)]
            decide
          · have hfin : (⟨c, hc⟩ : Fin 6) ≠ c0 := by
              intro hh; exact hcc (congrArg Fin.val hh)
            rw [if_neg hfin, if_neg (by simp [beq_iff_eq, hcc])]
            rfl
        rw [show (c == 0) = false by simp [hc0],
          show (c == 5) = false by simp [hc5], hcoord]
        simp [show (3 - 1) % 3 = 2 by norm_num]

private lemma l05nD4C_cases_apply (p c0 : Nat) (wits : List GGDepANWit) (ha aa : List Nat)
    (hha : ha ∈ (ggDepEAllVecs p 7).filter (fun ha =>
      (List.range 6).all fun c =>
        c == 0 || c == 5 || ha.getD c 0 == (if c == c0 then (p - 1) % p else 0)))
    (haa : aa ∈ (ggDepEAllVecs p 7).filter (fun aa =>
      (List.range 6).all fun c =>
        c == 0 || c == 5 ||
          ggDepANDot p aa (ggDepEH p c) == (if c == c0 then (p - 1) % p else 0)))
    (h : ggDepED4Cases p c0 wits = true)
    (hcond : (ggDepANDot p aa ha == 2 % p && aa.getD 6 0 % p != 0) = true) :
    wits.any (fun w => ggDepEWitTest p w ha aa) = true := by
  simp only [ggDepED4Cases] at h
  have h1 := List.all_eq_true.mp h ha hha
  have h2 := List.all_eq_true.mp h1 aa haa
  rwa [if_pos hcond] at h2

private theorem l05nD4C_witTest_sound (w : GGDepANWit) (hw : ggDepANWitValid 7 w = true)
    (ha aa : List Nat) (hha : ha.length = 7) (haa : aa.length = 7)
    (hdot : ggDepANDot 3 aa ha = 2 % 3) (ht : ggDepEWitTest 3 w ha aa = true) :
    ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin 6 =>
        ggDepARefl (ggDepEh 3 i) (ggDepEα 3 i)) ∪
        {ggDepARefl (ggDepANToZ 3 7 ha) (ggDepANToZ 3 7 aa)}), GGDepAIsTv g := by
  set S : Submonoid (Module.End (ZMod 3) (GGDepAE 3 7)) :=
    Submonoid.closure (Set.range (fun i : Fin 6 =>
      ggDepARefl (ggDepEh 3 i) (ggDepEα 3 i)) ∪
      {ggDepARefl (ggDepANToZ 3 7 ha) (ggDepANToZ 3 7 aa)}) with hSdef
  have hdg : ∀ g : Nat, ggDepAdot (ggDepANToZ 3 7 (ggDepEGen 3 ha aa g).2)
      (ggDepANToZ 3 7 (ggDepEGen 3 ha aa g).1) = 2 := fun g => l05nD4C_gen_dot hha haa hdot g
  have hmem : ∀ g : Nat, ggDepARefl (ggDepANToZ 3 7 (ggDepEGen 3 ha aa g).1)
      (ggDepANToZ 3 7 (ggDepEGen 3 ha aa g).2) ∈ S := by
    intro g; rw [hSdef]; exact l05nD4C_gen_mem g
  set q1 : GGDepANPair := ggDepEWord 3 (ggDepEGen 3 ha aa w.g1) w.w1 ha aa with hq1def
  set q2 : GGDepANPair := ggDepEWord 3 (ggDepEGen 3 ha aa w.g2) w.w2 ha aa with hq2def
  have hL1 : q1.1.length = 7 :=
    (l05nD4C_word_length hha haa w.w1 (ggDepEGen 3 ha aa w.g1)
      (l05nD4C_gen_length1 hha haa w.g1) (l05nD4C_gen_length2 hha haa w.g1)).1
  have hL2 : q1.2.length = 7 :=
    (l05nD4C_word_length hha haa w.w1 (ggDepEGen 3 ha aa w.g1)
      (l05nD4C_gen_length1 hha haa w.g1) (l05nD4C_gen_length2 hha haa w.g1)).2
  have hL3 : q2.1.length = 7 :=
    (l05nD4C_word_length hha haa w.w2 (ggDepEGen 3 ha aa w.g2)
      (l05nD4C_gen_length1 hha haa w.g2) (l05nD4C_gen_length2 hha haa w.g2)).1
  have hL4 : q2.2.length = 7 :=
    (l05nD4C_word_length hha haa w.w2 (ggDepEGen 3 ha aa w.g2)
      (l05nD4C_gen_length1 hha haa w.g2) (l05nD4C_gen_length2 hha haa w.g2)).2
  have hword1 : ggDepAdot (ggDepANToZ 3 7 q1.2) (ggDepANToZ 3 7 q1.1) = 2 ∧
      ggDepARefl (ggDepANToZ 3 7 q1.1) (ggDepANToZ 3 7 q1.2) ∈ S := by
    rw [hq1def]
    exact l05nD4C_word ha aa hha haa S hdg hmem w.w1 (ggDepEGen 3 ha aa w.g1)
      (l05nD4C_gen_length1 hha haa w.g1) (l05nD4C_gen_length2 hha haa w.g1) (hdg w.g1) (hmem w.g1)
  have hword2 : ggDepAdot (ggDepANToZ 3 7 q2.2) (ggDepANToZ 3 7 q2.1) = 2 ∧
      ggDepARefl (ggDepANToZ 3 7 q2.1) (ggDepANToZ 3 7 q2.2) ∈ S := by
    rw [hq2def]
    exact l05nD4C_word ha aa hha haa S hdg hmem w.w2 (ggDepEGen 3 ha aa w.g2)
      (l05nD4C_gen_length1 hha haa w.g2) (l05nD4C_gen_length2 hha haa w.g2) (hdg w.g2) (hmem w.g2)
  have hdot1 : ggDepANDot 3 q1.2 q1.1 = 2 % 3 := by
    have h := ggDepANDot_cast (p := 3) (N := 7) q1.2 q1.1 hL2 hL1
    rw [hword1.1] at h
    have h2 : ((ggDepANDot 3 q1.2 q1.1 : Nat) : ZMod 3) = ((2 % 3 : Nat) : ZMod 3) := by
      rw [ZMod.natCast_mod]; exact h
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    simpa [ggDepANDot, Nat.mod_mod] using h2
  have hdot2 : ggDepANDot 3 q2.2 q2.1 = 2 % 3 := by
    have h := ggDepANDot_cast (p := 3) (N := 7) q2.2 q2.1 hL4 hL3
    rw [hword2.1] at h
    have h2 : ((ggDepANDot 3 q2.2 q2.1 : Nat) : ZMod 3) = ((2 % 3 : Nat) : ZMod 3) := by
      rw [ZMod.natCast_mod]; exact h
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    simpa [ggDepANDot, Nat.mod_mod] using h2
  have ht' : ggDepANTestPair 3 q1 q2 = true := by
    rw [hq1def, hq2def]; simpa only [ggDepEWitTest] using ht
  have htv := ggDepANTestPair_sound (p := 3) (N := 7) (by norm_num) q1 q2 hL1 hL2 hL3 hL4
    hdot1 hdot2 ht'
  have hfin : ggDepARefl (ggDepANToZ 3 7 q1.1) (ggDepANToZ 3 7 q1.2) *
      ggDepARefl (ggDepANToZ 3 7 q2.1) (ggDepANToZ 3 7 q2.2) ∈ S :=
    Submonoid.mul_mem _ hword1.2 hword2.2
  rw [hSdef] at hfin
  exact ⟨_, hfin, htv.2.2⟩

private theorem l05nD4C_check : ggDepED4Check ggDepED4Data = true := by decide +kernel

private theorem l05nD4C_sound (data : List (Nat × List GGDepANWit))
    (h : ggDepED4Check data = true) : GGDepED4Cells1 := by
  intro c0 hleaf ha αa hpairs hdot2 hx
  rw [ggDepED4Check, Bool.and_eq_true] at h
  obtain ⟨hvalid, hcheck⟩ := h
  have hc0_mem : c0.val ∈ [1, 2, 4] := by
    rcases hleaf with h1 | h2 | h4
    · rw [h1]; simp
    · rw [h2]; simp
    · rw [h4]; simp
  have h1 := List.all_eq_true.mp hcheck c0.val hc0_mem
  cases hlook : data.lookup c0.val with
  | none => rw [hlook] at h1; simp at h1
  | some wits =>
    rw [hlook] at h1
    obtain ⟨l₁, l₂, hdata, -⟩ := List.lookup_eq_some_iff.mp hlook
    subst hdata
    have hentry : ((c0.val, wits) : Nat × List GGDepANWit) ∈
        l₁ ++ ((c0.val, wits) : Nat × List GGDepANWit) :: l₂ := by simp
    obtain ⟨lh, -, hlh_len, hlh_lt, hlh_toZ⟩ := l05nD4C_allVecs_three 7 ha
    obtain ⟨la, -, hla_len, hla_lt, hla_toZ⟩ := l05nD4C_allVecs_three 7 αa
    have hpairsH : ∀ c : Fin 6, c ≠ 0 → c ≠ 5 →
        ggDepAdot (ggDepEα 3 c) ha = (if c = c0 then (-1 : ZMod 3) else 0) :=
      fun c h0 h5 => (hpairs c ⟨h0, h5⟩).2
    have hpairsA : ∀ c : Fin 6, c ≠ 0 → c ≠ 5 →
        ggDepAdot αa (ggDepEh 3 c) = (if c = c0 then (-1 : ZMod 3) else 0) :=
      fun c h0 h5 => (hpairs c ⟨h0, h5⟩).1
    have hHa_filter := l05nD4C_H_mem lh hlh_len hlh_lt hlh_toZ c0 hpairsH
    have hAa_filter := l05nD4C_A_mem la hla_len hla_lt hla_toZ c0 hpairsA
    have hdotN : ggDepANDot 3 la lh = 2 % 3 := by
      have hcast := ggDepANDot_cast (p := 3) (N := 7) la lh hla_len hlh_len
      rw [hla_toZ, hlh_toZ] at hcast
      rw [hdot2] at hcast
      have h2 : ((ggDepANDot 3 la lh : Nat) : ZMod 3) = ((2 % 3 : Nat) : ZMod 3) := by
        rw [ZMod.natCast_mod]; exact hcast
      rw [ZMod.natCast_eq_natCast_iff'] at h2
      simpa [ggDepANDot, Nat.mod_mod] using h2
    have hxval : ggDepAdot αa (ggDepEx 3) = (la.getD 6 0 : ZMod 3) := by
      rw [← hla_toZ, l05nD4C_dot_ex]
      rfl
    have hv0 : la.getD 6 0 % 3 ≠ 0 := by
      intro hz
      have hzero : (la.getD 6 0 : ZMod 3) = 0 := by
        rw [← ZMod.natCast_mod (la.getD 6 0) 3, hz]; simp
      exact hx (by rw [hxval, hzero])
    have hcond : (ggDepANDot 3 la lh == 2 % 3 && la.getD 6 0 % 3 != 0) = true := by
      rw [Bool.and_eq_true]
      exact ⟨beq_iff_eq.mpr hdotN, bne_iff_ne.mpr hv0⟩
    obtain ⟨w, hwmem, hwtest⟩ := List.any_eq_true.mp
      (l05nD4C_cases_apply 3 c0.val wits lh la hHa_filter hAa_filter h1 hcond)
    have hwvalid : ggDepANWitValid 7 w = true :=
      List.all_eq_true.mp
        (List.all_eq_true.mp hvalid ((c0.val, wits) : Nat × List GGDepANWit) hentry) w hwmem
    obtain ⟨g, hgmem, hgtv⟩ := l05nD4C_witTest_sound w hwvalid lh la hlh_len hla_len hdotN hwtest
    refine ⟨g, ?_, hgtv⟩
    rw [hlh_toZ, hla_toZ] at hgmem
    exact hgmem

theorem ggDepED4_cells1 : GGDepED4Cells1 := l05nD4C_sound ggDepED4Data l05nD4C_check

end CFSG.StandardType

end
