module

public import CFSG.LocalAnalysis.StandardType.GGDepELLowCheck1

public section

namespace CFSG.StandardType

open Certificates.DepED4Low Certificates.TwoDepSmall Certificates.DepASmall
  Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nK2_check_two (d : DepELData) (h : ggDepELCheck d = true) (c c' : Fin 6)
    (hc : GGDepED4Leaf c) (hc' : GGDepED4Leaf c') (hne : c ≠ c') :
    ∃ wits, d.two.lookup (c.val, c'.val) = some wits ∧
      (∀ w ∈ wits, ggDepELTvValid 8 w = true) ∧
      ggDepELCases2 c.val c'.val wits ((d.excTwo.lookup (c.val, c'.val)).getD []) = true := by
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have h3 := Bool.and_eq_true_iff.mp h2.1
  have htwo : d.two.all (fun e => e.2.all (ggDepELTvValid 8)) = true := h3.2
  have hleaves : ggDepELNLeaves.all (fun c => ggDepELNLeaves.all fun c' =>
      if c != c' then
        match d.two.lookup (c, c') with
        | none => false
        | some wits => ggDepELCases2 c c' wits ((d.excTwo.lookup (c, c')).getD [])
      else true) = true := h1.2
  have hc_mem : c.val ∈ ggDepELNLeaves := (ggDepELNLeaves_iff c).mpr hc
  have hc'_mem : c'.val ∈ ggDepELNLeaves := (ggDepELNLeaves_iff c').mpr hc'
  have hinner := List.all_eq_true.mp hleaves c.val hc_mem
  have hpair := List.all_eq_true.mp hinner c'.val hc'_mem
  have hne' : (c.val != c'.val) = true := by
    rw [bne_iff_ne]
    exact fun hh => hne (Fin.ext hh)
  rw [if_pos hne'] at hpair
  cases hlook : d.two.lookup (c.val, c'.val) with
  | none => rw [hlook] at hpair; simp at hpair
  | some wits =>
      rw [hlook] at hpair
      obtain ⟨l1, l2, hdata, -⟩ := List.lookup_eq_some_iff.mp hlook
      have hentry : ((c.val, c'.val), wits) ∈ d.two := by
        rw [hdata]; simp
      have hwv : ∀ w ∈ wits, ggDepELTvValid 8 w = true := by
        intro w hw
        exact List.all_eq_true.mp
          (List.all_eq_true.mp htwo (((c.val, c'.val), wits)) hentry) w hw
      exact ⟨wits, rfl, hwv, hpair⟩

private theorem l05nK2_cases2_extract (c c' : ℕ) (wits : List GGDepANWit)
    (exc : List ((List ℕ × List ℕ × List ℕ × List ℕ) × GGDepELReason))
    (h : ggDepELCases2 c c' wits exc = true)
    {lh1 la1 lh2 la2 : List ℕ}
    (hlh1 : lh1 ∈ ggDepELSolH (fun d => if d = c then 2 else 0))
    (hla1 : la1 ∈ ggDepELSolA (fun d => if d = c then 2 else 0))
    (hlh2 : lh2 ∈ ggDepELSolH (fun d => if d = c' then 2 else 0))
    (hla2 : la2 ∈ ggDepELSolA (fun d => if d = c' then 2 else 0))
    (hd1 : ggDepANDot 3 la1 lh1 = 2)
    (hd2 : ggDepANDot 3 la1 lh2 = 0)
    (hd3 : ggDepANDot 3 la2 lh2 = 2)
    (hd4 : ggDepANDot 3 la2 lh1 = 0)
    (hx : ggDepANDot 3 la1 ggDepELNX ≠ 0 ∨ ggDepANDot 3 la2 ggDepELNX ≠ 0)
    (hdet : (ggDepANDot 3 la1 ggDepELNX * ggDepANDot 3 la2 ggDepELNZ) % 3 =
      (ggDepANDot 3 la1 ggDepELNZ * ggDepANDot 3 la2 ggDepELNX) % 3) :
    (∃ w ∈ wits, ggDepELTvTest [(lh1, la1), (lh2, la2)] w = true) ∨
      (∃ e ∈ exc, ggTWLVecEq 3 e.1.1 lh1 = true ∧ ggTWLVecEq 3 e.1.2.1 la1 = true ∧
        ggTWLVecEq 3 e.1.2.2.1 lh2 = true ∧ ggTWLVecEq 3 e.1.2.2.2 la2 = true ∧
        ggDepELReasonTest [(lh1, la1), (lh2, la2)] e.2 = true) := by
  simp only [ggDepELCases2] at h
  have e1 := List.all_eq_true.mp h lh1 hlh1
  have e2 := List.all_eq_true.mp e1 la1 hla1
  rw [if_pos (beq_iff_eq.mpr hd1)] at e2
  have e3 := List.all_eq_true.mp e2 lh2 hlh2
  rw [if_pos (beq_iff_eq.mpr hd2)] at e3
  have e4 := List.all_eq_true.mp e3 la2 hla2
  have hor : (ggDepANDot 3 la1 ggDepELNX != 0 || ggDepANDot 3 la2 ggDepELNX != 0) = true := by
    rw [Bool.or_eq_true_iff]
    exact hx.imp (fun h => bne_iff_ne.mpr h) (fun h => bne_iff_ne.mpr h)
  have hcond : (ggDepANDot 3 la2 lh2 == 2 && ggDepANDot 3 la2 lh1 == 0 &&
      (ggDepANDot 3 la1 ggDepELNX != 0 || ggDepANDot 3 la2 ggDepELNX != 0) &&
      (ggDepANDot 3 la1 ggDepELNX * ggDepANDot 3 la2 ggDepELNZ) % 3 ==
        (ggDepANDot 3 la1 ggDepELNZ * ggDepANDot 3 la2 ggDepELNX) % 3) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨⟨beq_iff_eq.mpr hd3, beq_iff_eq.mpr hd4⟩, hor⟩, beq_iff_eq.mpr hdet⟩
  rw [if_pos hcond] at e4
  cases hfind : exc.find? (fun e => ggTWLVecEq 3 e.1.1 lh1 && ggTWLVecEq 3 e.1.2.1 la1 &&
      ggTWLVecEq 3 e.1.2.2.1 lh2 && ggTWLVecEq 3 e.1.2.2.2 la2) with
  | none => rw [hfind] at e4; exact Or.inl (List.any_eq_true.mp e4)
  | some e =>
      rw [hfind] at e4
      have hmem : e ∈ exc := List.mem_of_find?_eq_some hfind
      have hpred := List.find?_some (p := fun e => ggTWLVecEq 3 e.1.1 lh1 &&
        ggTWLVecEq 3 e.1.2.1 la1 && ggTWLVecEq 3 e.1.2.2.1 lh2 &&
        ggTWLVecEq 3 e.1.2.2.2 la2) (a := e) hfind
      simp only [Bool.and_eq_true] at hpred
      exact Or.inr ⟨e, hmem, hpred.1.1.1, hpred.1.1.2, hpred.1.2, hpred.2, e4⟩

theorem ggDepELNotSurv2 (d : DepELData) (h : ggDepELCheck d = true)
    (hpzOnly : ∀ k : ℕ × ℕ, ∀ e ∈ (d.excTwo.lookup k).getD [],
      ∃ w, e.2 = GGDepELReason.pz w) :
    ¬ GGDepED4LowSurv2 := by
  rintro ⟨c, c', ha1, αa1, ha2, αa2, lam, mu, hc, hc', hne, hP, hx, hlm, h1, h2, htv, hpz⟩
  obtain ⟨wits, _hlook, hwv, hcases⟩ := l05nK2_check_two d h c c' hc hc' hne
  obtain ⟨lh1, la1, lh2, la2, hlh1, hla1, hlh2, hla2, hd1, hd2, hd3, hd4, hx_list, hdet,
    hvalid_pair1, hvalid_pair2, hnews_eq⟩ :=
    ggDepELEnc2 c c' hc hc' ha1 αa1 ha2 αa2 hP hx lam mu hlm h1 h2
  have hvalid : ∀ q ∈ [(lh1, la1), (lh2, la2)], GGDepELNValid q := by
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq; exact hvalid_pair1
    · rcases List.mem_cons.mp hq with hq | hq
      · subst hq; exact hvalid_pair2
      · simp at hq
  have hla1mem : (ggDepELToZ lh1, ggDepELToZ la1) ∈
      ggDepELNNews [(lh1, la1), (lh2, la2)] :=
    ⟨(lh1, la1), by simp, rfl⟩
  rw [hnews_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hla1mem
  have hla2mem : (ggDepELToZ lh2, ggDepELToZ la2) ∈
      ggDepELNNews [(lh1, la1), (lh2, la2)] :=
    ⟨(lh2, la2), by simp, rfl⟩
  rw [hnews_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hla2mem
  have hfix' : ∀ q ∈ [(lh1, la1), (lh2, la2)],
      ggDepAdot (ggDepELToZ q.2) (lam • ggDepELx + mu • ggDepELz) = 0 := by
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq
      change ggDepAdot (ggDepELToZ la1) (lam • ggDepELx + mu • ggDepELz) = 0
      rcases hla1mem with he | he
      · have hla : ggDepELToZ la1 = αa1 := by simpa using congrArg Prod.snd he
        rw [hla]; exact h1
      · have hla : ggDepELToZ la1 = αa2 := by simpa using congrArg Prod.snd he
        rw [hla]; exact h2
    · rcases List.mem_cons.mp hq with hq | hq
      · subst hq
        change ggDepAdot (ggDepELToZ la2) (lam • ggDepELx + mu • ggDepELz) = 0
        rcases hla2mem with he | he
        · have hla : ggDepELToZ la2 = αa1 := by simpa using congrArg Prod.snd he
          rw [hla]; exact h1
        · have hla : ggDepELToZ la2 = αa2 := by simpa using congrArg Prod.snd he
          rw [hla]; exact h2
      · simp at hq
  have hx' : ∃ q ∈ [(lh1, la1), (lh2, la2)],
      ggDepAdot (ggDepELToZ q.2) ggDepELx ≠ 0 := by
    rcases hx with hx1 | hx2
    · have hmem : (ha1, αa1) ∈ ggDepELNNews [(lh1, la1), (lh2, la2)] := by
        rw [hnews_eq]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      rcases hmem with ⟨q, hq, hqeq⟩
      have hla : ggDepELToZ q.2 = αa1 := by
        simpa using (congrArg Prod.snd hqeq).symm
      exact ⟨q, hq, by rw [hla]; exact hx1⟩
    · have hmem : (ha2, αa2) ∈ ggDepELNNews [(lh1, la1), (lh2, la2)] := by
        rw [hnews_eq]
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
      rcases hmem with ⟨q, hq, hqeq⟩
      have hla : ggDepELToZ q.2 = αa2 := by
        simpa using (congrArg Prod.snd hqeq).symm
      exact ⟨q, hq, by rw [hla]; exact hx2⟩
  obtain hwit | hexc := l05nK2_cases2_extract c.val c'.val wits
    ((d.excTwo.lookup (c.val, c'.val)).getD []) hcases
    hlh1 hla1 hlh2 hla2 hd1 hd2 hd3 hd4 hx_list hdet
  · obtain ⟨w, hwmem, hwtest⟩ := hwit
    have hkill := ggDepELTv_sound hvalid w (hwv w hwmem) hwtest
    rw [hnews_eq] at hkill
    exact htv hkill
  · obtain ⟨e, hemem, _hp1, _hp2, _hp3, _hp4, hrt⟩ := hexc
    obtain ⟨w, hw⟩ := hpzOnly (c.val, c'.val) e hemem
    rw [hw] at hrt
    obtain ⟨hY0len, t, ht, heq⟩ := ggDepELY0_line hvalid lam mu hlm hfix' hx'
    have htest : ggDepELPZTest [(lh1, la1), (lh2, la2)]
        (ggDepELY0 [(lh1, la1), (lh2, la2)]) w = true := hrt
    obtain ⟨hc0z, hpz0⟩ := ggDepELPZTest_sound hvalid
      (ggDepELY0 [(lh1, la1), (lh2, la2)]) hY0len w htest
    rw [hnews_eq] at hpz0
    have hcne : (w.c0 : ZMod 3) * t⁻¹ ≠ 0 := mul_ne_zero hc0z (inv_ne_zero ht)
    have harg : ggDepELx + (w.c0 : ZMod 3) •
          ggDepELToZ (ggDepELY0 [(lh1, la1), (lh2, la2)]) =
        ggDepELx + ((w.c0 : ZMod 3) * t⁻¹) •
          (lam • ggDepELx + mu • ggDepELz) := by
      have htoz : ggDepELToZ (ggDepELY0 [(lh1, la1), (lh2, la2)]) =
          t⁻¹ • (lam • ggDepELx + mu • ggDepELz) := by
        rw [heq, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [htoz, smul_smul]
    rw [harg] at hpz0
    exact hpz ((w.c0 : ZMod 3) * t⁻¹) hcne hpz0

theorem ggDepELCheck_sound (d : DepELData) (h : ggDepELCheck d = true)
    (hpzOnly : ∀ k : ℕ × ℕ, ∀ e ∈ (d.excTwo.lookup k).getD [],
      ∃ w, e.2 = GGDepELReason.pz w) :
    GGDepED4LowCells :=
  ⟨ggDepELNotSurv1 d h, ggDepELNotSurv2 d h hpzOnly⟩

end CFSG.StandardType

end
