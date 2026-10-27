module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4OverFlag

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates
open scoped Pointwise

set_option linter.unusedSectionVars false


section Stabilizer

@[expose] noncomputable def flag0 : Flag := flagEquiv 0

theorem flag0_fst : flag0.1.1 = pt0 := by
  apply Fin.ext
  have := lnPt_zero.1
  simpa [flag0, flagEquiv_apply, flagOf, pt0] using this

theorem flag0_snd : flag0.1.2 = (0 : Fin 2457) := by
  apply Fin.ext
  simp [flag0, flagEquiv_apply, flagOf]

theorem smul_line_zero_iff (g : D) : g • line0 = line0 ↔ g • (0 : Fin 2457) = 0 := by
  rw [smul_line0, ← lineSet_zero, ← lineSet_smul, lineSet_injective.eq_iff]

theorem smul_flag0_iff (g : D) : g • flag0 = flag0 ↔ g ∈ d4B := by
  rw [mem_d4B_iff, smul_line_zero_iff]
  constructor
  · intro h
    have h1 := congrArg (fun x : Flag => x.1.1) h
    have h2 := congrArg (fun x : Flag => x.1.2) h
    simp only [smul_flag_fst, smul_flag_snd, flag0_fst, flag0_snd] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    apply Prod.ext
    · show g • flag0.1.1 = flag0.1.1
      rw [flag0_fst]
      exact h1
    · show g • flag0.1.2 = flag0.1.2
      rw [flag0_snd]
      exact h2

end Stabilizer


section Transitive

theorem exists_smul_flag0_eq (u : Flag) : ∃ g : D, g • flag0 = u := by
  obtain ⟨hF1, -, hF3, -⟩ := ovFlag_parts
  have hrep : ∀ i < flagArrs.size, Rep 7371 flagArrs[i]! (flagAct (d4GenG i)) :=
    fun i hi => flagAct_gen (by rw [hF1] at hi; exact hi)
  have := pretransitive_of_orbitLabelOK (gs := fun i => flagAct (d4GenG i)) hF3 hrep
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq
    (genGroup flagArrs fun i => flagAct (d4GenG i)) (0 : Fin 7371) (flagEquiv.symm u)
  have hle : genGroup flagArrs (fun i => flagAct (d4GenG i)) ≤
      (flagAct : D →* Equiv.Perm (Fin 7371)).range := by
    rw [genGroup, Subgroup.closure_le]
    rintro _ ⟨i, -, rfl⟩
    exact ⟨d4GenG i, rfl⟩
  obtain ⟨g, hg⟩ := hle h.2
  refine ⟨g, ?_⟩
  have h0 : flagAct g 0 = flagEquiv.symm u := by
    rw [hg]
    exact hh
  have := flagEquiv_flagAct g 0
  rw [h0, Equiv.apply_symm_apply] at this
  exact this.symm

end Transitive

section BGens

theorem d4Zeta_mem_B : d4Zeta ∈ d4B := by
  obtain ⟨h0, h1, -⟩ := ovZeta_parts
  have hr : Rep 819 (ptWordArr [3, 2, 4, 2]) (act d4Zeta) := rep_ptWordArr (by decide)
  exact ⟨mem_d4H_of_rep hr h0, mem_d4N_of_rep hr h1⟩

@[expose] noncomputable def bGen (i : ℕ) : D :=
  [d4GenG 0, d4GenG 1, d4GenG 2, d4GenG 6, d4Zeta].getD i 1

theorem bGen_mem_B {i : ℕ} (hi : i < 5) : bGen i ∈ d4B := by
  interval_cases i
  · exact gen_mem_B (j := 0) (Or.inl rfl)
  · exact gen_mem_B (j := 1) (Or.inr (Or.inl rfl))
  · exact gen_mem_B (j := 2) (Or.inr (Or.inr (Or.inl rfl)))
  · exact gen_mem_B (j := 6) (Or.inr (Or.inr (Or.inr rfl)))
  · exact d4Zeta_mem_B

theorem bFlagArrs_get0 : bFlagArrs[0]! = flagArrs[0]! := by simp [bFlagArrs]

theorem bFlagArrs_get1 : bFlagArrs[1]! = flagArrs[1]! := by simp [bFlagArrs]

theorem bFlagArrs_get2 : bFlagArrs[2]! = flagArrs[2]! := by simp [bFlagArrs]

theorem bFlagArrs_get3 : bFlagArrs[3]! = flagArrs[6]! := by simp [bFlagArrs]

theorem bFlagArrs_get4 : bFlagArrs[4]! = flagWordArr [3, 2, 4, 2] := by simp [bFlagArrs]

theorem bFlag_rep : ∀ i < bFlagArrs.size, Rep 7371 bFlagArrs[i]! (flagAct (bGen i)) := by
  intro i hi
  have h5 : bFlagArrs.size = 5 := ovFlag_parts.2.1
  rw [h5] at hi
  interval_cases i
  · rw [bFlagArrs_get0]
    exact flagAct_gen (j := 0) (by norm_num)
  · rw [bFlagArrs_get1]
    exact flagAct_gen (j := 1) (by norm_num)
  · rw [bFlagArrs_get2]
    exact flagAct_gen (j := 2) (by norm_num)
  · rw [bFlagArrs_get3]
    exact flagAct_gen (j := 6) (by norm_num)
  · rw [bFlagArrs_get4]
    exact rep_flagWordArr [3, 2, 4, 2] (by decide)

theorem genGroup_bFlag_le :
    genGroup bFlagArrs (fun i => flagAct (bGen i)) ≤ d4B.map flagAct := by
  rw [genGroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  have h5 : bFlagArrs.size = 5 := ovFlag_parts.2.1
  exact ⟨bGen i, bGen_mem_B (by simpa [h5] using hi), rfl⟩

@[expose] def ovRep (k : ℕ) : Fin 7371 := finPt 7371 ovReps[k]!

theorem ovRep_val {k : ℕ} (hk : k < 12) : ((ovRep k : Fin 7371) : ℕ) = ovReps[k]! := by
  obtain ⟨-, -, -, -, -, -, -, hF8, -⟩ := ovFlag_parts
  have := ((orbitLabelOK_parts hF8).2.2.1 k hk).1
  simp only [List.getElem!_toArray] at this
  exact finPt_val this

theorem ovB_orbit {k : ℕ} (hk : k < 12) {c : Fin 7371} (hc : ovBForest.1[(c : ℕ)]! = k) :
    ∃ s ∈ d4B, s • flagEquiv (ovRep k) = flagEquiv c := by
  obtain ⟨-, -, -, -, -, -, -, hF8, -⟩ := ovFlag_parts
  have h := orbit_eq_label hF8 (gs := fun i => flagAct (bGen i)) bFlag_rep hk
  have hc' : c ∈ {x : Fin 7371 | ovBForest.1[(x : ℕ)]! = k} := hc
  rw [← h] at hc'
  obtain ⟨⟨g, hg⟩, hgc⟩ := hc'
  obtain ⟨s, hs, rfl⟩ := genGroup_bFlag_le hg
  refine ⟨s, hs, ?_⟩
  have e : ovRep k = (⟨(ovReps.toArray)[k]! % 7371, by
      have := ((orbitLabelOK_parts hF8).2.2.1 k hk).1
      omega⟩ : Fin 7371) := by
    apply Fin.ext
    simp [ovRep, finPt]
  rw [← flagEquiv_flagAct, e]
  congr 1

end BGens

section Over

theorem ovRep_zero : ovRep 0 = 0 := by
  obtain ⟨-, -, -, -, h5, -⟩ := ovFlag_parts
  exact Fin.ext (by rw [ovRep_val (by norm_num), h5]; rfl)

theorem ovRep_one : ovRep 1 = 1 := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := ovFlag_parts
  exact Fin.ext (by rw [ovRep_val (by norm_num), h6]; rfl)

theorem ovRep_two : ovRep 2 = 3 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := ovFlag_parts
  exact Fin.ext (by rw [ovRep_val (by norm_num), h7]; rfl)

theorem flagEquiv_ovRep_zero : flagEquiv (ovRep 0) = flag0 := by rw [ovRep_zero]; rfl

@[expose] def overRel (X : Subgroup D) (u v : Flag) : Prop :=
  ∃ g h : D, g • flag0 = u ∧ h • flag0 = v ∧ g⁻¹ * h ∈ X

theorem overRel_equiv {X : Subgroup D} (hX : d4B ≤ X) : Equivalence (overRel X) := by
  refine ⟨fun u => ?_, fun ⟨g, h, hg, hh, hgh⟩ => ⟨h, g, hh, hg, ?_⟩, ?_⟩
  · obtain ⟨g, hg⟩ := exists_smul_flag0_eq u
    exact ⟨g, g, hg, hg, by simp⟩
  · simpa using X.inv_mem hgh
  · rintro u v w ⟨g, h, hg, hh, hgh⟩ ⟨h', k, hh', hk, hh'k⟩
    have hs : h⁻¹ * h' ∈ d4B := by
      rw [← smul_flag0_iff, mul_smul, hh', ← hh, inv_smul_smul]
    refine ⟨g, k, hg, hk, ?_⟩
    have := X.mul_mem (X.mul_mem hgh (hX hs)) hh'k
    simpa [mul_assoc] using this

theorem overRel_inv (X : Subgroup D) (a : D) {u v : Flag} (h : overRel X u v) :
    overRel X (a • u) (a • v) := by
  obtain ⟨g, h, hg, hh, hgh⟩ := h
  refine ⟨a * g, a * h, ?_, ?_, ?_⟩
  · rw [mul_smul, hg]
  · rw [mul_smul, hh]
  · simpa [mul_assoc] using hgh

theorem overRel_base {X : Subgroup D} (hX : d4B ≤ X) {n : D} (h : overRel X flag0 (n • flag0)) :
    n ∈ X := by
  obtain ⟨g, k, hg, hk, hgk⟩ := h
  have hgS : g ∈ d4B := (smul_flag0_iff g).1 hg
  have hkX : k ∈ X := by
    have := X.mul_mem (hX hgS) hgk
    simpa using this
  have hnk : k⁻¹ * n ∈ d4B := by
    rw [← smul_flag0_iff, mul_smul, ← hk, inv_smul_smul]
  have := X.mul_mem hkX (hX hnk)
  simpa using this

theorem overRel_of_mem {X : Subgroup D} {x : D} (hx : x ∈ X) : overRel X flag0 (x • flag0) :=
  ⟨1, x, by simp, rfl, by simpa using hx⟩

theorem overRel_smul_B {X : Subgroup D} {s : D} (hs : s ∈ d4B) {u : Flag}
    (h : overRel X flag0 u) : overRel X flag0 (s • u) := by
  have := overRel_inv X s h
  rwa [(smul_flag0_iff s).2 hs] at this

theorem overRel_orbit {X : Subgroup D} {k : ℕ} (hk : k < 12) {c : Fin 7371}
    (hc : ovBForest.1[(c : ℕ)]! = k) (h : overRel X flag0 (flagEquiv (ovRep k))) :
    overRel X flag0 (flagEquiv c) := by
  obtain ⟨s, hs, hsc⟩ := ovB_orbit hk hc
  rw [← hsc]
  exact overRel_smul_B hs h

end Over

section Lattice

theorem d4H_le_of_rel {X : Subgroup D} (hX : d4B ≤ X)
    (h : overRel X flag0 (flagEquiv (ovRep 2))) : d4H ≤ X := by
  obtain ⟨-, -, -, -, -, -, -, hF8, hF9, hF10, -⟩ := ovFlag_parts
  intro n hn
  apply overRel_base hX
  have hpt : (n • flag0).1.1 = pt0 := by
    show n • flag0.1.1 = pt0
    rw [flag0_fst]
    exact (mem_d4H_iff n).1 hn
  set c : Fin 7371 := flagEquiv.symm (n • flag0) with hc
  have hcu : flagEquiv c = n • flag0 := by rw [hc, Equiv.apply_symm_apply]
  have hcpt : lnPt (c.val / 3) (c.val % 3) = 0 := by
    have h1 : (flagEquiv c).1.1 = pt0 := by rw [hcu]; exact hpt
    have h2 := congrArg Fin.val h1
    simpa [flagEquiv_apply, flagOf, pt0] using h2
  rcases hF10 c.val c.2 hcpt with h0 | h2
  · obtain ⟨s, hs, hsc⟩ := ovB_orbit (k := 0) (by norm_num) h0
    rw [flagEquiv_ovRep_zero, (smul_flag0_iff s).2 hs] at hsc
    rw [← hcu, ← hsc]
    exact (overRel_equiv hX).refl _
  · rw [← hcu]
    exact overRel_orbit (by norm_num) h2 h

theorem d4N_le_of_rel {X : Subgroup D} (hX : d4B ≤ X)
    (h : overRel X flag0 (flagEquiv (ovRep 1))) : d4N ≤ X := by
  obtain ⟨-, -, -, -, h5, h6, -, hF8, hF9, -, -⟩ := ovFlag_parts
  intro n hn
  apply overRel_base hX
  have hline : (n • flag0).1.2 = (0 : Fin 2457) := by
    show n • flag0.1.2 = 0
    rw [flag0_snd]
    exact (smul_line_zero_iff n).1 ((mem_d4N_iff n).1 hn)
  set c : Fin 7371 := flagEquiv.symm (n • flag0) with hc
  have hcu : flagEquiv c = n • flag0 := by rw [hc, Equiv.apply_symm_apply]
  have hc3 : c.val / 3 = 0 := by
    have h1 : (flagEquiv c).1.2 = (0 : Fin 2457) := by rw [hcu]; exact hline
    have h2 := congrArg Fin.val h1
    simpa [flagEquiv_apply, flagOf] using h2
  have hlab : ovBForest.1[(c : ℕ)]! = 0 ∨ ovBForest.1[(c : ℕ)]! = 1 := by
    have hroot := (orbitLabelOK_parts hF8).2.2.1
    have r0 := (hroot 0 (by norm_num)).2.1
    have r1 := (hroot 1 (by norm_num)).2.1
    simp only [List.getElem!_toArray, h5, h6] at r0 r1
    rcases (by omega : c.val = 0 ∨ c.val = 1 ∨ c.val = 2) with e | e | e
    · left
      rw [show (c : ℕ) = 0 from e]
      exact r0
    · right
      rw [show (c : ℕ) = 1 from e]
      exact r1
    · right
      rw [show (c : ℕ) = 2 from e]
      exact hF9
  rcases hlab with h0 | h1
  · obtain ⟨s, hs, hsc⟩ := ovB_orbit (k := 0) (by norm_num) h0
    rw [flagEquiv_ovRep_zero, (smul_flag0_iff s).2 hs] at hsc
    rw [← hcu, ← hsc]
    exact (overRel_equiv hX).refl _
  · rw [← hcu]
    exact overRel_orbit (by norm_num) h1 h

theorem overRel_merge {X : Subgroup D} (hX : d4B ≤ X) {k : ℕ} (hk3 : 3 ≤ k) (hk : k < 12)
    (hp : overRel X flag0 (flagEquiv (ovRep k))) :
    overRel X flag0 (flagEquiv (ovRep 1)) ∧ overRel X flag0 (flagEquiv (ovRep 2)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hmerge, -⟩ := ovFlag_parts
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have hj : j < 9 := by omega
  have hrep : ∀ i : Fin 8, Rep 7371 flagArrs[(i : ℕ)]! (flagAct (d4GenG i)) :=
    fun i => flagAct_gen i.2
  have hvalid := validTargetMerge_of_mergeTargetsOK (S := fun i : Fin 8 => flagAct (d4GenG i))
    (G := flagArrs) hrep (b := (0 : Fin 7371)) (x := ovRep (j + 3)) (L := ovMerge j)
    (ts := [1, 3]) (by rw [ovRep_val hk]; simpa using hmerge j hj)
  have hR : Equivalence (fun u v : Fin 7371 => overRel X (flagEquiv u) (flagEquiv v)) :=
    ⟨fun u => (overRel_equiv hX).refl _, fun h => (overRel_equiv hX).symm h,
      fun h h' => (overRel_equiv hX).trans h h'⟩
  have hinv : ∀ (i : Fin 8) (u v : Fin 7371), overRel X (flagEquiv u) (flagEquiv v) →
      overRel X (flagEquiv (flagAct (d4GenG i) u)) (flagEquiv (flagAct (d4GenG i) v)) := by
    intro i u v h
    rw [flagEquiv_flagAct, flagEquiv_flagAct]
    exact overRel_inv X _ h
  have hbx : overRel X (flagEquiv 0) (flagEquiv (ovRep (j + 3))) := by
    rw [show flagEquiv 0 = flag0 from rfl]
    exact hp
  have := invariant_merge_targets_soundness (fun i : Fin 8 => flagAct (d4GenG i)) 0
    (ovRep (j + 3)) (ovMerge j) [1, 3] hvalid
    (fun u v => overRel X (flagEquiv u) (flagEquiv v)) hR hinv hbx
  refine ⟨?_, ?_⟩
  · have h1 := this 1 (by simp)
    rw [ovRep_one]
    exact h1
  · have h3 := this 3 (by simp)
    rw [ovRep_two]
    exact h3

theorem class_cases {X : Subgroup D} (hX : d4B ≤ X) {g : D} (hgX : g ∈ X) (hgB : g ∉ d4B) :
    (g ∈ d4N ∧ d4N ≤ X) ∨ (g ∈ d4H ∧ d4H ≤ X) ∨ (d4H ≤ X ∧ d4N ≤ X) := by
  obtain ⟨-, -, -, -, -, -, -, hF8, -, -, -, -, hF13⟩ := ovFlag_parts
  set c : Fin 7371 := flagEquiv.symm (g • flag0) with hc
  have hcu : flagEquiv c = g • flag0 := by rw [hc, Equiv.apply_symm_apply]
  have hrel : overRel X flag0 (flagEquiv c) := by
    rw [hcu]
    exact overRel_of_mem hgX
  set k := ovBForest.1[(c : ℕ)]! with hk
  have hk12 : k < 12 := (orbitLabelOK_parts hF8).1 c c.2
  obtain ⟨s, hs, hsc⟩ := ovB_orbit hk12 hk.symm
  have hrelk : overRel X flag0 (flagEquiv (ovRep k)) := by
    have := overRel_inv X s⁻¹ hrel
    rwa [← hsc, inv_smul_smul, (smul_flag0_iff s⁻¹).2 (inv_mem hs)] at this
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k) with h0 | h1 | h2 | h3
  · exfalso
    apply hgB
    rw [← smul_flag0_iff, ← hcu, ← hsc]
    rw [h0, flagEquiv_ovRep_zero, (smul_flag0_iff s).2 hs]
  · left
    refine ⟨?_, d4N_le_of_rel hX (by rw [h1, ovRep_one] at hrelk; rw [ovRep_one]; exact hrelk)⟩
    have hline : (flagEquiv (ovRep 1)).1.2 = (0 : Fin 2457) := by
      rw [ovRep_one]
      apply Fin.ext
      simp [flagEquiv_apply, flagOf]
    have h2' : (g • flag0).1.2 = (0 : Fin 2457) := by
      rw [← hcu, ← hsc, h1, smul_flag_snd, hline]
      exact (mem_d4B_iff s).1 hs |>.2 |> (smul_line_zero_iff s).1
    have h3 : g • (0 : Fin 2457) = 0 := by
      have := h2'
      rw [smul_flag_snd, flag0_snd] at this
      exact this
    exact (mem_d4N_iff g).2 ((smul_line_zero_iff g).2 h3)
  · right
    left
    refine ⟨?_, d4H_le_of_rel hX (by rw [h2] at hrelk; exact hrelk)⟩
    have hpt : (flagEquiv (ovRep 2)).1.1 = pt0 := by
      rw [ovRep_two]
      apply Fin.ext
      simpa [flagEquiv_apply, flagOf, pt0] using hF13
    have h2' : (g • flag0).1.1 = pt0 := by
      rw [← hcu, ← hsc, h2, smul_flag_fst, hpt]
      exact ((mem_d4B_iff s).1 hs).1
    have h3 : g • pt0 = pt0 := by
      have := h2'
      rw [smul_flag_fst, flag0_fst] at this
      exact this
    exact (mem_d4H_iff g).2 h3
  · right
    right
    have hm := overRel_merge hX h3 hk12 hrelk
    exact ⟨d4H_le_of_rel hX hm.2, d4N_le_of_rel hX hm.1⟩

theorem d4_lattice (X : Subgroup D) (hX : d4B ≤ X) :
    X = d4B ∨ X = d4H ∨ X = d4N ∨ X = ⊤ := by
  by_cases hXB : X ≤ d4B
  · exact Or.inl (le_antisymm hXB hX)
  by_cases hH : d4H ≤ X
  · by_cases hN : d4N ≤ X
    · right
      right
      right
      rw [eq_top_iff, ← d4H_sup_d4N]
      exact sup_le hH hN
    · right
      left
      refine le_antisymm ?_ hH
      intro g hg
      by_cases hgB : g ∈ d4B
      · exact (Subgroup.mem_inf.1 hgB).1
      · rcases class_cases hX hg hgB with ⟨-, hN'⟩ | ⟨hgH, -⟩ | ⟨-, hN'⟩
        · exact absurd hN' hN
        · exact hgH
        · exact absurd hN' hN
  · by_cases hN : d4N ≤ X
    · right
      right
      left
      refine le_antisymm ?_ hN
      intro g hg
      by_cases hgB : g ∈ d4B
      · exact (Subgroup.mem_inf.1 hgB).2
      · rcases class_cases hX hg hgB with ⟨hgN, -⟩ | ⟨-, hH'⟩ | ⟨hH', -⟩
        · exact hgN
        · exact absurd hH' hH
        · exact absurd hH' hH
    · exfalso
      apply hXB
      intro g hg
      by_contra hgB
      rcases class_cases hX hg hgB with ⟨-, hN'⟩ | ⟨-, hH'⟩ | ⟨hH', -⟩
      · exact hN hN'
      · exact hH hH'
      · exact hH hH'

end Lattice

end CFSG.Quasithin.D4Hex
