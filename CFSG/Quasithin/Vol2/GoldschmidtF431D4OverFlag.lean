module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Lines
public import Certificates.Certificate4238

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates

set_option linter.unusedSectionVars false

section Index

theorem lineIdx_parts :
    (∀ l < 2457, lineIndex.getD (lineKey (lnPt l 0) (lnPt l 1) (lnPt l 2)) 0 = l) ∧
    ∀ j < 8, ∀ l < 2457, lineIndex.getD (imgKey j l) 0 < 2457 ∧
      lineKey (lnPt (lineIndex.getD (imgKey j l) 0) 0) (lnPt (lineIndex.getD (imgKey j l) 0) 1)
        (lnPt (lineIndex.getD (imgKey j l) 0) 2) = imgKey j l := by
  have h := lineCheck_true
  simp only [lineCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun l hl => ?_, fun j hj l hl => ?_⟩
  · have := allLt_spec h3 hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.2
  · have := allLt_spec (allLt_spec h4 hj) hl
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

@[expose] def imgLine {j : ℕ} (hj : j < 8) (l : Fin 2457) : Fin 2457 :=
  ⟨lineIndex.getD (imgKey j l) 0, (lineIdx_parts.2 j hj l l.2).1⟩

theorem lineAct_gen_idx {j : ℕ} (hj : j < 8) (l : Fin 2457) :
    (d4GenG j) • l = imgLine hj l := by
  apply lineSet_injective
  rw [lineSet_smul]
  set l' := imgLine hj l with hl'
  have hk : imgKey j l = lineKey (lnPt l' 0) (lnPt l' 1) (lnPt l' 2) :=
    (lineIdx_parts.2 j hj l l.2).2.symm
  have hasc' := lnPt_asc l'.2
  have hperm : ∀ p : Fin 819, (act (d4GenG j) p : ℕ) = (permArrs[j]!)[(p : ℕ)]! := fun p =>
    ((act_gen hj) p).symm
  have e0 : (permArrs[j]!)[lnPt l 0]! < 819 := by
    have := (act (d4GenG j) (lpt0 l)).2
    rw [hperm (lpt0 l)] at this
    exact this
  have e1 : (permArrs[j]!)[lnPt l 1]! < 819 := by
    have := (act (d4GenG j) (lpt1 l)).2
    rw [hperm (lpt1 l)] at this
    exact this
  have e2 : (permArrs[j]!)[lnPt l 2]! < 819 := by
    have := (act (d4GenG j) (lpt2 l)).2
    rw [hperm (lpt2 l)] at this
    exact this
  obtain ⟨x, y, z, hxy, hyz, hz, hkey, hx, ha⟩ := sortKey_eq e0 e1 e2
  have hk' : lineKey x y z = lineKey (lnPt l' 0) (lnPt l' 1) (lnPt l' 2) := by
    rw [← hkey]
    exact hk
  obtain ⟨hx', hy', hz'⟩ := lineKey_inj (by omega) (by omega) (by omega) (by omega) hk'
  have h0 : (act (d4GenG j) (lpt0 l) : ℕ) = (permArrs[j]!)[lnPt l 0]! := hperm (lpt0 l)
  have h1 : (act (d4GenG j) (lpt1 l) : ℕ) = (permArrs[j]!)[lnPt l 1]! := hperm (lpt1 l)
  have h2 : (act (d4GenG j) (lpt2 l) : ℕ) = (permArrs[j]!)[lnPt l 2]! := hperm (lpt2 l)
  have g0 : ((lpt0 l' : Fin 819) : ℕ) = x := hx'.symm
  have g1 : ((lpt1 l' : Fin 819) : ℕ) = y := hy'.symm
  have g2 : ((lpt2 l' : Fin 819) : ℕ) = z := hz'.symm
  rw [lineSet, Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  apply finset3_eq
  rw [h0, h1, h2, g0, g1, g2]
  exact ⟨ha, hx⟩

end Index

section Flags

@[expose] def Flag : Type := {x : Fin 819 × Fin 2457 // x.1 ∈ lineSet x.2}

noncomputable instance instMulActionFlag : MulAction D Flag where
  smul g x := ⟨(g • x.1.1, g • x.1.2), (mem_lineSet_smul_iff g x.1.1 x.1.2).2 x.2⟩
  one_smul x := Subtype.ext (Prod.ext (one_smul D x.1.1) (one_smul D x.1.2))
  mul_smul g h x := Subtype.ext (Prod.ext (mul_smul g h x.1.1) (mul_smul g h x.1.2))

theorem smul_flag_fst (g : D) (x : Flag) : (g • x).1.1 = g • x.1.1 := rfl

theorem smul_flag_snd (g : D) (x : Flag) : (g • x).1.2 = g • x.1.2 := rfl

theorem lnPt_lt {l k : ℕ} (hl : l < 2457) (hk : k < 3) : lnPt l k < 819 := by
  have := lnPt_asc hl
  interval_cases k <;> omega

@[expose] def flagOf (c : Fin 7371) : Flag :=
  ⟨(⟨lnPt (c / 3) (c % 3), lnPt_lt (by omega) (Nat.mod_lt _ (by norm_num))⟩,
    ⟨c / 3, by omega⟩), by
    rw [mem_lineSet_iff]
    rcases (by omega : c.val % 3 = 0 ∨ c.val % 3 = 1 ∨ c.val % 3 = 2) with h | h | h <;>
      simp [h]⟩

theorem flagOf_injective : Function.Injective flagOf := by
  intro c c' h
  have h2 := congrArg (fun x : Flag => (x.1.2 : Fin 2457).val) h
  have h1 := congrArg (fun x : Flag => (x.1.1 : Fin 819).val) h
  simp only [flagOf] at h1 h2
  have hl : c.val / 3 < 2457 := by omega
  have hasc := lnPt_asc hl
  rw [← h2] at h1
  have hm : c.val % 3 = c'.val % 3 := by
    rcases (by omega : c.val % 3 = 0 ∨ c.val % 3 = 1 ∨ c.val % 3 = 2) with e | e | e <;>
    rcases (by omega : c'.val % 3 = 0 ∨ c'.val % 3 = 1 ∨ c'.val % 3 = 2) with e' | e' | e' <;>
    simp only [e, e'] at h1 ⊢ <;> omega
  apply Fin.ext
  omega

theorem flagOf_surjective : Function.Surjective flagOf := by
  rintro ⟨⟨p, l⟩, hp⟩
  rw [mem_lineSet_iff] at hp
  have key : ∀ k : ℕ, k < 3 → (p : ℕ) = lnPt l k → ∃ c, flagOf c = ⟨(p, l), by
      rw [mem_lineSet_iff]; exact hp⟩ := by
    intro k hk hpk
    have hl := l.2
    refine ⟨⟨3 * l.val + k, by omega⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have e1 : (3 * l.val + k) / 3 = l.val := by omega
      have e2 : (3 * l.val + k) % 3 = k := by omega
      show lnPt ((3 * l.val + k) / 3) ((3 * l.val + k) % 3) = p
      rw [e1, e2, hpk]
    · apply Fin.ext
      show (3 * l.val + k) / 3 = l.val
      omega
  rcases hp with h | h | h
  · exact key 0 (by norm_num) h
  · exact key 1 (by norm_num) h
  · exact key 2 (by norm_num) h

@[expose] noncomputable def flagEquiv : Fin 7371 ≃ Flag :=
  Equiv.ofBijective flagOf ⟨flagOf_injective, flagOf_surjective⟩

theorem flagEquiv_apply (c : Fin 7371) : flagEquiv c = flagOf c := rfl

end Flags

section Action

@[expose] noncomputable def flagAct : D →* Equiv.Perm (Fin 7371) :=
  (flagEquiv.symm.permCongrHom : Equiv.Perm Flag ≃* Equiv.Perm (Fin 7371)).toMonoidHom.comp
    (MulAction.toPermHom D Flag)

theorem flagAct_apply (g : D) (c : Fin 7371) : flagAct g c = flagEquiv.symm (g • flagEquiv c) :=
  rfl

theorem flagEquiv_flagAct (g : D) (c : Fin 7371) : flagEquiv (flagAct g c) = g • flagEquiv c := by
  rw [flagAct_apply, Equiv.apply_symm_apply]

theorem flagGen_lt {j : ℕ} (hj : j < 8) {c : ℕ} (hc : c < 7371) : flagGen j c < 7371 := by
  have := (lineIdx_parts.2 j hj (c / 3) (by omega)).1
  simp only [flagGen]
  split_ifs <;> omega

theorem flagAct_gen {j : ℕ} (hj : j < 8) : Rep 7371 flagArrs[j]! (flagAct (d4GenG j)) := by
  intro c
  have hL : (flagArrs[j]!)[c.val]! = flagGen j c.val := by
    rw [flagArrs, CFSG.Sporadic.Schreier.Tits.getElem!_ofFn_of_lt _ hj]
    simp only [flagArr]
    rw [getElem!_ofFn_nat _ c.2]
  rw [hL]
  have hlt := flagGen_lt hj c.2
  have hmain : d4GenG j • flagEquiv c = flagEquiv ⟨flagGen j c.val, hlt⟩ := by
    have hl : c.val / 3 < 2457 := by omega
    have hline : d4GenG j • (⟨c.val / 3, hl⟩ : Fin 2457) = imgLine hj ⟨c.val / 3, hl⟩ :=
      lineAct_gen_idx hj _
    have hl' := (imgLine hj ⟨c.val / 3, hl⟩).2
    have hperm : ∀ p : Fin 819, (act (d4GenG j) p : ℕ) = (permArrs[j]!)[(p : ℕ)]! := fun p =>
      ((act_gen hj) p).symm
    have hm3 : flagGen j c.val / 3 = (imgLine hj ⟨c.val / 3, hl⟩).val := by
      simp only [flagGen, imgLine]
      split_ifs <;> omega
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      show (act (d4GenG j) ⟨lnPt (c.val / 3) (c.val % 3), _⟩ : ℕ) =
        lnPt (flagGen j c.val / 3) (flagGen j c.val % 3)
      rw [hperm]
      show (permArrs[j]!)[lnPt (c.val / 3) (c.val % 3)]! = _
      have hinc : (d4GenG j • (flagEquiv c).1.1) ∈ lineSet (d4GenG j • (flagEquiv c).1.2) :=
        (mem_lineSet_smul_iff _ _ _).2 (flagEquiv c).2
      have hinc' : (act (d4GenG j) (flagEquiv c).1.1 : ℕ) =
          lnPt (imgLine hj ⟨c.val / 3, hl⟩) 0 ∨ (act (d4GenG j) (flagEquiv c).1.1 : ℕ) =
          lnPt (imgLine hj ⟨c.val / 3, hl⟩) 1 ∨ (act (d4GenG j) (flagEquiv c).1.1 : ℕ) =
          lnPt (imgLine hj ⟨c.val / 3, hl⟩) 2 := by
        rw [show (flagEquiv c).1.2 = (⟨c.val / 3, hl⟩ : Fin 2457) from rfl, hline,
          mem_lineSet_iff] at hinc
        exact hinc
      rw [hperm] at hinc'
      have hp : (permArrs[j]!)[lnPt (c.val / 3) (c.val % 3)]! =
          (permArrs[j]!)[((flagEquiv c).1.1 : ℕ)]! := rfl
      rw [← hp] at hinc'
      simp only [flagGen, imgLine] at hm3 hinc' ⊢
      by_cases h0 : lnPt (lineIndex.getD (imgKey j (c.val / 3)) 0) 0 =
          (permArrs[j]!)[lnPt (c.val / 3) (c.val % 3)]!
      · simp only [h0, ite_true]
        have e1 : (3 * lineIndex.getD (imgKey j (c.val / 3)) 0 + 0) / 3 =
            lineIndex.getD (imgKey j (c.val / 3)) 0 := by omega
        have e2 : (3 * lineIndex.getD (imgKey j (c.val / 3)) 0 + 0) % 3 = 0 := by omega
        rw [e1, e2, h0]
      · by_cases h1 : lnPt (lineIndex.getD (imgKey j (c.val / 3)) 0) 1 =
            (permArrs[j]!)[lnPt (c.val / 3) (c.val % 3)]!
        · simp only [h0, h1, ite_true, ite_false]
          have e1 : (3 * lineIndex.getD (imgKey j (c.val / 3)) 0 + 1) / 3 =
              lineIndex.getD (imgKey j (c.val / 3)) 0 := by omega
          have e2 : (3 * lineIndex.getD (imgKey j (c.val / 3)) 0 + 1) % 3 = 1 := by omega
          rw [e1, e2, h1]
        · simp only [h0, h1, ite_false]
          have h2 : lnPt (lineIndex.getD (imgKey j (c.val / 3)) 0) 2 =
              (permArrs[j]!)[lnPt (c.val / 3) (c.val % 3)]! := by
            rcases hinc' with h | h | h
            · exact absurd h.symm h0
            · exact absurd h.symm h1
            · exact h.symm
          have e1 : (3 * lineIndex.getD (imgKey j (c.val / 3)) 0 + 2) / 3 =
              lineIndex.getD (imgKey j (c.val / 3)) 0 := by omega
          have e2 : (3 * lineIndex.getD (imgKey j (c.val / 3)) 0 + 2) % 3 = 2 := by omega
          rw [e1, e2, h2]
    · apply Fin.ext
      show ((d4GenG j • (⟨c.val / 3, hl⟩ : Fin 2457) : Fin 2457) : ℕ) = flagGen j c.val / 3
      rw [hline, hm3]
  rw [flagAct_apply, hmain, Equiv.symm_apply_apply]

end Action

section Words

theorem rep_flagWordArr : ∀ w : List ℕ, (∀ k ∈ w, k < 8) →
    Rep 7371 (flagWordArr w) (flagAct (d4Word w))
  | [], _ => by
    have := rep_idA (n := 7371)
    simpa [flagWordArr, d4Word] using this
  | k :: w, hw => by
    have h1 := flagAct_gen (hw k List.mem_cons_self)
    have h2 := rep_flagWordArr w (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))
    have h3 := rep_compA h1 h2
    simpa [flagWordArr, d4Word, map_mul] using h3

@[expose] noncomputable def d4Zeta : D := d4Word [3, 2, 4, 2]

theorem rep_ptWordArr {w : List ℕ} (hw : ∀ k ∈ w, k < 8) :
    Rep 819 (ptWordArr w) (act (d4Word w)) := rep_d4WordArr w hw

end Words

section Check

theorem overCheck_parts : ovFlagCheck = true ∧ ovUCheck = true ∧ ovZetaCheck = true := by
  have h := (Certificates.certificate4238 : overCheck = true)
  simp only [overCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem ovFlag_parts : flagArrs.size = 8 ∧ bFlagArrs.size = 5 ∧
    orbitLabelOK 7371 flagArrs 1 ovDForest.1 #[0] ovDForest.2.1 ovDForest.2.2.1
      ovDForest.2.2.2 = true ∧
    ovReps.length = 12 ∧ ovReps[0]! = 0 ∧ ovReps[1]! = 1 ∧ ovReps[2]! = 3 ∧
    orbitLabelOK 7371 bFlagArrs 12 ovBForest.1 ovReps.toArray ovBForest.2.1 ovBForest.2.2.1
      ovBForest.2.2.2 = true ∧
    ovBForest.1[2]! = 1 ∧
    (∀ c < 7371, lnPt (c / 3) (c % 3) = 0 → ovBForest.1[c]! = 0 ∨ ovBForest.1[c]! = 2) ∧
    ovMergeLens.length = 9 ∧
    (∀ j < 9, mergeTargetsOK 7371 flagArrs 0 ovReps[j + 3]! (mergeVals (ovMerge j)) [1, 3] =
      true) ∧ lnPt 1 0 = 0 := by
  have h := overCheck_parts.1
  simp only [ovFlagCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun c hc hc0 => ?_, h11, fun j hj => ?_, h13⟩
  · have := allLt_spec h10 hc
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
    rcases this with (h | h) | h
    · exact absurd hc0 h
    · exact Or.inl h
    · exact Or.inr h
  · exact allLt_spec h12 hj

end Check

section Zeta

theorem ovZeta_parts :
    (ptWordArr [3, 2, 4, 2])[0]! = 0 ∧ fixesLine0 (ptWordArr [3, 2, 4, 2]) = true ∧
    ptPowArr (ptWordArr [3, 2, 4, 2]) 7 = idA 819 ∧
    compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[0]! =
      compA 819 (ptWordArr [2]) (ptWordArr [3, 2, 4, 2]) ∧
    compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[1]! =
      compA 819 (ptWordArr [0, 1]) (ptWordArr [3, 2, 4, 2]) ∧
    compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[2]! =
      compA 819 (ptWordArr [1, 2]) (ptWordArr [3, 2, 4, 2]) ∧
    compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[6]! =
      compA 819 (ptWordArr [0, 2, 6, 0, 2]) (ptWordArr [3, 2, 4, 2]) ∧
    compA 819 (ptWordArr [3, 2, 4, 2]) permArrs[0]! ≠
      compA 819 permArrs[0]! (ptWordArr [3, 2, 4, 2]) ∧
    (permArrs[7]!)[0]! ≠ 0 ∧ fixesLine0 permArrs[7]! = true ∧
    (permArrs[3]!)[0]! = 0 ∧ fixesLine0 permArrs[3]! = false := by
  have h := overCheck_parts.2.2
  simp only [ovZetaCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

end Zeta

end CFSG.Quasithin.D4Hex
