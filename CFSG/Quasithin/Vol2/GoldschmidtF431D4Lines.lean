module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Stab

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem lineKey_inj {a b c a' b' c' : ℕ} (hb : b < 819) (hc : c < 819) (hb' : b' < 819)
    (hc' : c' < 819) (h : lineKey a b c = lineKey a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  unfold lineKey at h
  omega

theorem sortKey_eq {a b c : ℕ} (ha : a < 819) (hb : b < 819) (hc : c < 819) :
    ∃ x y z, x ≤ y ∧ y ≤ z ∧ z < 819 ∧ sortKey a b c = lineKey x y z ∧
      ((x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c) ∧ (z = a ∨ z = b ∨ z = c)) ∧
      ((a = x ∨ a = y ∨ a = z) ∧ (b = x ∨ b = y ∨ b = z) ∧ (c = x ∨ c = y ∨ c = z)) := by
  refine ⟨min a (min b c), a + b + c - min a (min b c) - max a (max b c), max a (max b c),
    ?_, ?_, ?_, rfl, ?_, ?_⟩ <;> omega

section Table

theorem lineCheck_parts : ∃ idx : ℕ → ℕ, lnPt 0 0 = 0 ∧ lnPt 0 1 = 1 ∧ lnPt 0 2 = 5 ∧
    (∀ l < 2457, lnPt l 0 < lnPt l 1 ∧ lnPt l 1 < lnPt l 2 ∧ lnPt l 2 < 819 ∧
      idx (lineKey (lnPt l 0) (lnPt l 1) (lnPt l 2)) = l) ∧
    ∀ j < 8, ∀ l < 2457, idx (imgKey j l) < 2457 ∧
      lineKey (lnPt (idx (imgKey j l)) 0) (lnPt (idx (imgKey j l)) 1)
        (lnPt (idx (imgKey j l)) 2) = imgKey j l := by
  have h := lineCheck_true
  simp only [lineCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun k => lineIndex.getD k 0, h0, h1, h2, fun l hl => ?_, fun j hj l hl => ?_⟩
  · have := allLt_spec h3 hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · have := allLt_spec (allLt_spec h4 hj) hl
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem lnPt_asc {l : ℕ} (hl : l < 2457) :
    lnPt l 0 < lnPt l 1 ∧ lnPt l 1 < lnPt l 2 ∧ lnPt l 2 < 819 := by
  obtain ⟨idx, -, -, -, h, -⟩ := lineCheck_parts
  exact ⟨(h l hl).1, (h l hl).2.1, (h l hl).2.2.1⟩

theorem lnPt_zero : lnPt 0 0 = 0 ∧ lnPt 0 1 = 1 ∧ lnPt 0 2 = 5 := by
  obtain ⟨idx, h0, h1, h2, -⟩ := lineCheck_parts
  exact ⟨h0, h1, h2⟩

theorem lnPt_inj {l l' : ℕ} (hl : l < 2457) (hl' : l' < 2457) (h0 : lnPt l 0 = lnPt l' 0)
    (h1 : lnPt l 1 = lnPt l' 1) (h2 : lnPt l 2 = lnPt l' 2) : l = l' := by
  obtain ⟨idx, -, -, -, h, -⟩ := lineCheck_parts
  rw [← (h l hl).2.2.2, ← (h l' hl').2.2.2, h0, h1, h2]

theorem lnPt_gen {j : ℕ} (hj : j < 8) {l : ℕ} (hl : l < 2457) :
    ∃ l' < 2457, imgKey j l = lineKey (lnPt l' 0) (lnPt l' 1) (lnPt l' 2) := by
  obtain ⟨idx, -, -, -, -, h⟩ := lineCheck_parts
  exact ⟨idx (imgKey j l), (h j hj l hl).1, ((h j hj l hl).2).symm⟩

@[expose] def lpt0 (l : Fin 2457) : Fin 819 := ⟨lnPt l 0, (lnPt_asc l.2).1.trans
  ((lnPt_asc l.2).2.1.trans (lnPt_asc l.2).2.2)⟩

@[expose] def lpt1 (l : Fin 2457) : Fin 819 := ⟨lnPt l 1, (lnPt_asc l.2).2.1.trans
  (lnPt_asc l.2).2.2⟩

@[expose] def lpt2 (l : Fin 2457) : Fin 819 := ⟨lnPt l 2, (lnPt_asc l.2).2.2⟩

@[expose] def lineSet (l : Fin 2457) : Finset (Fin 819) := {lpt0 l, lpt1 l, lpt2 l}

theorem mem_lineSet_iff (p : Fin 819) (l : Fin 2457) :
    p ∈ lineSet l ↔ (p : ℕ) = lnPt l 0 ∨ (p : ℕ) = lnPt l 1 ∨ (p : ℕ) = lnPt l 2 := by
  simp only [lineSet, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, lpt0, lpt1, lpt2]

theorem lineSet_zero : lineSet 0 = line0 := by
  ext p
  rw [mem_lineSet_iff]
  obtain ⟨h0, h1, h2⟩ := lnPt_zero
  simp only [line0, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, pt0]
  show _ ↔ _
  simp only [show ((0 : Fin 2457) : ℕ) = 0 from rfl, h0, h1, h2]

theorem lineSet_injective : Function.Injective lineSet := by
  intro l l' h
  have hl := lnPt_asc l.2
  have hl' := lnPt_asc l'.2
  have hsub : ∀ p : Fin 819, (p : ℕ) = lnPt l 0 ∨ (p : ℕ) = lnPt l 1 ∨ (p : ℕ) = lnPt l 2 ↔
      (p : ℕ) = lnPt l' 0 ∨ (p : ℕ) = lnPt l' 1 ∨ (p : ℕ) = lnPt l' 2 := fun p => by
    rw [← mem_lineSet_iff, ← mem_lineSet_iff, h]
  have a0 := (hsub (lpt0 l)).1 (Or.inl rfl)
  have a1 := (hsub (lpt1 l)).1 (Or.inr (Or.inl rfl))
  have a2 := (hsub (lpt2 l)).1 (Or.inr (Or.inr rfl))
  have b0 := (hsub (lpt0 l')).2 (Or.inl rfl)
  have b1 := (hsub (lpt1 l')).2 (Or.inr (Or.inl rfl))
  have b2 := (hsub (lpt2 l')).2 (Or.inr (Or.inr rfl))
  simp only [lpt0, lpt1, lpt2] at a0 a1 a2 b0 b1 b2
  apply Fin.ext
  exact lnPt_inj l.2 l'.2 (by omega) (by omega) (by omega)

theorem finset3_eq {p0 p1 p2 q0 q1 q2 : Fin 819}
    (h : (((p0 : ℕ) = q0 ∨ (p0 : ℕ) = q1 ∨ (p0 : ℕ) = q2) ∧
      ((p1 : ℕ) = q0 ∨ (p1 : ℕ) = q1 ∨ (p1 : ℕ) = q2) ∧
      ((p2 : ℕ) = q0 ∨ (p2 : ℕ) = q1 ∨ (p2 : ℕ) = q2)) ∧
      (((q0 : ℕ) = p0 ∨ (q0 : ℕ) = p1 ∨ (q0 : ℕ) = p2) ∧
      ((q1 : ℕ) = p0 ∨ (q1 : ℕ) = p1 ∨ (q1 : ℕ) = p2) ∧
      ((q2 : ℕ) = p0 ∨ (q2 : ℕ) = p1 ∨ (q2 : ℕ) = p2))) :
    ({p0, p1, p2} : Finset (Fin 819)) = {q0, q1, q2} := by
  ext r
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem image_lineSet_gen {j : ℕ} (hj : j < 8) (l : Fin 2457) :
    ∃ l' : Fin 2457, (lineSet l).image (act (d4GenG j)) = lineSet l' := by
  obtain ⟨l', hl', hk⟩ := lnPt_gen hj l.2
  have hasc' := lnPt_asc hl'
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
  refine ⟨⟨l', hl'⟩, ?_⟩
  have h0 : (act (d4GenG j) (lpt0 l) : ℕ) = (permArrs[j]!)[lnPt l 0]! := hperm (lpt0 l)
  have h1 : (act (d4GenG j) (lpt1 l) : ℕ) = (permArrs[j]!)[lnPt l 1]! := hperm (lpt1 l)
  have h2 : (act (d4GenG j) (lpt2 l) : ℕ) = (permArrs[j]!)[lnPt l 2]! := hperm (lpt2 l)
  have g0 : ((lpt0 ⟨l', hl'⟩ : Fin 819) : ℕ) = x := hx'.symm
  have g1 : ((lpt1 ⟨l', hl'⟩ : Fin 819) : ℕ) = y := hy'.symm
  have g2 : ((lpt2 ⟨l', hl'⟩ : Fin 819) : ℕ) = z := hz'.symm
  rw [lineSet, Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  apply finset3_eq
  rw [h0, h1, h2, g0, g1, g2]
  exact ⟨ha, hx⟩

theorem exists_image_lineSet (g : D) :
    ∀ l : Fin 2457, ∃ l' : Fin 2457, (lineSet l).image (act g) = lineSet l' := by
  have hg : g ∈ Subgroup.closure (Set.range d4GenG) := by
    rw [closure_d4GenG]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨j, hj, hk⟩ := d4GenG_lt_eight k
    rw [hk]
    exact fun l => image_lineSet_gen hj l
  | one => exact fun l => ⟨l, by simp⟩
  | mul x y _ _ ihx ihy =>
    intro l
    obtain ⟨l1, h1⟩ := ihy l
    obtain ⟨l2, h2⟩ := ihx l1
    refine ⟨l2, ?_⟩
    rw [map_mul, Equiv.Perm.coe_mul, ← Finset.image_image, h1, h2]
  | inv x _ ihx =>
    choose f hf using ihx
    have hinj : Function.Injective f := by
      intro l l' h
      apply lineSet_injective
      have := hf l
      rw [h, ← hf l'] at this
      exact Finset.image_injective (act x).injective this
    have hsurj := Finite.injective_iff_surjective.1 hinj
    intro l
    obtain ⟨l', hl'⟩ := hsurj l
    refine ⟨l', ?_⟩
    have := hf l'
    rw [hl'] at this
    rw [← this, Finset.image_image]
    ext p
    simp

@[expose] noncomputable def lineActFun (g : D) (l : Fin 2457) : Fin 2457 :=
  Classical.choose (exists_image_lineSet g l)

theorem lineSet_lineActFun (g : D) (l : Fin 2457) :
    lineSet (lineActFun g l) = (lineSet l).image (act g) :=
  (Classical.choose_spec (exists_image_lineSet g l)).symm

theorem lineActFun_mul (g h : D) (l : Fin 2457) :
    lineActFun (g * h) l = lineActFun g (lineActFun h l) := by
  apply lineSet_injective
  rw [lineSet_lineActFun, lineSet_lineActFun, lineSet_lineActFun, map_mul, Equiv.Perm.coe_mul,
    ← Finset.image_image]

theorem lineActFun_one (l : Fin 2457) : lineActFun 1 l = l := by
  apply lineSet_injective
  rw [lineSet_lineActFun]
  simp

@[expose] noncomputable def lineAct : D →* Equiv.Perm (Fin 2457) where
  toFun g :=
    { toFun := lineActFun g
      invFun := lineActFun g⁻¹
      left_inv := fun l => by rw [← lineActFun_mul, inv_mul_cancel, lineActFun_one]
      right_inv := fun l => by rw [← lineActFun_mul, mul_inv_cancel, lineActFun_one] }
  map_one' := Equiv.ext lineActFun_one
  map_mul' g h := Equiv.ext (lineActFun_mul g h)

noncomputable instance instMulActionLine : MulAction D (Fin 2457) := MulAction.compHom _ lineAct

theorem lineSet_smul (g : D) (l : Fin 2457) : lineSet (g • l) = (lineSet l).image (act g) :=
  lineSet_lineActFun g l

theorem mem_lineSet_smul_iff (g : D) (p : Fin 819) (l : Fin 2457) :
    g • p ∈ lineSet (g • l) ↔ p ∈ lineSet l := by
  rw [lineSet_smul, smul_pt_def, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, hqp⟩
    rw [← (act g).injective hqp]
    exact hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem mem_d4N_of_rep {g : D} {a : Array ℕ} (hr : Rep 819 a (act g)) (h : fixesLine0 a = true) :
    g ∈ d4N := by
  have hlt : ∀ p : Fin 819, a[(p : ℕ)]! < 819 := fun p => by
    rw [hr p]
    exact (act g p).2
  have e0 := hlt ⟨0, by norm_num⟩
  have e1 := hlt ⟨1, by norm_num⟩
  have e5 := hlt ⟨5, by norm_num⟩
  simp only [fixesLine0, beq_iff_eq] at h
  obtain ⟨x, y, z, hxy, hyz, hz, hkey, hx, ha⟩ := sortKey_eq e0 e1 e5
  rw [hkey] at h
  obtain ⟨hx', hy', hz'⟩ := lineKey_inj (by omega) (by omega) (by omega) (by omega) h
  rw [mem_d4N_iff_image]
  have v0 : (act g ⟨0, by norm_num⟩ : ℕ) = a[0]! := (hr ⟨0, by norm_num⟩).symm
  have v1 : (act g ⟨1, by norm_num⟩ : ℕ) = a[1]! := (hr ⟨1, by norm_num⟩).symm
  have v5 : (act g ⟨5, by norm_num⟩ : ℕ) = a[5]! := (hr ⟨5, by norm_num⟩).symm
  rw [line0, Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  apply finset3_eq
  simp only [pt0] at *
  rw [v0, v1, v5]
  omega

theorem mem_d4H_of_rep {g : D} {a : Array ℕ} (hr : Rep 819 a (act g)) (h : a[0]! = 0) :
    g ∈ d4H := by
  rw [mem_d4H_iff_act]
  apply Fin.ext
  rw [← hr pt0]
  exact h

theorem gen_mem_H_or_N {j : ℕ} (hj : j < 8) : d4GenG j ∈ d4H ∨ d4GenG j ∈ d4N := by
  have h := baseFlagCheck_true
  simp only [baseFlagCheck, Bool.and_eq_true] at h
  have := allLt_spec h.1 hj
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h0 | h0
  · exact Or.inl (mem_d4H_of_rep (act_gen hj) h0)
  · exact Or.inr (mem_d4N_of_rep (act_gen hj) h0)

theorem gen_mem_B {j : ℕ} (hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 6) : d4GenG j ∈ d4B := by
  have h := baseFlagCheck_true
  simp only [baseFlagCheck, Bool.and_eq_true] at h
  have h8 : j < 8 := by omega
  have h1 : (permArrs[j]!)[0]! == 0 && fixesLine0 permArrs[j]! = true := by
    have := h.2
    rw [List.all_eq_true] at this
    apply this
    rcases hj with rfl | rfl | rfl | rfl <;> simp
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨mem_d4H_of_rep (act_gen h8) h1.1, mem_d4N_of_rep (act_gen h8) h1.2⟩

theorem d4H_sup_d4N : d4H ⊔ d4N = ⊤ := by
  rw [eq_top_iff, ← closure_d4GenG, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨j, hj, hk⟩ := d4GenG_lt_eight k
  rw [hk]
  rcases gen_mem_H_or_N hj with h | h
  · exact Subgroup.mem_sup_left h
  · exact Subgroup.mem_sup_right h

end Table

end CFSG.Quasithin.D4Hex
