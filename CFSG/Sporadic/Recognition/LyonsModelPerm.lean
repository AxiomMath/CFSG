module

public import CFSG.Sporadic.Recognition.LyonsModelInputs
public import CFSG.Sporadic.Recognition.McLMultiplier
public import CFSG.Sporadic.Recognition.McLMultiplierMatrix

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Ly0

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Recognition.McLMultiplier
  CFSG.LieType.Multipliers Equiv Subgroup

theorem deg_lt : deg < 2 ^ 32 := by norm_num [deg]

theorem permOK_spec {T R : Table} (h : permOK deg T R = true) :
    ∀ i < deg, ap T i < deg ∧ ap R i < deg ∧ ap R (ap T i) = i ∧ ap T (ap R i) = i := by
  unfold permOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  intro i hi
  have := allIn_eq_true.1 h.2 i (Nat.zero_le _) hi
  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using this

noncomputable def permOfTab (T R : Table) : Perm (Fin deg) :=
  if h : permOK deg T R = true then
    { toFun := fun i => ⟨ap T i.val, (permOK_spec h i.val i.isLt).1⟩
      invFun := fun i => ⟨ap R i.val, (permOK_spec h i.val i.isLt).2.1⟩
      left_inv := fun i => Fin.ext (by
        simpa using (permOK_spec h i.val i.isLt).2.2.1)
      right_inv := fun i => Fin.ext (by
        simpa using (permOK_spec h i.val i.isLt).2.2.2) }
  else 1

theorem rep_permOfTab {T R : Table} (h : permOK deg T R = true) : Rep deg T (permOfTab T R) := by
  intro i hi
  rw [idx_of_lt _ hi]
  simp [permOfTab, h]

theorem invOK_of_permOK {T R : Table} (h : permOK deg T R = true) : invOK deg T R = true := by
  unfold invOK
  rw [allIn_eq_true]
  intro i _ hi
  exact beq_iff_eq.2 (permOK_spec h i hi).2.2.1

theorem eq_of_rep {T : Table} {g h : Perm (Fin deg)} (hg : Rep deg T g) (hh : Rep deg T h) :
    g = h := by
  ext i
  have e := (hg i.val i.isLt).symm.trans (hh i.val i.isLt)
  rw [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at e
  exact e

noncomputable def letterG (gs : ℕ → Perm (Fin deg)) (l : ℤ) : Perm (Fin deg) :=
  if 0 < l then gs (l - 1).toNat else (gs (-l - 1).toNat)⁻¹

noncomputable def wG (gs : ℕ → Perm (Fin deg)) (w : List ℤ) : Perm (Fin deg) :=
  wordG (letterG gs) w

@[simp] theorem wG_nil (gs : ℕ → Perm (Fin deg)) : wG gs [] = 1 := by
  simp [wG, wordG]

@[simp] theorem wG_cons (gs : ℕ → Perm (Fin deg)) (l : ℤ) (w : List ℤ) :
    wG gs (l :: w) = letterG gs l * wG gs w := by
  simp [wG, wordG]

theorem wG_append (gs : ℕ → Perm (Fin deg)) (u v : List ℤ) :
    wG gs (u ++ v) = wG gs u * wG gs v := by
  induction u with
  | nil => simp
  | cons l u ih => simp [ih, mul_assoc]

theorem letterG_neg (gs : ℕ → Perm (Fin deg)) {l : ℤ} (hl : l ≠ 0) :
    letterG gs (-l) = (letterG gs l)⁻¹ := by
  rcases lt_trichotomy l 0 with h | h | h
  · have h1 : ¬ 0 < l := by omega
    have h2 : 0 < -l := by omega
    simp only [letterG, h1, h2, ite_false, ite_true, neg_neg, inv_inv]
  · exact absurd h hl
  · have h1 : ¬ 0 < -l := by omega
    simp only [letterG, h1, h, ite_false, ite_true, neg_neg]

theorem wG_invW (gs : ℕ → Perm (Fin deg)) {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0) :
    wG gs (invW w) = (wG gs w)⁻¹ := by
  induction w with
  | nil => simp [invW]
  | cons l w ih =>
    have hl : l ≠ 0 := hw l (by simp)
    have ih' := ih (fun l' hl' => hw l' (by simp [hl']))
    have hinv : invW (l :: w) = invW w ++ [-l] := by simp [invW]
    rw [hinv, wG_append, ih', wG_cons, wG_cons, wG_nil, mul_one, letterG_neg gs hl, mul_inv_rev]

theorem wT_nil (tabs invs : Array Table) : wT tabs invs [] = idT deg := rfl

theorem wT_cons (tabs invs : Array Table) (l : ℤ) (w : List ℤ) :
    wT tabs invs (l :: w) = compT deg (letterOf tabs invs l) (wT tabs invs w) := rfl

theorem rep_letterOf {tabs invs : Array Table} {gs : ℕ → Perm (Fin deg)} {m : ℕ}
    (hT : ∀ k < m, Rep deg tabs[k]! (gs k))
    (hI : ∀ k < m, invOK deg tabs[k]! invs[k]! = true) {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ m) :
    Rep deg (letterOf tabs invs l) (letterG gs l) := by
  unfold letterOf letterG
  by_cases hp : 0 < l
  · simp only [hp, ite_true]
    exact hT _ (by omega)
  · simp only [hp, ite_false]
    exact Rep.inv_of_invOK (hT _ (by omega)) (hI _ (by omega))

theorem rep_wT {tabs invs : Array Table} {gs : ℕ → Perm (Fin deg)} {m : ℕ}
    (hT : ∀ k < m, Rep deg tabs[k]! (gs k))
    (hI : ∀ k < m, invOK deg tabs[k]! invs[k]! = true) :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) → Rep deg (wT tabs invs w) (wG gs w) := by
  intro w
  induction w with
  | nil =>
    intro _
    rw [wT_nil, wG_nil]
    exact Rep.idT deg_lt
  | cons l w ih =>
    intro hw
    have hl := hw l (by simp)
    have ih' := ih (fun l' hl' => hw l' (by simp [hl']))
    rw [wT_cons, wG_cons]
    exact Rep.compT (rep_letterOf hT hI hl) ih'

theorem decodeWord_mem (s : String) : ∀ l ∈ decodeWord s, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  simp only [decodeWord, List.mem_map] at hl
  obtain ⟨ch, -, rfl⟩ := hl
  by_cases h1 : ch = 'c' ∨ ch = 'a'
  · simp [h1]
  · by_cases h2 : ch = 'C' ∨ ch = 'A'
    · simp [h1, h2]
    · by_cases h3 : ch = 'd' ∨ ch = 'b'
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]

noncomputable def cG : Perm (Fin deg) := permOfTab cT invs0[0]!

noncomputable def dG : Perm (Fin deg) := permOfTab dT invs0[1]!

noncomputable def gens0 (k : ℕ) : Perm (Fin deg) := if k = 0 then cG else dG

noncomputable def AG : Perm (Fin deg) := wG gens0 wordA

noncomputable def BG : Perm (Fin deg) := wG gens0 wordB

noncomputable def gens1 (k : ℕ) : Perm (Fin deg) := if k = 0 then AG else BG

noncomputable def yG (k : ℕ) : Perm (Fin deg) := wG gens1 (mclGenWord k)

noncomputable def R0G : Perm (Fin deg) := wG yG (mclR0.map letterZ)

noncomputable def xG : Perm (Fin deg) := R0G⁻¹

theorem getElem!_map_invT (tabs : Array Table) {k : ℕ} (hk : k < tabs.size) :
    (tabs.map (invT deg))[k]! = invT deg tabs[k]! := by
  rw [getElem!_pos (tabs.map (invT deg)) k (by simpa using hk), Array.getElem_map,
    getElem!_pos tabs k hk]

theorem letterG_pos (gs : ℕ → Perm (Fin deg)) {l : ℤ} (hl : 0 < l) :
    letterG gs l = gs (l - 1).toNat := by
  simp [letterG, hl]

theorem letterG_neg_of (gs : ℕ → Perm (Fin deg)) {l : ℤ} (hl : ¬ 0 < l) :
    letterG gs l = (gs (-l - 1).toNat)⁻¹ := by
  simp [letterG, hl]

theorem tabs0_zero : tabs0[0]! = cT := by simp [tabs0]

theorem tabs0_one : tabs0[1]! = dT := by simp [tabs0]

theorem invs0_get {k : ℕ} (hk : k < 2) : invs0[k]! = invT deg tabs0[k]! :=
  getElem!_map_invT tabs0 (by simpa [tabs0] using hk)

theorem invs1_get {k : ℕ} (hk : k < 2) : invs1[k]! = invT deg tabs1[k]! :=
  getElem!_map_invT tabs1 (by simpa [tabs1] using hk)

theorem invs2_get {k : ℕ} (hk : k < 6) : invs2[k]! = invT deg tabs2[k]! :=
  getElem!_map_invT tabs2 (by simpa [tabs2] using hk)

theorem tabs1_zero : tabs1[0]! = wT tabs0 invs0 wordA := by simp [tabs1]

theorem tabs1_one : tabs1[1]! = wT tabs0 invs0 wordB := by simp [tabs1]

theorem tabs2_get {k : ℕ} (hk : k < 6) : tabs2[k]! = wT tabs1 invs1 (mclGenWord k) := by
  simp [tabs2, hk]

theorem cG_def : cG = permOfTab cT invs0[0]! := by unfold cG; rfl

theorem dG_def : dG = permOfTab dT invs0[1]! := by unfold dG; rfl

theorem gens0_zero : gens0 0 = cG := by simp [gens0]

theorem gens0_one : gens0 1 = dG := by simp [gens0]

theorem AG_def : AG = wG gens0 wordA := by unfold AG; rfl

theorem BG_def : BG = wG gens0 wordB := by unfold BG; rfl

theorem gens1_zero : gens1 0 = AG := by simp [gens1]

theorem gens1_one : gens1 1 = BG := by simp [gens1]

theorem yG_def (k : ℕ) : yG k = wG gens1 (mclGenWord k) := by unfold yG; rfl

theorem R0G_def : R0G = wG yG (mclR0.map letterZ) := by unfold R0G; rfl

theorem xG_def : xG = R0G⁻¹ := by unfold xG; rfl

theorem tabCheck_spec (h : tabCheck = true) :
    permOK deg cT invs0[0]! = true ∧ permOK deg dT invs0[1]! = true ∧
      (∀ k < 2, invOK deg tabs1[k]! invs1[k]! = true) ∧
      ∀ k < 6, invOK deg tabs2[k]! invs2[k]! = true := by
  unfold tabCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem rep_cG (h : tabCheck = true) : Rep deg cT cG := rep_permOfTab (tabCheck_spec h).1

theorem rep_dG (h : tabCheck = true) : Rep deg dT dG := rep_permOfTab (tabCheck_spec h).2.1

theorem invOK_level0 (h : tabCheck = true) : ∀ k < 2, invOK deg tabs0[k]! invs0[k]! = true := by
  intro k hk
  interval_cases k
  · rw [tabs0_zero]; exact invOK_of_permOK (tabCheck_spec h).1
  · rw [tabs0_one]; exact invOK_of_permOK (tabCheck_spec h).2.1

theorem rep_gens0 (h : tabCheck = true) : ∀ k < 2, Rep deg tabs0[k]! (gens0 k) := by
  intro k hk
  interval_cases k
  · rw [tabs0_zero]; simpa [gens0] using rep_cG h
  · rw [tabs0_one]; simpa [gens0] using rep_dG h

theorem rep_gens1 (h : tabCheck = true) : ∀ k < 2, Rep deg tabs1[k]! (gens1 k) := by
  have hw := rep_wT (invs := invs0) (rep_gens0 h) (invOK_level0 h)
  intro k hk
  interval_cases k
  · rw [tabs1_zero]
    simpa [gens1, AG] using hw wordA (fun l hl => by simpa using decodeWord_mem _ l hl)
  · rw [tabs1_one]
    simpa [gens1, BG] using hw wordB (fun l hl => by simpa using decodeWord_mem _ l hl)

theorem rep_yG (h : tabCheck = true) : ∀ k < 6, Rep deg tabs2[k]! (yG k) := by
  have hw := rep_wT (invs := invs1) (rep_gens1 h) (tabCheck_spec h).2.2.1
  intro k hk
  rw [tabs2_get hk]
  refine hw (mclGenWord k) ?_
  intro l hl
  interval_cases k <;> simp [mclGenWord] at hl <;> omega

theorem letterZ_mem (l : Fin 6 × Bool) : letterZ l ≠ 0 ∧ (letterZ l).natAbs ≤ 6 := by
  obtain ⟨i, b⟩ := l
  have := i.isLt
  cases b <;> simp [letterZ] <;> omega

theorem rep_yWord (h : tabCheck = true) (w : List ℤ) (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 6) :
    Rep deg (wT tabs2 invs2 w) (wG yG w) :=
  rep_wT (invs := invs2) (rep_yG h) (tabCheck_spec h).2.2.2 w hw

theorem wG_yG_of_check (h : tabCheck = true) {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 6)
    (hT : wT tabs2 invs2 w = idT deg) : wG yG w = 1 :=
  eq_of_rep (rep_yWord h w hw) (hT ▸ Rep.idT deg_lt)

theorem lift_mk_eq_wG (w : List (Fin 6 × Bool)) :
    FreeGroup.lift (fun i : Fin 6 => yG i.val) (FreeGroup.mk w) = wG yG (w.map letterZ) := by
  induction w with
  | nil => simp
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    rw [show FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w from rfl,
      map_mul, ih, List.map_cons, wG_cons]
    congr 1
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      have h0 : ¬ 0 < letterZ (i, false) := by simp [letterZ]
      simp [letterG, letterZ]
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp [letterG, letterZ]

theorem cover_lift_eq_one (h : tabCheck = true) (hc : coverCheck = true) :
    ∀ r ∈ coverRelators (wordSet mclRels) mclCommW,
      FreeGroup.lift (fun i : Fin 6 => yG i.val) r = 1 := by
  intro r hr
  rw [coverRelators_mclCommW] at hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [lift_mk_eq_wG]
  unfold coverCheck at hc
  have h1 := beq_iff_eq.1 ((List.all_eq_true.1 hc) w hw)
  refine wG_yG_of_check h (fun l hl => ?_) h1
  obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
  exact letterZ_mem l'

noncomputable def coverHom (h : tabCheck = true) (hc : coverCheck = true) :
    MclCover →* Perm (Fin deg) :=
  PresentedGroup.toGroup (cover_lift_eq_one h hc)

theorem coverHom_of (h : tabCheck = true) (hc : coverCheck = true) (i : Fin 6) :
    coverHom h hc (PresentedGroup.of i) = yG i.val :=
  PresentedGroup.toGroup.of _

noncomputable def z0 : MclCover := PresentedGroup.mk _ (FreeGroup.mk mclR0)

theorem z0_mem_center : z0 ∈ Subgroup.center MclCover :=
  mk_mem_center mclCommW (List.mem_map_of_mem (f := FreeGroup.mk) mclR0_mem)

theorem z0_def : z0 = PresentedGroup.mk _ (FreeGroup.mk mclR0) := by unfold z0; rfl

theorem coverHom_z0 (h : tabCheck = true) (hc : coverCheck = true) :
    coverHom h hc z0 = R0G := by
  show FreeGroup.lift (fun i : Fin 6 => yG i.val) (FreeGroup.mk mclR0) = R0G
  rw [lift_mk_eq_wG]
  rfl

theorem idT_size : (idT deg).size = deg := by
  simp [idT]

theorem compT_size (P Q : Table) : (compT deg P Q).size = deg := by
  simp [compT]

theorem wT_size (tabs invs : Array Table) (w : List ℤ) : (wT tabs invs w).size = deg := by
  cases w with
  | nil => exact idT_size
  | cons l w => rw [wT_cons]; exact compT_size _ _

theorem tab_eq_of_rep {T₁ T₂ : Table} {g : Perm (Fin deg)} (h₁ : T₁.size = deg)
    (h₂ : T₂.size = deg) (hg₁ : Rep deg T₁ g) (hg₂ : Rep deg T₂ g) : T₁ = T₂ := by
  refine Array.ext (h₁.trans h₂.symm) fun i hi₁ hi₂ => ?_
  have e := (hg₁ i (h₁ ▸ hi₁)).trans (hg₂ i (h₁ ▸ hi₁)).symm
  unfold ap at e
  rw [getElem!_pos T₁ i hi₁, getElem!_pos T₂ i hi₂] at e
  exact UInt32.toNat_inj.1 e

theorem ne_of_tab_ne {T₁ T₂ : Table} {g h : Perm (Fin deg)} (h₁ : T₁.size = deg)
    (h₂ : T₂.size = deg) (hg : Rep deg T₁ g) (hh : Rep deg T₂ h) (hne : T₁ ≠ T₂) : g ≠ h := by
  rintro rfl
  exact hne (tab_eq_of_rep h₁ h₂ hg hh)

noncomputable def y0G : Perm (Fin deg) := wG gens0 wordY

noncomputable def fG : Perm (Fin deg) := wG gens0 wordF

noncomputable def nG : Perm (Fin deg) := wG gens0 wordN

theorem y0G_def : y0G = wG gens0 wordY := by unfold y0G; rfl

theorem fG_def : fG = wG gens0 wordF := by unfold fG; rfl

theorem nG_def : nG = wG gens0 wordN := by unfold nG; rfl

theorem rep_tabA (h : tabCheck = true) : Rep deg tabA AG := by
  have := rep_gens1 h 0 (by norm_num)
  simpa [gens1, tabA] using this

theorem rep_tabB (h : tabCheck = true) : Rep deg tabB BG := by
  have := rep_gens1 h 1 (by norm_num)
  simpa [gens1, tabB] using this

theorem rep_R0 (h : tabCheck = true) : Rep deg tabR0 R0G :=
  rep_yWord h _ fun l hl => by
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact letterZ_mem l'

theorem rep_cinv (h : tabCheck = true) : Rep deg invs0[0]! cG⁻¹ := by
  have h1 := invOK_level0 h 0 (by norm_num)
  rw [tabs0_zero] at h1
  exact Rep.inv_of_invOK (rep_cG h) h1

theorem rep_word0 (h : tabCheck = true) (w : List ℤ) (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) :
    Rep deg (wT tabs0 invs0 w) (wG gens0 w) :=
  rep_wT (invs := invs0) (rep_gens0 h) (invOK_level0 h) w hw

theorem rep_word1 (h : tabCheck = true) (w : List ℤ) (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) :
    Rep deg (wT tabs1 invs1 w) (wG gens1 w) :=
  rep_wT (invs := invs1) (rep_gens1 h) (tabCheck_spec h).2.2.1 w hw

theorem structCheck_spec (hs : structCheck = true) :
    invOK deg tabR0 tabX = true ∧ tabR0 ≠ idT deg ∧
      compT deg tabR0 (compT deg tabR0 tabR0) = idT deg ∧ tabs2[5]! = tabA ∧
      tabB = compT deg (wT tabs2 invs2 (mclSurjB.map letterZ)) (compT deg tabX tabX) ∧
      wT tabs0 invs0 wordX = tabX ∧ dT = wT tabs1 invs1 wordD ∧
      compT deg cT (compT deg tabA invs0[0]!) = wT tabs1 invs1 wordCAC ∧
      compT deg cT (compT deg tabB invs0[0]!) = wT tabs1 invs1 wordCBC ∧
      compT deg cT cT = idT deg ∧ compT deg cT (compT deg tabX invs0[0]!) = tabR0 := by
  unfold structCheck at hs
  simpa only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, and_assoc, ne_eq,
    Bool.not_eq_true, beq_eq_false_iff_ne] using hs

theorem rep_X (h : tabCheck = true) (hs : structCheck = true) : Rep deg tabX xG :=
  Rep.inv_of_invOK (rep_R0 h) (structCheck_spec hs).1

theorem R0G_ne_one (h : tabCheck = true) (hs : structCheck = true) : R0G ≠ 1 :=
  ne_of_tab_ne (wT_size _ _ _) idT_size (rep_R0 h) (Rep.idT deg_lt)
    (structCheck_spec hs).2.1

theorem R0G_pow_three (h : tabCheck = true) (hs : structCheck = true) : R0G ^ 3 = 1 := by
  have h1 := Rep.compT (rep_R0 h) (Rep.compT (rep_R0 h) (rep_R0 h))
  rw [(structCheck_spec hs).2.2.1] at h1
  have := eq_of_rep h1 (Rep.idT deg_lt)
  rw [pow_three]
  simpa [mul_assoc] using this

theorem yG_five (h : tabCheck = true) (hs : structCheck = true) : yG 5 = AG := by
  have h1 := rep_yG h 5 (by norm_num)
  rw [(structCheck_spec hs).2.2.2.1] at h1
  exact eq_of_rep h1 (rep_tabA h)

theorem BG_eq (h : tabCheck = true) (hs : structCheck = true) :
    BG = wG yG (mclSurjB.map letterZ) * (xG * xG) := by
  refine eq_of_rep (rep_tabB h) ?_
  rw [(structCheck_spec hs).2.2.2.2.1]
  exact Rep.compT (rep_yWord h _ fun l hl => by
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact letterZ_mem l') (Rep.compT (rep_X h hs) (rep_X h hs))

theorem dG_eq (h : tabCheck = true) (hs : structCheck = true) : dG = wG gens1 wordD := by
  refine eq_of_rep (rep_dG h) ?_
  rw [(structCheck_spec hs).2.2.2.2.2.2.1]
  exact rep_word1 h _ (decodeWord_mem _)

theorem cAc_eq (h : tabCheck = true) (hs : structCheck = true) :
    cG * (AG * cG⁻¹) = wG gens1 wordCAC := by
  refine eq_of_rep (Rep.compT (rep_cG h) (Rep.compT (rep_tabA h) (rep_cinv h))) ?_
  rw [(structCheck_spec hs).2.2.2.2.2.2.2.1]
  exact rep_word1 h _ (decodeWord_mem _)

theorem cBc_eq (h : tabCheck = true) (hs : structCheck = true) :
    cG * (BG * cG⁻¹) = wG gens1 wordCBC := by
  refine eq_of_rep (Rep.compT (rep_cG h) (Rep.compT (rep_tabB h) (rep_cinv h))) ?_
  rw [(structCheck_spec hs).2.2.2.2.2.2.2.2.1]
  exact rep_word1 h _ (decodeWord_mem _)

theorem cG_sq (h : tabCheck = true) (hs : structCheck = true) : cG * cG = 1 := by
  have h1 := Rep.compT (rep_cG h) (rep_cG h)
  rw [(structCheck_spec hs).2.2.2.2.2.2.2.2.2.1] at h1
  exact eq_of_rep h1 (Rep.idT deg_lt)

theorem cG_xG (h : tabCheck = true) (hs : structCheck = true) :
    cG * (xG * cG⁻¹) = xG⁻¹ := by
  have h1 := Rep.compT (rep_cG h) (Rep.compT (rep_X h hs) (rep_cinv h))
  rw [(structCheck_spec hs).2.2.2.2.2.2.2.2.2.2] at h1
  exact eq_of_rep h1 (by simpa [xG] using rep_R0 h)

theorem xword_eq (h : tabCheck = true) (hs : structCheck = true) : wG gens0 wordX = xG := by
  refine eq_of_rep ?_ (rep_X h hs)
  rw [← (structCheck_spec hs).2.2.2.2.2.1]
  exact rep_word0 h _ (decodeWord_mem _)

theorem mem_invW {w : List ℤ} {l : ℤ} (hl : l ∈ invW w) : -l ∈ w := by
  simp only [invW, List.mem_reverse, List.mem_map] at hl
  obtain ⟨a, ha, rfl⟩ := hl
  simpa using ha

theorem rep_inv_word0 (h : tabCheck = true) {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) :
    Rep deg (wT tabs0 invs0 (invW w)) (wG gens0 w)⁻¹ := by
  rw [← wG_invW gens0 (fun l hl => (hw l hl).1)]
  refine rep_word0 h _ fun l hl => ?_
  have := hw (-l) (mem_invW hl)
  simpa using this

theorem rep_tabYw (h : tabCheck = true) : Rep deg tabYw y0G :=
  rep_word0 h wordY (decodeWord_mem _)

theorem rep_tabF (h : tabCheck = true) : Rep deg tabF fG :=
  rep_word0 h wordF (decodeWord_mem _)

theorem rep_tabN (h : tabCheck = true) : Rep deg tabN nG :=
  rep_word0 h wordN (decodeWord_mem _)

theorem rep_tabNinv (h : tabCheck = true) : Rep deg (wT tabs0 invs0 (invW wordN)) nG⁻¹ :=
  rep_inv_word0 h (decodeWord_mem _)

theorem cp1Check_spec (hc : cp1Check = true) :
    compT deg tabYw tabX = compT deg tabX tabYw ∧
      compT deg tabYw (compT deg tabYw tabYw) = idT deg ∧ tabYw ≠ idT deg ∧
      compT deg tabYw tabYw ≠ tabR0 ∧ tabYw ≠ tabR0 ∧ powT deg 5 tabF = idT deg ∧
      tabF ≠ idT deg ∧ compT deg tabF tabYw = compT deg tabYw tabF ∧
      compT deg tabN (compT deg tabYw (wT tabs0 invs0 (invW wordN))) = tabYw ∧
      compT deg tabN (compT deg tabX (wT tabs0 invs0 (invW wordN))) = tabR0 := by
  unfold cp1Check at hc
  simpa only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, and_assoc, ne_eq,
    Bool.not_eq_true, beq_eq_false_iff_ne] using hc

theorem cp1_facts (h : tabCheck = true) (hs : structCheck = true) (hc : cp1Check = true) :
    y0G * xG = xG * y0G ∧ y0G ^ 3 = 1 ∧ y0G ≠ 1 ∧ y0G * y0G ≠ R0G ∧ y0G ≠ R0G ∧
      fG ^ 5 = 1 ∧ fG ≠ 1 ∧ fG * y0G = y0G * fG ∧
      nG * (y0G * nG⁻¹) = y0G ∧ nG * (xG * nG⁻¹) = xG⁻¹ := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := cp1Check_spec hc
  have rY := rep_tabYw h
  have rX := rep_X h hs
  have rR := rep_R0 h
  have rF := rep_tabF h
  have rN := rep_tabN h
  have rNi := rep_tabNinv h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have r1 : Rep deg (compT deg tabYw tabX) (y0G * xG) := Rep.compT rY rX
    have r2 : Rep deg (compT deg tabX tabYw) (xG * y0G) := Rep.compT rX rY
    rw [c1] at r1
    exact eq_of_rep r1 r2
  · have := eq_of_rep (Rep.compT rY (Rep.compT rY rY)) (c2 ▸ Rep.idT deg_lt)
    rw [pow_three]
    simpa [mul_assoc] using this
  · exact ne_of_tab_ne (wT_size _ _ _) idT_size rY (Rep.idT deg_lt) c3
  · exact ne_of_tab_ne (compT_size _ _) (wT_size _ _ _) (Rep.compT rY rY) rR c4
  · exact ne_of_tab_ne (wT_size _ _ _) (wT_size _ _ _) rY rR c5
  · have := eq_of_rep (Rep.powT deg_lt rF 5) (c6 ▸ Rep.idT deg_lt)
    simpa using this
  · exact ne_of_tab_ne (wT_size _ _ _) idT_size rF (Rep.idT deg_lt) c7
  · have r1 : Rep deg (compT deg tabF tabYw) (fG * y0G) := Rep.compT rF rY
    have r2 : Rep deg (compT deg tabYw tabF) (y0G * fG) := Rep.compT rY rF
    rw [c8] at r1
    exact eq_of_rep r1 r2
  · have r1 := Rep.compT rN (Rep.compT rY rNi)
    rw [c9] at r1
    exact eq_of_rep r1 rY
  · have r1 := Rep.compT rN (Rep.compT rX rNi)
    rw [c10] at r1
    exact eq_of_rep r1 (by simpa [xG] using rR)

noncomputable def gcG : Perm (Fin deg) := wG gens0 wordConj

noncomputable def w0G : Perm (Fin deg) := wG gens0 wordW

noncomputable def gG : Perm (Fin deg) := wG gens0 wordGg

noncomputable def uG (j : ℕ) : Perm (Fin deg) := wG gens0 (uWords.getD j [])

noncomputable def t0G : Perm (Fin deg) := wG gens0 wordT0

theorem gcG_def : gcG = wG gens0 wordConj := by unfold gcG; rfl

theorem w0G_def : w0G = wG gens0 wordW := by unfold w0G; rfl

theorem gG_def : gG = wG gens0 wordGg := by unfold gG; rfl

theorem uG_def (j : ℕ) : uG j = wG gens0 (uWords.getD j []) := by unfold uG; rfl

theorem t0G_def : t0G = wG gens0 wordT0 := by unfold t0G; rfl

theorem mem_wordW {l : ℤ} (hl : l ∈ wordW) : l ≠ 0 ∧ l.natAbs ≤ 2 := by
  simp only [wordW, List.mem_append] at hl
  rcases hl with (hl | hl) | hl
  · exact decodeWord_mem _ l hl
  · have := decodeWord_mem _ (-l) (mem_invW hl)
    simpa using this
  · have := decodeWord_mem _ (-l) (mem_invW hl)
    simpa using this

theorem w0G_eq : w0G = gcG * y0G⁻¹ * gcG⁻¹ := by
  have hY : ∀ l ∈ wordY, l ≠ 0 := fun l hl => (decodeWord_mem _ l hl).1
  have hC : ∀ l ∈ wordConj, l ≠ 0 := fun l hl => (decodeWord_mem _ l hl).1
  rw [w0G_def, wordW, wG_append, wG_append, gcG_def, y0G_def, wG_invW gens0 hY,
    wG_invW gens0 hC]

theorem rep_tabW (h : tabCheck = true) : Rep deg tabW w0G := by
  rw [w0G_def]
  exact rep_word0 h wordW fun l hl => mem_wordW hl

theorem rep_tabWinv (h : tabCheck = true) : Rep deg tabWinv w0G⁻¹ := by
  rw [w0G_def]
  exact rep_inv_word0 h fun l hl => mem_wordW hl

theorem rep_tabYinv (h : tabCheck = true) : Rep deg tabYinv y0G⁻¹ := by
  rw [y0G_def]
  exact rep_inv_word0 h (decodeWord_mem _)

theorem rep_tabG (h : tabCheck = true) : Rep deg tabG gG := by
  rw [gG_def]
  exact rep_word0 h wordGg (decodeWord_mem _)

theorem rep_tabGinv (h : tabCheck = true) :
    Rep deg (wT tabs0 invs0 (invW wordGg)) gG⁻¹ := by
  rw [gG_def]
  exact rep_inv_word0 h (decodeWord_mem _)

theorem uWords_mem : ∀ j < 4, ∀ l ∈ uWords.getD j [], l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro j hj l hl
  interval_cases j <;> simp [uWords] at hl <;> exact decodeWord_mem _ l hl

theorem rep_uTabs (h : tabCheck = true) {j : ℕ} (hj : j < 4) :
    Rep deg uTabs[j]! (uG j) := by
  rw [uG_def]
  have e : uTabs[j]! = wT tabs0 invs0 (uWords.getD j []) := by
    interval_cases j <;> simp [uTabs, uWords]
  rw [e]
  exact rep_word0 h _ (uWords_mem j hj)

theorem rep_uInvTabs (h : tabCheck = true) {j : ℕ} (hj : j < 4) :
    Rep deg uInvTabs[j]! (uG j)⁻¹ := by
  rw [uG_def]
  have e : uInvTabs[j]! = wT tabs0 invs0 (invW (uWords.getD j [])) := by
    interval_cases j <;> simp [uInvTabs, uWords]
  rw [e]
  exact rep_inv_word0 h (uWords_mem j hj)

theorem invCheck_spec (h : tabCheck = true) (hs : structCheck = true) (hi : invCheck = true) :
    gG * (xG * gG⁻¹) = xG⁻¹ ∧ (gG * (y0G * gG⁻¹) = y0G ∨ gG * (y0G * gG⁻¹) = y0G⁻¹) ∧
      (gG * (w0G * gG⁻¹) = w0G ∨ gG * (w0G * gG⁻¹) = w0G⁻¹) ∧
      ∀ j < 4, uG j * (y0G * (uG j)⁻¹) = y0G ∨ uG j * (y0G * (uG j)⁻¹) = y0G⁻¹ := by
  unfold invCheck at hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hi
  obtain ⟨⟨⟨i1, i2⟩, i3⟩, i4⟩ := hi
  have rG := rep_tabG h
  have rGi := rep_tabGinv h
  have rY := rep_tabYw h
  have rW := rep_tabW h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have r1 := Rep.compT rG (Rep.compT (rep_X h hs) rGi)
    rw [i1] at r1
    exact eq_of_rep r1 (by simpa [xG_def] using rep_R0 h)
  · have r1 := Rep.compT rG (Rep.compT rY rGi)
    rcases i2 with i2 | i2
    · rw [i2] at r1; exact Or.inl (eq_of_rep r1 rY)
    · rw [i2] at r1; exact Or.inr (eq_of_rep r1 (rep_tabYinv h))
  · have r1 := Rep.compT rG (Rep.compT rW rGi)
    rcases i3 with i3 | i3
    · rw [i3] at r1; exact Or.inl (eq_of_rep r1 rW)
    · rw [i3] at r1; exact Or.inr (eq_of_rep r1 (rep_tabWinv h))
  · intro j hj
    have r1 := Rep.compT (rep_uTabs h hj) (Rep.compT rY (rep_uInvTabs h hj))
    rcases i4 j hj with i4 | i4
    · rw [i4] at r1; exact Or.inl (eq_of_rep r1 rY)
    · rw [i4] at r1; exact Or.inr (eq_of_rep r1 (rep_tabYinv h))

theorem rep_tabT0 (h : tabCheck = true) : Rep deg tabT0 t0G := by
  rw [t0G_def]
  exact rep_word0 h wordT0 (decodeWord_mem _)

theorem markCheck_spec (hm : markCheck = true) :
    compT deg tabT0 tabT0 = idT deg ∧ tabT0 ≠ idT deg ∧
      compT deg tabT0 tabX = compT deg tabX tabT0 ∧
      compT deg tabT0 tabYw = compT deg tabYw tabT0 ∧
      compT deg tabT0 tabW = compT deg tabW tabT0 := by
  unfold markCheck at hm
  simpa only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, and_assoc, ne_eq,
    Bool.not_eq_true, beq_eq_false_iff_ne] using hm

theorem mark_facts (h : tabCheck = true) (hs : structCheck = true) (hm : markCheck = true) :
    t0G * t0G = 1 ∧ t0G ≠ 1 ∧ t0G * xG = xG * t0G ∧ t0G * y0G = y0G * t0G ∧
      t0G * w0G = w0G * t0G := by
  obtain ⟨m1, m2, m3, m4, m5⟩ := markCheck_spec hm
  have rT := rep_tabT0 h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have r1 : Rep deg (compT deg tabT0 tabT0) (t0G * t0G) := Rep.compT rT rT
    rw [m1] at r1
    exact eq_of_rep r1 (Rep.idT deg_lt)
  · exact ne_of_tab_ne (wT_size _ _ _) idT_size rT (Rep.idT deg_lt) m2
  · have r1 : Rep deg (compT deg tabT0 tabX) (t0G * xG) := Rep.compT rT (rep_X h hs)
    have r2 : Rep deg (compT deg tabX tabT0) (xG * t0G) := Rep.compT (rep_X h hs) rT
    rw [m3] at r1
    exact eq_of_rep r1 r2
  · have r1 : Rep deg (compT deg tabT0 tabYw) (t0G * y0G) := Rep.compT rT (rep_tabYw h)
    have r2 : Rep deg (compT deg tabYw tabT0) (y0G * t0G) := Rep.compT (rep_tabYw h) rT
    rw [m4] at r1
    exact eq_of_rep r1 r2
  · have r1 : Rep deg (compT deg tabT0 tabW) (t0G * w0G) := Rep.compT rT (rep_tabW h)
    have r2 : Rep deg (compT deg tabW tabT0) (w0G * t0G) := Rep.compT (rep_tabW h) rT
    rw [m5] at r1
    exact eq_of_rep r1 r2

end CFSG.Sporadic.Recognition.LyonsSims.Ly0
