module

public import CFSG.Sporadic.SuzRecog.B0GluingCert
public import CFSG.Sporadic.SuzRecog.C1ModelT0

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.B0Gluing

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzRecog.B0GluingData

@[expose] noncomputable def tE (k : ℕ) : Equiv.Perm (Fin 1782) :=
  Classical.epsilon fun g : Equiv.Perm (Fin 1782) => TabRep ttabs[k]! g

@[expose] noncomputable def z2 : Equiv.Perm (Fin 1782) :=
  t0Gen 0 * t0Gen 3 * (t0Gen 0)⁻¹ * (t0Gen 3)⁻¹

@[expose] def gR (k : ℕ) : Equiv.Perm (Fin 42) :=
  if k = 0 then g₁ else if k = 1 then g₂ else if k = 2 then g₃ else if k = 3 then g₄
  else if k = 4 then g₅ else g₆

@[expose] def thetaR (i : ℕ) : Equiv.Perm (Fin 42) := ((thetaWords.getD i []).map gR).prod

section Pos


theorem ttabs_size : ttabs.size = 64 := t0_parts.2.1

theorem tabRep_tE {k : ℕ} (hk : k < 64) : TabRep ttabs[k]! (tE k) := by
  obtain ⟨g, -, hr⟩ := enumerates_T0.exists_elt (k := k) (by rw [t0_parts.2.1]; exact hk)
  exact Classical.epsilon_spec (p := fun g : Equiv.Perm (Fin 1782) => TabRep ttabs[k]! g) ⟨g, hr⟩

theorem tE_mem {k : ℕ} (hk : k < 64) : tE k ∈ T0 := by
  obtain ⟨g, hg, hr⟩ := enumerates_T0.exists_elt (k := k) (by rw [t0_parts.2.1]; exact hk)
  rwa [(tabRep_tE hk).perm_eq hr]

theorem exists_tE {x : Equiv.Perm (Fin 1782)} (hx : x ∈ T0) : ∃ k < 64, tE k = x := by
  obtain ⟨k, hk, hr⟩ := enumerates_T0.exists_pos hx
  rw [t0_parts.2.1] at hk
  exact ⟨k, hk, (tabRep_tE hk).perm_eq hr⟩

theorem tE_inj {k k' : ℕ} (hk : k < 64) (hk' : k' < 64) (h : tE k = tE k') : k = k' :=
  enumerates_T0.pos_unique (by rw [t0_parts.2.1]; exact hk) (by rw [t0_parts.2.1]; exact hk')
    (tabRep_tE hk) (by rw [h]; exact tabRep_tE hk')

theorem tE_eq_of_rep {k : ℕ} (hk : k < 64) {t : Tab} (ht : ttabs[k]! = t)
    {g : Equiv.Perm (Fin 1782)} (hg : Rep 1782 t g) : tE k = g := by
  have h : Rep 1782 t (tE k) := by
    rw [← ht]
    exact (tabRep_tE hk).2
  exact h.unique hg

theorem tFound_spec {x : Tab} (h : tFound x = true) : tPos x < 64 ∧ ttabs[tPos x]! = x := by
  simpa only [tFound, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using h

theorem idx_parts :
    (∀ a < 64, ∀ b < 64, mulP a b < 64 ∧ ttabs[mulP a b]! = comp 1782 ttabs[a]! ttabs[b]!) ∧
    tFound (idTab 1782) = true ∧ oneI = 0 ∧ (∀ i < 4, tFound t0Tabs[i]! = true) ∧
    tFound tTab = true ∧ (∀ a < 64, invP a < 64 ∧ mulP a (invP a) = oneI) ∧
    (∀ i < 4, mulP (gP i) (gP i) = oneI) ∧ cmP (gP 0) (gP 1) = oneI ∧
    cmP (gP 2) (gP 3) = oneI ∧ cmP (gP 0) (gP 2) = cmP (gP 1) (gP 3) ∧
    mulP (mulP (cmP (gP 0) (gP 3)) (cmP (gP 1) (gP 2))) (cmP (gP 0) (gP 2)) = oneI ∧
    (∀ a < 64, mulP zI[2]! a = mulP a zI[2]!) ∧ mulP zI[2]! zI[2]! = oneI ∧
    (∀ v < 15, (chiIs[v]!)[0]! = 0 ∧
      (∀ k < 64, k = 0 ∨ (chiIs[v]!)[k]! =
        (chiBit v t0Enum.lab[k]! + (chiIs[v]!)[t0Enum.par[k]!]!) % 2) ∧
      (∀ a < 64, ∀ b < 64, (chiIs[v]!)[mulP a b]! = ((chiIs[v]!)[a]! + (chiIs[v]!)[b]!) % 2) ∧
      ∃ i < 4, (chiIs[v]!)[gP i]! = 1) ∧
    (∀ r < 16, (gammaIs[r]!)[0]! = oneI ∧
      (∀ k < 64, k = 0 ∨ (gammaIs[r]!)[k]! =
        mulP (gammaGen r t0Enum.lab[k]!) (gammaIs[r]!)[t0Enum.par[k]!]!) ∧
      ∀ k < 64, (gammaInvIs[r]!)[k]! < 64 ∧ (gammaIs[r]!)[(gammaInvIs[r]!)[k]!]! = k) := by
  have h := b0Idx_check
  simp only [idxCheck, Bool.and_eq_true, Bool.or_eq_true, allBelow_eq_true, anyBelow_eq_true,
    beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, fun v hv => ?_,
    fun r hr => ?_⟩
  · obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h14 v hv
    exact ⟨a, b, c, d⟩
  · obtain ⟨⟨a, b⟩, c⟩ := h15 r hr
    exact ⟨a, b, c⟩

theorem tE_mulP {a b : ℕ} (ha : a < 64) (hb : b < 64) :
    mulP a b < 64 ∧ tE (mulP a b) = tE a * tE b := by
  obtain ⟨h1, h2⟩ := idx_parts.1 a ha b hb
  refine ⟨h1, (tabRep_tE h1).perm_eq ?_⟩
  rw [h2]
  exact (tabRep_tE ha).comp (tabRep_tE hb)

theorem oneI_eq : oneI = 0 := idx_parts.2.2.1

theorem tE_oneI : oneI < 64 ∧ tE oneI = 1 := by
  obtain ⟨h1, h2⟩ := tFound_spec idx_parts.2.1
  have hrep : TabRep ttabs[tPos (idTab 1782)]! (1 : Equiv.Perm (Fin 1782)) := by
    rw [h2]
    exact TabRep.idTab
  exact ⟨h1, (tabRep_tE h1).perm_eq hrep⟩

theorem tE_zero : tE 0 = 1 := by
  rw [← oneI_eq]
  exact tE_oneI.2

theorem tE_invP {a : ℕ} (ha : a < 64) : invP a < 64 ∧ tE (invP a) = (tE a)⁻¹ := by
  obtain ⟨h1, h2⟩ := idx_parts.2.2.2.2.2.1 a ha
  refine ⟨h1, (eq_inv_of_mul_eq_one_right ?_)⟩
  rw [← (tE_mulP ha h1).2, h2, tE_oneI.2]

theorem cmP_eq {a b : ℕ} (ha : a < 64) (hb : b < 64) :
    cmP a b = mulP (mulP a b) (mulP (invP a) (invP b)) := by
  unfold cmP cmI
  rw [getElem!_ofFn' _ ha, getElem!_ofFn' _ hb]

theorem tE_cmP {a b : ℕ} (ha : a < 64) (hb : b < 64) :
    cmP a b < 64 ∧ tE (cmP a b) = tE a * tE b * (tE a)⁻¹ * (tE b)⁻¹ := by
  have hab := tE_mulP ha hb
  have hai := tE_invP ha
  have hbi := tE_invP hb
  have hi := tE_mulP hai.1 hbi.1
  have h := tE_mulP hab.1 hi.1
  rw [cmP_eq ha hb]
  refine ⟨h.1, ?_⟩
  rw [h.2, hab.2, hi.2, hai.2, hbi.2]
  group

theorem gP_spec {i : ℕ} (hi : i < 4) : gP i < 64 ∧ tE (gP i) = t0Gen i := by
  obtain ⟨h1, h2⟩ := tFound_spec (idx_parts.2.2.2.1 i hi)
  exact ⟨h1, tE_eq_of_rep h1 (h2.trans (t0Tabs_get hi)) (tabRep_t0Tab hi).2⟩

theorem t1Pos_spec : tPos tTab < 64 ∧ tE (tPos tTab) = suzInv 1 := by
  obtain ⟨h1, h2⟩ := tFound_spec idx_parts.2.2.2.2.1
  exact ⟨h1, tE_eq_of_rep h1 h2 rep_tTab⟩

theorem getElem!_quad_zero {α : Type} [Inhabited α] (a b c d : α) :
    (#[a, b, c, d] : Array α)[0]! = a := rfl

theorem getElem!_quad_one {α : Type} [Inhabited α] (a b c d : α) :
    (#[a, b, c, d] : Array α)[1]! = b := rfl

theorem getElem!_quad_two {α : Type} [Inhabited α] (a b c d : α) :
    (#[a, b, c, d] : Array α)[2]! = c := rfl

theorem getElem!_quad_three {α : Type} [Inhabited α] (a b c d : α) :
    (#[a, b, c, d] : Array α)[3]! = d := rfl

theorem zI_zero : zI[0]! = oneI := getElem!_quad_zero _ _ _ _

theorem zI_one : zI[1]! = tPos tTab := getElem!_quad_one _ _ _ _

theorem zI_two : zI[2]! = cmP (gP 0) (gP 3) := getElem!_quad_two _ _ _ _

theorem zI_three : zI[3]! = mulP (cmP (gP 0) (gP 3)) (tPos tTab) := getElem!_quad_three _ _ _ _

theorem zI_spec2 : zI[2]! < 64 ∧ tE zI[2]! = z2 := by
  rw [zI_two]
  have h := tE_cmP (gP_spec (i := 0) (by norm_num)).1 (gP_spec (i := 3) (by norm_num)).1
  refine ⟨h.1, ?_⟩
  rw [h.2, (gP_spec (i := 0) (by norm_num)).2, (gP_spec (i := 3) (by norm_num)).2]
  rfl

theorem zI_spec3 : zI[3]! < 64 ∧ tE zI[3]! = z2 * suzInv 1 := by
  rw [zI_three, ← zI_two]
  have h := tE_mulP zI_spec2.1 t1Pos_spec.1
  exact ⟨h.1, by rw [h.2, zI_spec2.2, t1Pos_spec.2]⟩

theorem zI_spec {j : ℕ} (hj : j < 4) :
    zI[j]! < 64 ∧ (tE zI[j]! = 1 ∨ tE zI[j]! = suzInv 1 ∨ tE zI[j]! = z2 ∨
      tE zI[j]! = z2 * suzInv 1) := by
  interval_cases j
  · rw [zI_zero]
    exact ⟨tE_oneI.1, Or.inl tE_oneI.2⟩
  · rw [zI_one]
    exact ⟨t1Pos_spec.1, Or.inr (Or.inl t1Pos_spec.2)⟩
  · exact ⟨zI_spec2.1, Or.inr (Or.inr (Or.inl zI_spec2.2))⟩
  · exact ⟨zI_spec3.1, Or.inr (Or.inr (Or.inr zI_spec3.2))⟩

theorem z2_mem_T0 : z2 ∈ T0 := zI_spec2.2 ▸ tE_mem zI_spec2.1

theorem z2_comm {x : Equiv.Perm (Fin 1782)} (hx : x ∈ T0) : z2 * x = x * z2 := by
  obtain ⟨a, ha, rfl⟩ := exists_tE hx
  have h := idx_parts.2.2.2.2.2.2.2.2.2.2.2.1 a ha
  rw [← zI_spec2.2, ← (tE_mulP zI_spec2.1 ha).2, ← (tE_mulP ha zI_spec2.1).2, h]

theorem z2_mul_self : z2 * z2 = 1 := by
  rw [← zI_spec2.2, ← (tE_mulP zI_spec2.1 zI_spec2.1).2,
    idx_parts.2.2.2.2.2.2.2.2.2.2.2.2.1, tE_oneI.2]

theorem tauZ_parts :
    tFound (conjTab 1782 tauT tauT ttabs[zI[2]!]!) = true ∧
      tPos (conjTab 1782 tauT tauT ttabs[zI[2]!]!) = zI[3]! ∧
      comp 1782 tTab C1Model.zT ≠ comp 1782 C1Model.zT tTab := by
  have h := b0TauZ_check
  simp only [tauZCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem tau0_conj_z2 : tau0 * z2 * tau0⁻¹ = z2 * suzInv 1 := by
  obtain ⟨h1, h2⟩ := tFound_spec tauZ_parts.1
  have hinv : tau0⁻¹ = tau0 := inv_eq_of_mul_eq_one_right tau0_mul_self
  have hrep : TabRep (conjTab 1782 tauT tauT ttabs[zI[2]!]!) (tau0 * tE zI[2]! * tau0⁻¹) :=
    tabRep_tau0.conjTab (tabRep_tE zI_spec2.1) (by rw [hinv]; exact tabRep_tau0)
  have hrep' : TabRep ttabs[tPos (conjTab 1782 tauT tauT ttabs[zI[2]!]!)]!
      (tau0 * tE zI[2]! * tau0⁻¹) := by
    rw [h2]
    exact hrep
  rw [← zI_spec3.2, ← zI_spec2.2, ← tauZ_parts.2.1]
  exact ((tabRep_tE h1).perm_eq hrep').symm

theorem suzInv_one_not_comm_zJ0 : suzInv 1 * zJ0 ≠ zJ0 * suzInv 1 := fun h =>
  tauZ_parts.2.2 (((tabRep_comp' rep_tTab tabRep_zJ0.2).eq_iff
    (tabRep_comp' tabRep_zJ0.2 rep_tTab)).mpr h)

theorem rtabs_get {k : ℕ} (hk : k < 64) : rtabs[k]! = resTab ttabs[k]! := by
  have hk' : k < ttabs.size := by rw [ttabs_size]; exact hk
  unfold rtabs
  rw [getElem!_pos _ k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
    getElem!_pos ttabs k hk']

theorem tabRep_rtabs {k : ℕ} (hk : k < 64) :
    TabRep rtabs[k]! (resW0 ⟨tE k, T0_le_centralizer_w0 (tE_mem hk)⟩) :=
  rtabs_get hk ▸ tabRep_resTab (tabRep_tE hk).2

theorem tabRep_p0Gens {i : ℕ} (hi : i < 4) :
    TabRep p0Gens[i]! (resW0 ⟨t0Gen i, T0_le_centralizer_w0 (t0Gen_mem_T0 hi)⟩) := by
  rw [show p0Gens[i]! = resTab t0Tabs[i]! from getElem!_ofFn' _ hi, t0Tabs_get hi]
  exact tabRep_resTab (tabRep_t0Tab hi).2

@[expose] def repImg (G : ℕ → ℕ) (m : ℕ) : List ℕ := (List.range m).map fun i => G (cReps.getD i 0)

theorem repImg_length (G : ℕ → ℕ) (m : ℕ) : (repImg G m).length = m := by simp [repImg]

theorem repImg_getD {G : ℕ → ℕ} {m j : ℕ} (hj : j < m) :
    (repImg G m).getD j 0 = G (cReps.getD j 0) := by
  simp [repImg, List.getD_eq_getElem?_getD, hj]

theorem repImg_succ (G : ℕ → ℕ) (m : ℕ) :
    repImg G (m + 1) = repImg G m ++ [G (cReps.getD m 0)] := by
  simp [repImg, List.range_succ]

theorem cReps_lt {m : ℕ} (hm : m < 6) : cReps.getD m 0 < 42 := by
  interval_cases m <;> decide

theorem cPar_lt {m : ℕ} (hm : m < 6) (h0 : m ≠ 0) : cPar.getD m 0 < m := by
  interval_cases m <;> simp_all <;> decide

theorem cPar_adj {m : ℕ} (hm : m < 6) (h0 : m ≠ 0) :
    eAdj (cReps.getD (cPar.getD m 0) 0) (cReps.getD m 0) = true := by
  interval_cases m <;> simp_all <;> decide

theorem cSearch_leaf {P Z : ℕ → ℕ → ℕ} {G : ℕ → ℕ} (hGl : ∀ y < 42, G y < 42)
    (hstab : ∀ m < 6, stabOK P (cReps.getD m 0) (G (cReps.getD m 0)) = true)
    (hadj : ∀ x y, eAdj x y = true → eAdj (G x) (G y) = true) :
    ∀ f m, f + m = 6 → cSearch P Z f (repImg G m) = true → cLeaf P Z (repImg G 6) = true
  | 0, m, h, hs => by
    rw [show m = 6 by omega] at hs
    exact hs
  | f + 1, m, h, hs => by
    have hm : m < 6 := by omega
    have hc : G (cReps.getD m 0) ∈ cCands (repImg G m) := by
      unfold cCands
      rw [repImg_length]
      by_cases h0 : m = 0
      · rw [if_pos h0]
        exact List.mem_range.2 (hGl _ (cReps_lt hm))
      · rw [if_neg h0, repImg_getD (cPar_lt hm h0)]
        have := hadj _ _ (cPar_adj hm h0)
        simpa [eAdj] using this
    rw [cSearch, List.all_eq_true] at hs
    have := hs _ hc
    rw [repImg_length, hstab m hm, Bool.not_true, Bool.false_or, ← repImg_succ] at this
    exact cSearch_leaf hGl hstab hadj f (m + 1) (by omega) this

theorem wordAt_cons (P : ℕ → ℕ → ℕ) (k : ℕ) (w : List ℕ) (y : ℕ) :
    wordAt P (k :: w) y = P k (wordAt P w y) := by
  simp [wordAt]

@[expose] def p0F (k y : ℕ) : ℕ := (p0Gens[k]!)[y]!

theorem wordAt_comm {G : ℕ → ℕ} (hP : ∀ k < 4, ∀ y < 42, p0F k y < 42)
    (hGl : ∀ y < 42, G y < 42) (hGc : ∀ k < 4, ∀ y < 42, G (p0F k y) = p0F k (G y)) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 4) → ∀ y < 42,
      wordAt p0F w y < 42 ∧ wordAt p0F w (G y) = G (wordAt p0F w y)
  | [], _, y, hy => ⟨hy, rfl⟩
  | k :: w, hw, y, hy => by
    have hk := hw k List.mem_cons_self
    obtain ⟨h1, h2⟩ := wordAt_comm hP hGl hGc w (fun j hj => hw j (List.mem_cons_of_mem _ hj)) y hy
    rw [wordAt_cons, wordAt_cons, h2, hGc k hk _ h1]
    exact ⟨hP k hk _ h1, rfl⟩

theorem cMap_get {G : ℕ → ℕ} (hd : cDataOK p0F = true)
    (hP : ∀ k < 4, ∀ y < 42, p0F k y < 42) (hGl : ∀ y < 42, G y < 42)
    (hGc : ∀ k < 4, ∀ y < 42, G (p0F k y) = p0F k (G y)) {x : ℕ} (hx : x < 42) :
    cMap p0F (repImg G 6) x = G x := by
  simp only [cDataOK, Bool.and_eq_true, allBelow_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at hd
  obtain ⟨⟨hi, hw⟩, hx'⟩ := hd.2 x hx
  unfold cMap
  rw [repImg_getD hi, (wordAt_comm hP hGl hGc _ hw _ (cReps_lt hi)).2, hx']

theorem p0Gens_lt {k : ℕ} (hk : k < 4) {y : ℕ} (hy : y < 42) : p0F k y < 42 := by
  rw [p0F, (tabRep_p0Gens hk).apply ⟨y, hy⟩]
  exact Fin.isLt _

@[expose] def natMap (g : Equiv.Perm (Fin 42)) (x : ℕ) : ℕ := if h : x < 42 then g ⟨x, h⟩ else x

theorem natMap_lt (g : Equiv.Perm (Fin 42)) {x : ℕ} (hx : x < 42) : natMap g x < 42 := by
  rw [natMap, dif_pos hx]
  exact Fin.isLt _

theorem eNbr_lt : ∀ x : Fin 42, ∀ z ∈ eNbr.getD x.val [], z < 42 := by decide

theorem eAdj_lt {x y : ℕ} (h : eAdj x y = true) : x < 42 ∧ y < 42 := by
  unfold eAdj at h
  rcases Nat.lt_or_ge x 42 with hx | hx
  · exact ⟨hx, eNbr_lt ⟨x, hx⟩ y (List.contains_iff_mem.1 h)⟩
  · rw [List.getD_eq_default _ _ (by simp [eNbr]; omega)] at h
    simp at h

theorem eAdj_of_mem_R {g : Equiv.Perm (Fin 42)} (hg : g ∈ ComponentClassification.PSL3Four.R)
    (hE : ∀ k < 6, eInv gTabs[k]! = true) :
    ∀ x y : Fin 42, eAdj x y = eAdj (g x) (g y) := by
  have gen : ∀ k < 6, ∀ {h : Equiv.Perm (Fin 42)}, TabRep gTabs[k]! h →
      ∀ x y : Fin 42, eAdj x y = eAdj (h x) (h y) := by
    intro k hk h hr x y
    have := hE k hk
    simp only [eInv, allBelow_eq_true, beq_iff_eq] at this
    rw [this x x.2 y y.2, hr.apply x, hr.apply y]
  induction hg using Subgroup.closure_induction with
  | mem h hh =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [gen 0 (by norm_num) tabRep_g₁, gen 1 (by norm_num) tabRep_g₂,
      gen 2 (by norm_num) tabRep_g₃, gen 3 (by norm_num) tabRep_g₄,
      gen 4 (by norm_num) tabRep_g₅, gen 5 (by norm_num) tabRep_g₆]
  | one => exact fun x y => rfl
  | mul a b _ _ ha hb => exact fun x y => (hb x y).trans (ha (b x) (b y))
  | inv a _ ha =>
    intro x y
    simpa using (ha (a⁻¹ x) (a⁻¹ y)).symm

theorem centR_T0 {g : Equiv.Perm (Fin 42)}
    (hg : g ∈ ComponentClassification.PSL3Four.R)
    (hc : ∀ x (hx : x ∈ T0),
      g * (j0Equiv ⟨x, T0_le_J0 hx⟩ : Equiv.Perm (Fin 42)) =
        (j0Equiv ⟨x, T0_le_J0 hx⟩ : Equiv.Perm (Fin 42)) * g) :
    ∃ w, ∃ hw : w ∈ J0, (w = 1 ∨ w = suzInv 1 ∨ w = z2 ∨ w = z2 * suzInv 1) ∧
      g = (j0Equiv ⟨w, hw⟩ : Equiv.Perm (Fin 42)) := by
  have hcheck := b0CentR_check
  simp only [centRCheck, centRSearch, Bool.and_eq_true, allBelow_eq_true] at hcheck
  obtain ⟨⟨hE, hd⟩, hs⟩ := hcheck
  have hEg := eAdj_of_mem_R hg hE
  set G := natMap g with hG
  have hGl : ∀ y < 42, G y < 42 := fun y hy => natMap_lt g hy
  have hcomm : ∀ k (hk : k < 4), g * resW0 ⟨t0Gen k, T0_le_centralizer_w0 (t0Gen_mem_T0 hk)⟩ =
      resW0 ⟨t0Gen k, T0_le_centralizer_w0 (t0Gen_mem_T0 hk)⟩ * g := by
    intro k hk
    have hcm := hc _ (t0Gen_mem_T0 hk)
    rw [j0Equiv_apply] at hcm
    exact hcm
  have hGc : ∀ k < 4, ∀ y < 42, G (p0F k y) = p0F k (G y) := by
    intro k hk y hy
    have hr := tabRep_p0Gens hk
    have e := congrArg (fun p : Equiv.Perm (Fin 42) => (p ⟨y, hy⟩ : ℕ)) (hcomm k hk)
    simp only [Equiv.Perm.mul_apply] at e
    rw [p0F, p0F, hr.apply ⟨y, hy⟩, hG, natMap, dif_pos (Fin.isLt _), natMap, dif_pos hy,
      hr.apply (g ⟨y, hy⟩)]
    exact e
  have hadj : ∀ x y, eAdj x y = true → eAdj (G x) (G y) = true := by
    intro x y h
    obtain ⟨hx, hy⟩ := eAdj_lt h
    rw [hG, natMap, natMap, dif_pos hx, dif_pos hy, ← hEg ⟨x, hx⟩ ⟨y, hy⟩]
    exact h
  have hstab : ∀ m < 6, stabOK p0F (cReps.getD m 0) (G (cReps.getD m 0)) = true := by
    intro m hm
    simp only [stabOK, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
      beq_iff_eq]
    intro k hk
    by_cases e : p0F k (cReps.getD m 0) = cReps.getD m 0
    · right
      rw [← hGc k hk _ (cReps_lt hm), e]
    · exact Or.inl e
  have hleaf := cSearch_leaf (Z := fun j x => (zRes[j]!)[x]!) hGl hstab hadj 6 0 rfl hs
  have hcm : ∀ x < 42, cMap p0F (repImg G 6) x = G x := fun x hx =>
    cMap_get hd (fun k hk y hy => p0Gens_lt hk hy) hGl hGc hx
  have hX : (allBelow 4 fun k => allBelow 42 fun y =>
      cMap p0F (repImg G 6) (p0F k y) == p0F k (cMap p0F (repImg G 6) y)) = true := by
    simp only [allBelow_eq_true, beq_iff_eq]
    intro k hk y hy
    rw [hcm _ (p0Gens_lt hk hy), hcm y hy, hGc k hk y hy]
  have hY : eMap (cMap p0F (repImg G 6)) = true := by
    simp only [eMap, allBelow_eq_true, List.all_eq_true]
    intro x hx y hy
    have hy42 : y < 42 := eNbr_lt ⟨x, hx⟩ y hy
    rw [hcm x hx, hcm y hy42]
    exact hadj x y (List.contains_iff_mem.2 hy)
  have hO : onto42 (cMap p0F (repImg G 6)) = true := by
    simp only [onto42, allBelow_eq_true, anyBelow_eq_true, beq_iff_eq]
    intro y hy
    refine ⟨(g⁻¹ ⟨y, hy⟩ : Fin 42), Fin.isLt _, ?_⟩
    rw [hcm _ (Fin.isLt _), hG, natMap, dif_pos (Fin.isLt _)]
    simp
  have hmem : (anyBelow 4 fun j => allBelow 42 fun x =>
      cMap p0F (repImg G 6) x == (zRes[j]!)[x]!) = true := by
    have h := hleaf
    rw [cLeaf, hO, hX, hY] at h
    simpa using h
  simp only [anyBelow_eq_true, allBelow_eq_true, beq_iff_eq] at hmem
  obtain ⟨j, hj', hjt⟩ := hmem
  obtain ⟨hz, hw⟩ := zI_spec hj'
  have e : zRes[j]! = rtabs[zI[j]!]! := getElem!_ofFn' _ hj'
  have hrep : TabRep zRes[j]! g := by
    refine ⟨by rw [e]; exact (tabRep_rtabs hz).1, fun i => ?_⟩
    rw [← hjt i i.2, hcm i i.2, hG, natMap, dif_pos i.2]
  refine ⟨tE zI[j]!, T0_le_J0 (tE_mem hz), hw, ?_⟩
  rw [j0Equiv_apply]
  have hrep' : TabRep zRes[j]! (resW0 ⟨tE zI[j]!, T0_le_centralizer_w0 (tE_mem hz)⟩) := by
    rw [e]
    exact tabRep_rtabs hz
  exact hrep.perm_eq hrep'

theorem rep_gR {k : ℕ} (hk : k < 6) : Rep 42 gTabs[k]! (gR k) := by
  interval_cases k
  · exact tabRep_g₁.2
  · exact tabRep_g₂.2
  · exact tabRep_g₃.2
  · exact tabRep_g₄.2
  · exact tabRep_g₅.2
  · exact tabRep_g₆.2

theorem gR_mem (k : ℕ) :
    gR k ∈ ComponentClassification.PSL3Four.R := by
  unfold gR
  split_ifs
  exacts [S_le_R g₁_mem_S, S_le_R g₂_mem_S, S_le_R g₃_mem_S, g₄_mem_R, g₅_mem_R, g₆_mem_R]

theorem thetaR_mem (i : ℕ) :
    thetaR i ∈ ComponentClassification.PSL3Four.R :=
  wordProd_mem gR_mem _

theorem thetaWords_lt : ∀ i < 36, ∀ k ∈ thetaWords.getD i [], k < gTabs.size := by
  decide

theorem tabRep_thetaTab {i : ℕ} (hi : i < 36) : TabRep (thetaTab i) (thetaR i) :=
  tabRep_wordTab (fun _ hk => rep_gR hk) _ (thetaWords_lt i hi)

theorem theta_parts {i : ℕ} (hi : i < 36) :
    (thetaInvTab i).size = 42 ∧ comp 42 (thetaInvTab i) (thetaTab i) = idTab 42 ∧
      (∀ k < 64, (thetaPerms[i]!)[k]! < 64 ∧
        rtabs[(thetaPerms[i]!)[k]!]! = conjTab 42 (thetaTab i) (thetaInvTab i) rtabs[k]!) ∧
      ∀ k < 64, (thetaInvPerms[i]!)[k]! < 64 ∧ (thetaPerms[i]!)[(thetaInvPerms[i]!)[k]!]! = k := by
  have h := b0Theta_check
  simp only [thetaCheck, Bool.and_eq_true, allBelow_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h i hi
  exact ⟨h1, h2, h3, h4⟩

theorem theta_spec {i k : ℕ} (hi : i < 36) (hk : k < 64) :
    (thetaPerms[i]!)[k]! < 64 ∧
      resW0 ⟨tE (thetaPerms[i]!)[k]!,
          T0_le_centralizer_w0 (tE_mem ((theta_parts hi).2.2.1 k hk).1)⟩ =
        thetaR i * resW0 ⟨tE k, T0_le_centralizer_w0 (tE_mem hk)⟩ * (thetaR i)⁻¹ := by
  obtain ⟨h1, h2, h3, -⟩ := theta_parts hi
  obtain ⟨hp, he⟩ := h3 k hk
  refine ⟨hp, (tabRep_rtabs hp).perm_eq ?_⟩
  rw [he]
  exact (tabRep_thetaTab hi).conjTab (tabRep_rtabs hk) ((tabRep_thetaTab hi).inv h1 h2)

theorem t0_tree {k : ℕ} (hk : k < 64) (hk0 : 0 < k) :
    t0Enum.par[k]! < k ∧ t0Enum.lab[k]! < 4 ∧ tE k = t0Gen t0Enum.lab[k]! * tE t0Enum.par[k]! := by
  have h := t0_parts.1
  unfold enumOK at h
  obtain ⟨-, -, -, -, htree⟩ := treeOK_spec h
  obtain ⟨h1, h2, h3⟩ := htree k (by rw [t0_parts.2.1]; exact hk) hk0
  have h2' : t0Enum.lab[k]! < 4 := by simpa [t0Tabs] using h2
  refine ⟨h1, h2', (tabRep_tE hk).perm_eq ?_⟩
  have e : ttabs[k]! = comp 1782 (t0Tab t0Enum.lab[k]!) ttabs[t0Enum.par[k]!]! := by
    rw [← t0Tabs_get h2']
    exact h3
  rw [e]
  exact (tabRep_t0Tab h2').comp (tabRep_tE (h1.trans hk))

section Hom

variable {f : Equiv.Perm (Fin 1782) → Equiv.Perm (Fin 1782)}
  (hmem : ∀ x ∈ T0, f x ∈ T0) (hmul : ∀ x ∈ T0, ∀ y ∈ T0, f (x * y) = f x * f y)

include hmul in
theorem hom_one : f 1 = 1 := by
  have h := hmul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  exact (mul_eq_left.mp h.symm)

include hmul in
theorem hom_inv {x : Equiv.Perm (Fin 1782)} (hx : x ∈ T0) : f x⁻¹ = (f x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← hmul x hx x⁻¹ (inv_mem hx), mul_inv_cancel]
  exact hom_one hmul

include hmul in
theorem hom_comm {x y : Equiv.Perm (Fin 1782)} (hx : x ∈ T0) (hy : y ∈ T0) :
    f (x * y * x⁻¹ * y⁻¹) = f x * f y * (f x)⁻¹ * (f y)⁻¹ := by
  rw [hmul _ (mul_mem (mul_mem hx hy) (inv_mem hx)) _ (inv_mem hy),
    hmul _ (mul_mem hx hy) _ (inv_mem hx), hmul _ hx _ hy, hom_inv hmul hx, hom_inv hmul hy]

theorem chi_lt {v k : ℕ} (hv : v < 15) (hk : k < 64) : (chiIs[v]!)[k]! < 2 := by
  obtain ⟨h0, htree, -, -⟩ := idx_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v hv
  rcases htree k hk with rfl | h
  · rw [h0]
    norm_num
  · rw [h]
    exact Nat.mod_lt _ (by norm_num)

include hmem hmul in
theorem not_inKer (hsurj : ∀ y ∈ T0, ∃ x ∈ T0, f x = y) {a : ℕ → ℕ}
    (ha : ∀ i < 4, a i < 64 ∧ tE (a i) = f (t0Gen i)) : inKer (a 0) (a 1) (a 2) (a 3) = false := by
  by_contra hne
  rw [Bool.not_eq_false] at hne
  simp only [inKer, anyBelow_eq_true, Bool.and_eq_true, beq_iff_eq] at hne
  obtain ⟨v, hv, ⟨⟨h0, h1⟩, h2⟩, h3⟩ := hne
  obtain ⟨hc0, -, hhom, i, hi, hgi⟩ := idx_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v hv
  set ch := chiIs[v]!
  have hz : ∀ j < 4, ch[a j]! = 0 := fun j hj => by
    interval_cases j
    exacts [h0, h1, h2, h3]
  let P : Equiv.Perm (Fin 1782) → Prop := fun y => ∃ k < 64, tE k = y ∧ ch[k]! = 0
  have hP : ∀ x ∈ closure {g | ∃ i < 4, t0Gen i = g}, P (f x) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨a j, (ha j hj).1, (ha j hj).2, hz j hj⟩
    | one =>
      refine ⟨oneI, tE_oneI.1, by rw [tE_oneI.2, hom_one hmul], ?_⟩
      rw [oneI_eq]
      exact hc0
    | mul x y hx hy ihx ihy =>
      obtain ⟨kx, hkx, ex, cx⟩ := ihx
      obtain ⟨ky, hky, ey, cy⟩ := ihy
      have hm := tE_mulP hkx hky
      refine ⟨mulP kx ky, hm.1, ?_, ?_⟩
      · rw [hm.2, ex, ey, hmul x (closure_t0Gen_le_T0 hx) y (closure_t0Gen_le_T0 hy)]
      · rw [hhom kx hkx ky hky, cx, cy]
    | inv x hx ihx =>
      obtain ⟨kx, hkx, ex, cx⟩ := ihx
      have hi' := tE_invP hkx
      refine ⟨invP kx, hi'.1, by rw [hi'.2, ex, hom_inv hmul (closure_t0Gen_le_T0 hx)], ?_⟩
      have e := hhom kx hkx (invP kx) hi'.1
      rw [idx_parts.2.2.2.2.2.1 kx hkx |>.2, oneI_eq, hc0, cx, zero_add] at e
      have hlt : ch[invP kx]! < 2 := chi_lt hv hi'.1
      omega
  obtain ⟨hgP, egP⟩ := gP_spec hi
  obtain ⟨x, hx, hfx⟩ := hsurj _ (tE_mem hgP)
  rw [T0_eq] at hx
  obtain ⟨k, hk, ek, ck⟩ := hP x hx
  rw [hfx] at ek
  rw [tE_inj hk hgP ek] at ck
  rw [ck] at hgi
  exact absurd hgi (by norm_num)

theorem decompOK_spec {a b c d : ℕ} (h : decompOK a b c d = true) :
    ∃ i < 36, ∃ t < 64, ∃ r < 16, a = (thetaPerms[i]!)[ctGamma t r 0]! ∧
      b = (thetaPerms[i]!)[ctGamma t r 1]! ∧ c = (thetaPerms[i]!)[ctGamma t r 2]! ∧
      d = (thetaPerms[i]!)[ctGamma t r 3]! := by
  unfold decompOK at h
  obtain ⟨⟨i, t, r⟩, -, h⟩ := (Option.any_eq_true _ _).1 h
  simp only [decompEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hi, ht⟩, hr⟩, ha⟩, hb⟩, hc⟩, hd⟩ := h
  exact ⟨i, hi, t, ht, r, hr, ha, hb, hc, hd⟩

theorem aut_spec {a b c d : ℕ} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64)
    (haa : mulP a a = oneI) (hbb : mulP b b = oneI) (hab : cmP a b = oneI)
    (hcc : mulP c c = oneI) (hdd : mulP d d = oneI) (hcd : cmP c d = oneI)
    (hacbd : cmP a c = cmP b d) (hrel : mulP (mulP (cmP a d) (cmP b c)) (cmP a c) = oneI) :
    inKer a b c d = true ∨ decompOK a b c d = true := by
  have h := b0Aut_check
  have hp : ∀ x y, x < 64 → y < 64 → mulP x x = oneI → mulP y y = oneI → cmP x y = oneI →
      (x, y) ∈ cPairs := fun x y hx hy hxx hyy hxy => by
    simp only [cPairs, invPs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      beq_iff_eq]
    exact ⟨x, ⟨hx, hxx⟩, y, ⟨⟨hy, hyy⟩, hxy⟩, rfl⟩
  simp only [autCheck, List.all_eq_true] at h
  have h' := h _ (hp a b ha hb haa hbb hab) _ (hp c d hc hd hcc hdd hcd)
  dsimp only at h'
  have e1 : (cmP a c == cmP b d) = true := beq_iff_eq.mpr hacbd
  have e2 : (mulP (mulP (cmP a d) (cmP b c)) (cmP a c) == oneI) = true := beq_iff_eq.mpr hrel
  rw [e1, e2, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h'
  exact h'

include hmem hmul in
theorem exists_decomp (hsurj : ∀ y ∈ T0, ∃ x ∈ T0, f x = y) :
    ∃ i < 36, ∃ t < 64, ∃ r < 16, ∀ j < 4, f (t0Gen j) = tE (thetaPerms[i]!)[ctGamma t r j]! := by
  have hpos : ∀ j, ∃ k, j < 4 → k < 64 ∧ tE k = f (t0Gen j) := fun j => by
    by_cases hj : j < 4
    · obtain ⟨k, hk, e⟩ := exists_tE (hmem _ (t0Gen_mem_T0 hj))
      exact ⟨k, fun _ => ⟨hk, e⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose a ha using hpos
  have hfm : ∀ k < 64, ∀ k' < 64, f (tE (mulP k k')) = f (tE k) * f (tE k') := fun k hk k' hk' => by
    rw [(tE_mulP hk hk').2, hmul _ (tE_mem hk) _ (tE_mem hk')]
  have hfc : ∀ k < 64, ∀ k' < 64,
      f (tE (cmP k k')) = f (tE k) * f (tE k') * (f (tE k))⁻¹ * (f (tE k'))⁻¹ :=
    fun k hk k' hk' => by rw [(tE_cmP hk hk').2, hom_comm hmul (tE_mem hk) (tE_mem hk')]
  have hf1 : f (tE oneI) = 1 := by rw [tE_oneI.2, hom_one hmul]
  have hg : ∀ j < 4, gP j < 64 := fun j hj => (gP_spec hj).1
  have ha' : ∀ j < 4, a j < 64 := fun j hj => (ha j hj).1
  have hga : ∀ j < 4, f (tE (gP j)) = tE (a j) := fun j hj => by
    rw [(gP_spec hj).2, (ha j hj).2]
  have hcm : ∀ i < 4, ∀ j < 4, tE (cmP (a i) (a j)) = f (tE (cmP (gP i) (gP j))) :=
    fun i hi j hj => by
      rw [hfc _ (hg i hi) _ (hg j hj), hga i hi, hga j hj, (tE_cmP (ha' i hi) (ha' j hj)).2]
  have hcm_lt : ∀ i < 4, ∀ j < 4, cmP (a i) (a j) < 64 := fun i hi j hj =>
    (tE_cmP (ha' i hi) (ha' j hj)).1
  have hsq : ∀ j < 4, mulP (a j) (a j) = oneI := fun j hj => by
    apply tE_inj (tE_mulP (ha' j hj) (ha' j hj)).1 tE_oneI.1
    rw [(tE_mulP (ha' j hj) (ha' j hj)).2, ← hga j hj, ← hfm _ (hg j hj) _ (hg j hj),
      idx_parts.2.2.2.2.2.2.1 j hj, hf1, tE_oneI.2]
  have hc1 : ∀ i < 4, ∀ j < 4, cmP (gP i) (gP j) = oneI → cmP (a i) (a j) = oneI :=
    fun i hi j hj h => by
      apply tE_inj (hcm_lt i hi j hj) tE_oneI.1
      rw [hcm i hi j hj, h, hf1, tE_oneI.2]
  obtain ⟨-, -, -, -, -, -, -, h01, h23, h0213, hrel, -⟩ := idx_parts
  have hx : cmP (a 0) (a 2) = cmP (a 1) (a 3) := by
    apply tE_inj (hcm_lt 0 (by norm_num) 2 (by norm_num)) (hcm_lt 1 (by norm_num) 3 (by norm_num))
    rw [hcm 0 (by norm_num) 2 (by norm_num), hcm 1 (by norm_num) 3 (by norm_num), h0213]
  have hy : mulP (mulP (cmP (a 0) (a 3)) (cmP (a 1) (a 2))) (cmP (a 0) (a 2)) = oneI := by
    have h1 := tE_mulP (hcm_lt 0 (by norm_num) 3 (by norm_num))
      (hcm_lt 1 (by norm_num) 2 (by norm_num))
    have h2 := tE_mulP h1.1 (hcm_lt 0 (by norm_num) 2 (by norm_num))
    have g03 := tE_cmP (hg 0 (by norm_num)) (hg 3 (by norm_num))
    have g12 := tE_cmP (hg 1 (by norm_num)) (hg 2 (by norm_num))
    have g02 := tE_cmP (hg 0 (by norm_num)) (hg 2 (by norm_num))
    have k1 := tE_mulP g03.1 g12.1
    have k2 := tE_mulP k1.1 g02.1
    apply tE_inj h2.1 tE_oneI.1
    rw [h2.2, h1.2, hcm 0 (by norm_num) 3 (by norm_num), hcm 1 (by norm_num) 2 (by norm_num),
      hcm 0 (by norm_num) 2 (by norm_num), ← hfm _ g03.1 _ g12.1, ← hfm _ k1.1 _ g02.1, hrel, hf1,
      tE_oneI.2]
  rcases aut_spec (ha' 0 (by norm_num)) (ha' 1 (by norm_num)) (ha' 2 (by norm_num))
      (ha' 3 (by norm_num)) (hsq 0 (by norm_num)) (hsq 1 (by norm_num))
      (hc1 0 (by norm_num) 1 (by norm_num) h01) (hsq 2 (by norm_num)) (hsq 3 (by norm_num))
      (hc1 2 (by norm_num) 3 (by norm_num) h23) hx hy with h | h
  · have := not_inKer hmem hmul hsurj (a := a) ha
    rw [this] at h
    exact absurd h (by decide)
  · obtain ⟨i, hi, t, ht, r, hr, e0, e1, e2, e3⟩ := decompOK_spec h
    refine ⟨i, hi, t, ht, r, hr, fun j hj => ?_⟩
    rw [← (ha j hj).2]
    interval_cases j
    · rw [← e0]
    · rw [← e1]
    · rw [← e2]
    · rw [← e3]

theorem gammaReps_lt : ∀ r < 16, ∀ j < 4, (gammaReps.getD r []).getD j 0 < 4 := by
  decide

theorem gammaGen_lt {r j : ℕ} (hr : r < 16) (hj : j < 4) : gammaGen r j < 64 :=
  (tE_mulP (gP_spec hj).1 (zI_spec (gammaReps_lt r hr j hj)).1).1

theorem gammaIs_lt {r : ℕ} (hr : r < 16) : ∀ k < 64, (gammaIs[r]!)[k]! < 64 := by
  obtain ⟨h0, htree, -⟩ := idx_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2 r hr
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h0]
      exact tE_oneI.1
    · obtain ⟨hp, hl, -⟩ := t0_tree hk hk0
      rcases htree k hk with h | h
      · omega
      · rw [h]
        exact (tE_mulP (gammaGen_lt hr hl) (ih _ hp (hp.trans hk))).1

theorem gammaInv_spec {r k : ℕ} (hr : r < 16) (hk : k < 64) :
    (gammaInvIs[r]!)[k]! < 64 ∧ (gammaIs[r]!)[(gammaInvIs[r]!)[k]!]! = k :=
  (idx_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2 r hr).2.2 k hk

include hmul in
theorem gamma_tree {r : ℕ} (hr : r < 16) (hgen : ∀ j < 4, f (t0Gen j) = tE (gammaGen r j)) :
    ∀ k < 64, (gammaIs[r]!)[k]! < 64 ∧ f (tE k) = tE (gammaIs[r]!)[k]! := by
  obtain ⟨h0, htree, -⟩ := idx_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2 r hr
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h0, tE_zero, hom_one hmul]
      exact ⟨tE_oneI.1, tE_oneI.2.symm⟩
    · obtain ⟨hp, hl, he⟩ := t0_tree hk hk0
      obtain ⟨ih1, ih2⟩ := ih _ hp (hp.trans hk)
      rcases htree k hk with h | h
      · omega
      rw [h]
      have hm := tE_mulP (gammaGen_lt hr hl) ih1
      refine ⟨hm.1, ?_⟩
      rw [hm.2, he, hmul _ (t0Gen_mem_T0 hl) _ (tE_mem (hp.trans hk)), hgen _ hl, ih2]

end Hom

end Pos

end CFSG.Sporadic.SuzRecog.B0Gluing
