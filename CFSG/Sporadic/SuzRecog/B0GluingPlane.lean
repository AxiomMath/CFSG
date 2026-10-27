module

public import CFSG.Sporadic.SuzRecog.B0GluingAut

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.B0Gluing

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzRecog.B0GluingData

@[expose] noncomputable def jPerm (w : List ℕ) : Equiv.Perm (Fin 1782) :=
  (w.map fun k => if k = 0 then suzInv 1 else zJ0).prod

@[expose] def nWord (l : ℕ) : List ℕ :=
  [witJ1.getD 0 [], witJ2.getD 0 [], witJ1.getD 1 [], witJ2.getD 1 []].getD l []

@[expose] noncomputable def nPerm (l : ℕ) : Equiv.Perm (Fin 1782) := jPerm (nWord l)

@[expose] noncomputable def cPerm (X : ℕ) : Equiv.Perm (Fin 1782) := decPerm (witC.getD X ([], 0))

@[expose] noncomputable def r0E (ρ : ℕ) : Equiv.Perm (Fin 1782) :=
  if ρ = 0 then 1 else if ρ = 1 then Model.w0 else if ρ = 2 then r1 else r2

@[expose] noncomputable def yE (X p : ℕ) : Equiv.Perm (Fin 1782) :=
  tE (rads[X]!)[p / 4]! * r0E (p % 4)

section Plane


theorem r0E_mem_R0 (ρ : ℕ) : r0E ρ ∈ Model.R0 := by
  unfold r0E
  split_ifs
  exacts [one_mem _, w0_mem_R0, r1_mem_R0, r2_mem_R0]

theorem tabRep_r0Tabs {ρ : ℕ} (hρ : ρ < 4) : TabRep r0Tabs[ρ]! (r0E ρ) := by
  interval_cases ρ
  · rw [r0Tabs, getElem!_quad_zero]
    exact TabRep.idTab
  · rw [r0Tabs, getElem!_quad_one]
    exact tabRep_w0
  · rw [r0Tabs, getElem!_quad_two]
    exact tabRep_r1
  · rw [r0Tabs, getElem!_quad_three]
    exact tabRep_r2

theorem jPerm_mem_J0 (w : List ℕ) : jPerm w ∈ J0 :=
  wordProd_mem (fun k => by
    split_ifs
    · exact suzInv_one_mem_J0
    · exact zJ0_mem_J0) w

theorem nWord_lt : ∀ l < 4, ∀ k ∈ nWord l, k < (#[tTab, C1Model.zT] : Array Tab).size := by
  decide

theorem nTabs_get {l : ℕ} (hl : l < 4) : nTabs[l]! = jTab (nWord l) := by
  interval_cases l
  · exact getElem!_quad_zero _ _ _ _
  · exact getElem!_quad_one _ _ _ _
  · exact getElem!_quad_two _ _ _ _
  · exact getElem!_quad_three _ _ _ _

theorem tabRep_nTabs {l : ℕ} (hl : l < 4) : TabRep nTabs[l]! (nPerm l) := by
  rw [nTabs_get hl]
  exact tabRep_wordTab (fun k hk => rep_t0ConjGen hk) _ (nWord_lt l hl)

theorem nInvs_get {l : ℕ} (hl : l < 4) : nInvs[l]! = invTab 1782 nTabs[l]! := by
  have hl' : l < nTabs.size := hl
  unfold nInvs
  rw [getElem!_pos _ l (by rw [Array.size_map]; exact hl'), Array.getElem_map,
    getElem!_pos nTabs l hl']

theorem witC_ok :
    ∀ X < 2, (∀ k ∈ (witC.getD X ([], 0)).1, k < 10) ∧ (witC.getD X ([], 0)).2 < 128 := by
  decide

theorem cPerm_mem {X : ℕ} (hX : X < 2) : cPerm X ∈ invE 1 := decPerm_mem (witC_ok X hX).1

theorem cTabsW_get {X : ℕ} (hX : X < 2) : cTabsW[X]! = cTabW X := by
  interval_cases X
  · exact getElem!_pair_zero _ _
  · exact getElem!_pair_one _ _

theorem tabRep_cTabsW {X : ℕ} (hX : X < 2) : TabRep cTabsW[X]! (cPerm X) := by
  rw [cTabsW_get hX]
  exact tabRep_decTab (witC_ok X hX).1 (witC_ok X hX).2

theorem cInvsW_get {X : ℕ} (hX : X < 2) : cInvsW[X]! = invTab 1782 cTabsW[X]! := by
  have hX' : X < cTabsW.size := hX
  unfold cInvsW
  rw [getElem!_pos _ X (by rw [Array.size_map]; exact hX'), Array.getElem_map,
    getElem!_pos cTabsW X hX']

theorem y0Tabs_get {X p : ℕ} (hX : X < 2) (hp : p < 64) :
    (y0Tabs[X]!)[p]! = comp 1782 ttabs[(rads[X]!)[p / 4]!]! r0Tabs[p % 4]! := by
  have e : y0Tabs[X]! = y0TabsOf X := by
    interval_cases X
    · exact getElem!_pair_zero _ _
    · exact getElem!_pair_one _ _
  rw [e, y0TabsOf, getElem!_ofFn' _ hp]

theorem inRad_spec {X e : ℕ} (h : inRad X e = true) :
    (radIdxs[X]!)[e]! < 16 ∧ (rads[X]!)[(radIdxs[X]!)[e]!]! = e := by
  simpa only [inRad, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using h

theorem radOK_parts {X : ℕ} (h : radOK X = true) :
    (rads[X]!).size = 16 ∧ (∀ i < 16, (rads[X]!)[i]! < 64 ∧ inRad X (rads[X]!)[i]! = true) ∧
      (cInvsW[X]!).size = 1782 ∧ comp 1782 cInvsW[X]! cTabsW[X]! = idTab 1782 ∧
      (∀ p < 64, (cActs[X]!)[p]! < 64 ∧
        (y0Tabs[X]!)[(cActs[X]!)[p]!]! = conjTab 1782 cTabsW[X]! cInvsW[X]! (y0Tabs[X]!)[p]!) ∧
      inRad X oneI = true ∧ inRad X zI[1]! = true := by
  simp only [radOK, Bool.and_eq_true, allBelow_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem tabRep_y0Tabs {X p : ℕ} (hX : X < 2) (hrad : radOK X = true) (hp : p < 64) :
    TabRep (y0Tabs[X]!)[p]! (yE X p) := by
  rw [y0Tabs_get hX hp]
  exact (tabRep_tE ((radOK_parts hrad).2.1 (p / 4) (by omega)).1).comp
    (tabRep_r0Tabs (Nat.mod_lt _ (by norm_num)))

theorem yE_mem {X p : ℕ} (hrad : radOK X = true) (hp : p < 64) : yE X p ∈ invE 1 :=
  mul_mem (T0_le_invE (tE_mem ((radOK_parts hrad).2.1 (p / 4) (by omega)).1))
    (R0_le_invE (r0E_mem_R0 _))

theorem nActs_spec {l k : ℕ} (hl : l < 4) (hk : k < 64) (h : (nActs[l]!)[k]! < 64) :
    ttabs[(nActs[l]!)[k]!]! = conjTab 1782 nTabs[l]! nInvs[l]! ttabs[k]! := by
  have e : (nActs[l]!)[k]! =
      if tFound (conjTab 1782 nTabs[l]! nInvs[l]! ttabs[k]!) then
        tPos (conjTab 1782 nTabs[l]! nInvs[l]! ttabs[k]!) else 64 := by
    unfold nActs
    rw [getElem!_ofFn' _ hl, getElem!_ofFn' _ hk]
  rw [e] at h ⊢
  split_ifs at h ⊢ with hf
  · exact (tFound_spec hf).2
  · exact absurd h (lt_irrefl 64)

theorem plane_parts :
    (∀ i < 1782, (w0T[i]! == i) = (r1T[i]! == i)) ∧
    (∀ l < 4, (nInvs[l]!).size = 1782 ∧ comp 1782 nInvs[l]! nTabs[l]! = idTab 1782) ∧
    radOK 0 = true ∧ radOK 1 = true ∧
    ∀ r' < 15, witRadical.getD (r' + 1) 0 < 2 ∧
      letterOK (witRadical.getD (r' + 1) 0) (r' + 1) = true ∧
      hAct (r' + 1) (pT1 (witRadical.getD (r' + 1) 0)) = pT1 (witRadical.getD (r' + 1) 0) ∧
      ∃ i < 1782,
        ((y0Tabs[witRadical.getD (r' + 1) 0]!)[hAct (r' + 1)
          (pR0 (witRadical.getD (r' + 1) 0) 1)]!)[i]! = i ∧
        ¬ ((y0Tabs[witRadical.getD (r' + 1) 0]!)[hAct (r' + 1)
          (pR0 (witRadical.getD (r' + 1) 0) 2)]!)[i]! = i := by
  have h := b0Plane_check
  simp only [planeCheck, Bool.and_eq_true, allBelow_eq_true, anyBelow_eq_true, beq_iff_eq,
    decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun r' hr' => ?_⟩
  obtain ⟨⟨⟨hX, hl⟩, hT⟩, i, hi, ha, hb⟩ := h5 r' hr'
  exact ⟨hX, hl, hT, i, hi, ha, hb⟩

section Act

variable {G : Type*} [Group G] {Φ Ι : Equiv.Perm (Fin 1782) → G}
  (hΦmul : ∀ x ∈ invE 1, ∀ y ∈ invE 1, Φ (x * y) = Φ x * Φ y)
  (hΙmul : ∀ x ∈ J0, ∀ y ∈ J0, Ι (x * y) = Ι x * Ι y)

include hΦmul in
theorem Φ_conj {c x : Equiv.Perm (Fin 1782)} (hc : c ∈ invE 1) (hx : x ∈ invE 1) :
    Φ (c * x * c⁻¹) = Φ c * Φ x * (Φ c)⁻¹ := by
  have h1 : Φ 1 = 1 := by
    have := hΦmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact mul_eq_left.mp this.symm
  have hi : Φ c⁻¹ = (Φ c)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← hΦmul _ hc _ (inv_mem hc), mul_inv_cancel, h1]
  rw [hΦmul _ (mul_mem hc hx) _ (inv_mem hc), hΦmul _ hc _ hx, hi]

include hΙmul in
theorem Ι_conj {n x : Equiv.Perm (Fin 1782)} (hn : n ∈ J0) (hx : x ∈ J0) :
    Ι (n * x * n⁻¹) = Ι n * Ι x * (Ι n)⁻¹ := by
  have h1 : Ι 1 = 1 := by
    have := hΙmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact mul_eq_left.mp this.symm
  have hi : Ι n⁻¹ = (Ι n)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← hΙmul _ hn _ (inv_mem hn), mul_inv_cancel, h1]
  rw [hΙmul _ (mul_mem hn hx) _ (inv_mem hn), hΙmul _ hn _ hx, hi]

variable (hR : ∀ y ∈ Model.R0, ∀ x ∈ J0, Φ y * Ι x = Ι x * Φ y) {r : ℕ} (hr : r < 16)
  (hγ : ∀ k < 64, Φ (tE k) = Ι (tE (gammaIs[r]!)[k]!))

include hΦmul hΙmul hR hr hγ in
theorem jStep {X l p : ℕ} (hl : l < 4) (hrad : radOK X = true)
    (hn : (nInvs[l]!).size = 1782 ∧ comp 1782 nInvs[l]! nTabs[l]! = idTab 1782)
    (hlet : jE l r (rads[X]!)[p / 4]! < 64 ∧ inRad X (jE l r (rads[X]!)[p / 4]!) = true)
    (hp : p < 64) :
    jAct X l r p < 64 ∧
      Ι (nPerm l) * Φ (yE X p) * (Ι (nPerm l))⁻¹ = Φ (yE X (jAct X l r p)) := by
  obtain ⟨-, hE, -⟩ := radOK_parts hrad
  have hi : p / 4 < 16 := by omega
  set e := (rads[X]!)[p / 4]! with he
  have heT : e < 64 := (hE (p / 4) hi).1
  have hγe := gammaIs_lt hr e heT
  set k := (nActs[l]!)[(gammaIs[r]!)[e]!]! with hk
  have hk64 : k < 64 := by
    by_contra hk'
    have : jE l r e = 64 := by
      unfold jE
      rw [← hk, ite_eq_right hk']
    omega
  have hjE : jE l r e = (gammaInvIs[r]!)[k]! := by
    unfold jE
    rw [← hk, ite_eq_left hk64]
  obtain ⟨hidx, hidx'⟩ := inRad_spec hlet.2
  have hnT := tabRep_nTabs hl
  have hnI : TabRep nInvs[l]! (nPerm l)⁻¹ := by
    rw [nInvs_get hl]
    exact hnT.inv (by rw [← nInvs_get hl]; exact hn.1) (by rw [← nInvs_get hl]; exact hn.2)
  have hconj : tE k = nPerm l * tE (gammaIs[r]!)[e]! * (nPerm l)⁻¹ := by
    refine (tabRep_tE hk64).perm_eq ?_
    rw [nActs_spec hl hγe hk64]
    exact hnT.conjTab (tabRep_tE hγe) hnI
  obtain ⟨hinv1, hinv2⟩ := gammaInv_spec hr hk64
  have hρ : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hjA : jAct X l r p = 4 * (radIdxs[X]!)[jE l r e]! + p % 4 := rfl
  have hj1 : jAct X l r p / 4 = (radIdxs[X]!)[jE l r e]! := by omega
  have hj2 : jAct X l r p % 4 = p % 4 := by omega
  refine ⟨by omega, ?_⟩
  have hnJ : nPerm l ∈ J0 := jPerm_mem_J0 (nWord l)
  have hr0 := r0E_mem_R0 (p % 4)
  have he' : yE X (jAct X l r p) = tE (jE l r e) * r0E (p % 4) := by
    rw [yE, hj1, hj2, hidx']
  rw [he', yE, ← he, hΦmul _ (T0_le_invE (tE_mem heT)) _ (R0_le_invE hr0),
    hΦmul _ (T0_le_invE (tE_mem hlet.1)) _ (R0_le_invE hr0), hγ e heT, hγ _ hlet.1,
    hjE, hinv2, hconj]
  rw [Ι_conj hΙmul hnJ (T0_le_J0 (tE_mem hγe))]
  have hc := hR _ hr0 _ hnJ
  calc Ι (nPerm l) * (Ι (tE (gammaIs[r]!)[e]!) * Φ (r0E (p % 4))) * (Ι (nPerm l))⁻¹
      = Ι (nPerm l) * Ι (tE (gammaIs[r]!)[e]!) * (Ι (nPerm l))⁻¹ *
          ((Ι (nPerm l)) * Φ (r0E (p % 4)) * (Ι (nPerm l))⁻¹) := by group
    _ = Ι (nPerm l) * Ι (tE (gammaIs[r]!)[e]!) * (Ι (nPerm l))⁻¹ * Φ (r0E (p % 4)) := by
        rw [← hc, mul_inv_cancel_right]

include hΦmul in
theorem cStep {X p : ℕ} (hX : X < 2) (hrad : radOK X = true) (hp : p < 64) :
    (cActs[X]!)[p]! < 64 ∧
      Φ (cPerm X) * Φ (yE X p) * (Φ (cPerm X))⁻¹ = Φ (yE X (cActs[X]!)[p]!) := by
  obtain ⟨-, -, hci1, hci2, hA, -⟩ := radOK_parts hrad
  obtain ⟨hA1, hA2⟩ := hA p hp
  refine ⟨hA1, ?_⟩
  have hcT := tabRep_cTabsW hX
  have hcI : TabRep cInvsW[X]! (cPerm X)⁻¹ := by
    rw [cInvsW_get hX]
    exact hcT.inv (by rw [← cInvsW_get hX]; exact hci1) (by rw [← cInvsW_get hX]; exact hci2)
  have e : yE X (cActs[X]!)[p]! = cPerm X * yE X p * (cPerm X)⁻¹ := by
    refine (tabRep_y0Tabs hX hrad hA1).perm_eq ?_
    rw [hA2]
    exact hcT.conjTab (tabRep_y0Tabs hX hrad hp) hcI
  rw [e, Φ_conj hΦmul (cPerm_mem hX) (yE_mem hrad hp)]

end Act

theorem plane_test {G : Type*} [Group G] {Φ Ι : Equiv.Perm (Fin 1782) → G}
    (hΦmul : ∀ x ∈ invE 1, ∀ y ∈ invE 1, Φ (x * y) = Φ x * Φ y)
    (hΦinj : ∀ x ∈ invE 1, ∀ y ∈ invE 1, Φ x = Φ y → x = y)
    (hΙmul : ∀ x ∈ J0, ∀ y ∈ J0, Ι (x * y) = Ι x * Ι y)
    (hR : ∀ y ∈ Model.R0, ∀ x ∈ J0, Φ y * Ι x = Ι x * Φ y)
    (hz : ∀ g : G, g * Φ (suzInv 1) = Φ (suzInv 1) * g → ∃ k ∈ invE 1, Φ k = g)
    {r : ℕ} (hr : r < 16) (hγ : ∀ k < 64, Φ (tE k) = Ι (tE (gammaIs[r]!)[k]!)) : r = 0 := by
  by_contra hr0
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨hfix, hn, hrad0, hrad1, hall⟩ := plane_parts
  obtain ⟨hX, hlet, hT1, i, hi, hai, hbi⟩ := hall r' (by omega)
  set X := witRadical.getD (r' + 1) 0 with hXdef
  have hrad : radOK X = true := by
    interval_cases hx : X
    · exact hrad0
    · exact hrad1
  obtain ⟨-, hE, -, -, -, h1E, ht1E⟩ := radOK_parts hrad
  have hletS : ∀ s < 2, ∀ i < 16, jE (2 * X + s) (r' + 1) (rads[X]!)[i]! < 64 ∧
      inRad X (jE (2 * X + s) (r' + 1) (rads[X]!)[i]!) = true := by
    simpa only [letterOK, allBelow_eq_true, Bool.and_eq_true, decide_eq_true_eq] using hlet
  set g := Ι (nPerm (2 * X + 1)) * Φ (cPerm X) * Ι (nPerm (2 * X)) with hg
  have hact : ∀ p < 64, hAct (r' + 1) p < 64 ∧
      g * Φ (yE X p) * g⁻¹ = Φ (yE X (hAct (r' + 1) p)) := by
    intro p hp
    have hl1 : 2 * X < 4 := by omega
    have hl2 : 2 * X + 1 < 4 := by omega
    obtain ⟨hp1, e1⟩ := jStep hΦmul hΙmul hR hr hγ hl1 hrad (hn _ hl1)
      (by simpa using hletS 0 (by norm_num) (p / 4) (by omega)) hp
    obtain ⟨hp2, e2⟩ := cStep hΦmul hX hrad hp1
    obtain ⟨hp3, e3⟩ := jStep hΦmul hΙmul hR hr hγ hl2 hrad (hn _ hl2)
      (hletS 1 (by norm_num) _ (by omega)) hp2
    have ehA : hAct (r' + 1) p =
        jAct X (2 * X + 1) (r' + 1) ((cActs[X]!)[jAct X (2 * X) (r' + 1) p]!) := rfl
    rw [ehA]
    refine ⟨hp3, ?_⟩
    rw [← e3, ← e2, ← e1, hg]
    group
  have hpT1 : yE X (pT1 X) = suzInv 1 := by
    have h4 : pT1 X / 4 = (radIdxs[X]!)[zI[1]!]! := by unfold pT1; omega
    have h5 : pT1 X % 4 = 0 := by unfold pT1; omega
    rw [yE, h4, h5, (inRad_spec ht1E).2, zI_one, t1Pos_spec.2, r0E, ite_eq_left rfl, mul_one]
  have hpT1lt : pT1 X < 64 := by
    have := (inRad_spec ht1E).1
    unfold pT1
    omega
  have hgt : g * Φ (suzInv 1) = Φ (suzInv 1) * g := by
    have := (hact _ hpT1lt).2
    rw [hT1, hpT1] at this
    calc g * Φ (suzInv 1) = g * Φ (suzInv 1) * g⁻¹ * g := by group
      _ = Φ (suzInv 1) * g := by rw [this]
  obtain ⟨k, hk, hkg⟩ := hz g hgt
  have hk' : ∀ p < 64, k * yE X p * k⁻¹ = yE X (hAct (r' + 1) p) := fun p hp => by
    apply hΦinj _ (mul_mem (mul_mem hk (yE_mem hrad hp)) (inv_mem hk)) _
      (yE_mem hrad (hact p hp).1)
    rw [Φ_conj hΦmul hk (yE_mem hrad hp), hkg]
    exact (hact p hp).2
  have hpR : ∀ ρ < 4, pR0 X ρ < 64 ∧ yE X (pR0 X ρ) = r0E ρ := fun ρ hρ => by
    have h4 : pR0 X ρ / 4 = (radIdxs[X]!)[oneI]! := by unfold pR0; omega
    have h5 : pR0 X ρ % 4 = ρ := by unfold pR0; omega
    have := (inRad_spec h1E).1
    refine ⟨by unfold pR0; omega, ?_⟩
    rw [yE, h4, h5, (inRad_spec h1E).2, tE_oneI.2, one_mul]
  obtain ⟨hp1, e1⟩ := hpR 1 (by norm_num)
  obtain ⟨hp2, e2⟩ := hpR 2 (by norm_num)
  have ha := hk' _ hp1
  have hb := hk' _ hp2
  rw [e1, show r0E 1 = Model.w0 from rfl] at ha
  rw [e2, show r0E 2 = r1 from rfl] at hb
  have hA := tabRep_y0Tabs hX hrad (hact _ hp1).1
  have hB := tabRep_y0Tabs hX hrad (hact _ hp2).1
  rw [← ha] at hA
  rw [← hb] at hB
  have hfix' : ∀ x : Fin 1782, Model.w0 x = x ↔ r1 x = x := fun x => by
    have h := hfix x.val x.2
    rw [tabRep_w0.apply x, tabRep_r1.apply x] at h
    constructor
    · intro hw
      have : ((Model.w0 x : ℕ) == x.val) = true := beq_iff_eq.mpr (congrArg Fin.val hw)
      rw [h] at this
      exact Fin.ext (beq_iff_eq.mp this)
    · intro hw
      have : ((r1 x : ℕ) == x.val) = true := beq_iff_eq.mpr (congrArg Fin.val hw)
      rw [← h] at this
      exact Fin.ext (beq_iff_eq.mp this)
  have hai' := hai
  rw [hA.apply ⟨i, hi⟩] at hai'
  rw [hB.apply ⟨i, hi⟩] at hbi
  apply hbi
  have hw : Model.w0 (k⁻¹ ⟨i, hi⟩) = k⁻¹ ⟨i, hi⟩ := by
    have : (k * Model.w0 * k⁻¹) ⟨i, hi⟩ = ⟨i, hi⟩ := Fin.ext hai'
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at this
    exact Equiv.Perm.eq_inv_iff_eq.mpr this
  have hr1 := (hfix' _).mp hw
  show ((k * r1 * k⁻¹) ⟨i, hi⟩ : ℕ) = i
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hr1, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

end Plane

end CFSG.Sporadic.SuzRecog.B0Gluing
