module

public import Certificates.Kernel.AutJ2Lat.Facts
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.AutJ2Lat

open CFSG.KC.LQT.PW CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.IdxG
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.ComponentClassification.J2Cover CFSG.Quasithin.F112R.AJ2L
open CFSG.KD.J2Dc (wW G ga gb)


noncomputable abbrev TR : Subgroup R := Subgroup.closure {x | x ∈ rSg}

theorem rSg_length : rSg.length = 3 := rfl

theorem conj_cancel (c g : G) : c * (c⁻¹ * g * c) * c⁻¹ = g := by group

theorem evalElt_mem {Γ : Type} [Group Γ] {H : Subgroup Γ} (els : Array Γ)
    (h : ∀ l < els.size, els.getD l 1 ∈ H) : ∀ w : List ℕ, (∀ l ∈ w, l < els.size) →
      evalElt els w ∈ H
  | [], _ => by
    rw [evalElt_nil]
    exact H.one_mem
  | l :: w, hw => by
    rw [evalElt_cons]
    exact H.mul_mem (h l (hw l List.mem_cons_self))
      (evalElt_mem els h w fun x hx => hw x (List.mem_cons_of_mem _ hx))

theorem rSg_getD {l : ℕ} (hl : l < 3) : rSg.toArray.getD l 1 = sgen l hl := by
  interval_cases l <;> rfl

theorem tw_lt3 (i : ℕ) : ∀ l ∈ K.tw.getD i [], l < 3 := by
  intro l hl
  rcases Nat.lt_or_ge i K.tw.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi] at hl
    exact lt_of_all (List.all_eq_true.1 tw_lt _ (List.getElem_mem hi)) l hl
  · rw [List.getD_eq_default _ _ hi] at hl
    simp at hl

theorem conj_mem : ∀ s ∈ J2Dc.j2SgK, φ (cJ * s * cJ⁻¹) ∈ TR := by
  have key : ∀ i (hi : i < 3), φ (cJ * (ga :: gb :: J2Dc.sl).getD (2 + i) 1 * cJ⁻¹) ∈ TR := by
    intro i hi
    have hg := J2Dc.good0 (l := 2 + i) (by omega)
    have hpi : PI (actionHom ((ga :: gb :: J2Dc.sl).getD (2 + i) 1))
        (imgW 9 (J2Dc.J.tc.getD (Nat.add 2 i) 0)) := pi_of_goodJ hg
    have hw : PI (R.subtype (evalElt rSg.toArray (K.tw.getD i [])))
        (imgW 9 (wT (K.tw.getD i []))) :=
      pi_word R.subtype rSg.toArray K.SC (fun l hl => by
        have hl' : l < 3 := by simpa [rSg_length] using hl
        rw [rSg_getD hl']
        exact piS hl') _ (by simpa [rSg_length] using tw_lt3 i)
    have e : φ (cJ * (ga :: gb :: J2Dc.sl).getD (2 + i) 1 * cJ⁻¹) =
        evalElt rSg.toArray (K.tw.getD i []) := by
      apply Subtype.ext
      refine pi_ext (pi_conj hpi) ?_
      rw [eq_of_beq (List.all_eq_true.1 conj_ok i (List.mem_range.2 hi))]
      exact hw
    rw [e]
    refine evalElt_mem _ (fun l hl => ?_) _ (by simpa [rSg_length] using tw_lt3 i)
    have hl' : l < 3 := by simpa [rSg_length] using hl
    rw [rSg_getD hl']
    apply Subgroup.subset_closure
    change sgen l hl' ∈ rSg
    interval_cases l
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  intro s hs
  rw [J2Dc.j2SgK_eq] at hs
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact key 0 (by norm_num)
  · exact key 1 (by norm_num)
  · exact key 2 (by norm_num)

theorem mem_range_of {x : R} (h : (x : Equiv.Perm (Fin 315)) ∈ P) : x ∈ φ.range := by
  obtain ⟨g, hg⟩ : (x : Equiv.Perm (Fin 315)) ∈ actionHom.range := by rw [actionHom_range]; exact h
  exact ⟨g, Subtype.ext hg⟩

theorem mul_inv_mem_range {x y : R} (hx : x ∉ φ.range) (hy : y ∉ φ.range) :
    x * y⁻¹ ∈ φ.range := by
  have hxP : (x : Equiv.Perm (Fin 315)) * permU ∈ P :=
    ((mem_R_iff _).1 x.2).resolve_left fun h => hx (mem_range_of h)
  have hyP : (y : Equiv.Perm (Fin 315)) * permU ∈ P :=
    ((mem_R_iff _).1 y.2).resolve_left fun h => hy (mem_range_of h)
  apply mem_range_of
  have h := P.mul_mem hxP (P.inv_mem hyP)
  have e : (x : Equiv.Perm (Fin 315)) * permU * ((y : Equiv.Perm (Fin 315)) * permU)⁻¹ =
      ((x * y⁻¹ : R) : Equiv.Perm (Fin 315)) := by
    simp [mul_assoc]
  rwa [e] at h

theorem not_le_range : ¬ (TR ≤ φ.range) := by
  intro h
  have h1 : Nat.card TR ∣ Nat.card φ.range := Subgroup.card_dvd_of_le h
  rw [card_closure_rSg, ← Nat.card_congr (MonoidHom.ofInjective φ_injective).toEquiv,
    CFSG.Sporadic.J2.card_J] at h1
  norm_num at h1

noncomputable abbrev MR (k : ℕ) : Subgroup R :=
  Subgroup.closure {x | x ∈ rSg ++ (AutJ2Lat.RL.mw.getD k []).map (wordElt xR yR)}

theorem MR_words {k : ℕ} (hk : k < 5) : (AutJ2Lat.RL.mw.getD k []).map (wordElt xR yR) =
    (J2Dc.J.mw.getD (ORD.getD k 0) []).map fun w => φ (cJ * wordElt ga gb w * cJ⁻¹) := by
  rw [mw_getD hk, List.map_map]
  exact List.map_congr_left fun w hw => member_word (CFSG.KD.J2Dc.mw_lt2 w hw)

theorem TR_le_MR (k : ℕ) : TR ≤ MR k :=
  Subgroup.closure_mono fun _ hx => List.mem_append_left _ hx

theorem mem_comap_conj (M : Subgroup R) (g : G) :
    g ∈ M.comap (φ.comp (MulAut.conj cJ).toMonoidHom) ↔ φ (cJ * g * cJ⁻¹) ∈ M := by
  rw [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem r_complete : ∀ Z : Subgroup R, TR ≤ Z → ∃ k ≤ AutJ2Lat.RL.mw.length,
    Z = memberOrTop AutJ2Lat.RL.mw.length (fun k => MR k) k := by
  intro Z hZ
  obtain ⟨t, htT, htP⟩ : ∃ t ∈ TR, t ∉ φ.range := by
    by_contra h
    exact not_le_range fun x hx => by_contra fun hn => h ⟨x, hx, hn⟩
  let ZJ : Subgroup G := Z.comap (φ.comp (MulAut.conj cJ).toMonoidHom)
  have memZJ : ∀ g, g ∈ ZJ ↔ φ (cJ * g * cJ⁻¹) ∈ Z := fun g => mem_comap_conj Z g
  have hr : ∀ y ∈ φ.range, ∀ (M : Subgroup R), (∀ g ∈ ZJ, φ (cJ * g * cJ⁻¹) ∈ M) → y ∈ Z →
      y ∈ M := by
    rintro _ ⟨g', rfl⟩ M hM hy
    have e : φ (cJ * (cJ⁻¹ * g' * cJ) * cJ⁻¹) = φ g' := by rw [conj_cancel]
    have hy' : φ (cJ * (cJ⁻¹ * g' * cJ) * cJ⁻¹) ∈ Z := by
      rw [e]
      exact hy
    rw [← e]
    exact hM _ ((memZJ _).2 hy')
  have split : ∀ M : Subgroup R, TR ≤ M → (∀ g ∈ ZJ, φ (cJ * g * cJ⁻¹) ∈ M) → Z ≤ M := by
    intro M hTM hM z hz
    by_cases hzr : z ∈ φ.range
    · exact hr z hzr M hM hz
    · have h1 := hr _ (mul_inv_mem_range hzr htP) M hM (Z.mul_mem hz (Z.inv_mem (hZ htT)))
      rw [← inv_mul_cancel_right z t]
      exact M.mul_mem h1 (hTM htT)
  have hSZ : Subgroup.closure {x | x ∈ J2Dc.j2SgK} ≤ ZJ :=
    (Subgroup.closure_le _).2 fun s hs => (memZJ s).2 (hZ (conj_mem s hs))
  obtain ⟨j, hj, hZj⟩ := J2Dc.dc_complete ZJ hSZ
  rw [J2Dc.mw_len] at hj hZj
  rw [rmw_len]
  rcases Nat.lt_or_ge j 5 with hj5 | hj5
  · obtain ⟨k, hk, hkj⟩ : ∃ k < 5, ORD.getD k 0 = j := by
      interval_cases j
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨4, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
      · exact ⟨2, by norm_num, rfl⟩
      · exact ⟨3, by norm_num, rfl⟩
    refine ⟨k, hk.le, ?_⟩
    have hm : memberOrTop 5 (fun k => MR k) k = MR k := by simp [memberOrTop, hk]
    rw [hm]
    have hYJ : ZJ = Subgroup.closure
        {x | x ∈ J2Dc.j2SgK ++ (J2Dc.J.mw.getD j []).map (wordElt ga gb)} := by
      rw [hZj]
      simp [memberOrTop, hj5]
    apply le_antisymm
    · refine split (MR k) (TR_le_MR k) fun g hg => ?_
      rw [hYJ] at hg
      have hle : Subgroup.closure
          {x | x ∈ J2Dc.j2SgK ++ (J2Dc.J.mw.getD j []).map (wordElt ga gb)} ≤
          (MR k).comap (φ.comp (MulAut.conj cJ).toMonoidHom) := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact TR_le_MR k (conj_mem x hx)
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
          apply Subgroup.subset_closure
          apply List.mem_append_right
          rw [MR_words hk, hkj]
          exact List.mem_map.2 ⟨w, hw, rfl⟩
      exact (mem_comap_conj _ _).1 (hle hg)
    · rw [Subgroup.closure_le]
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hZ (Subgroup.subset_closure hx)
      · rw [MR_words hk, hkj] at hx
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
        apply (memZJ _).1
        rw [hYJ]
        exact Subgroup.subset_closure (List.mem_append_right _ (List.mem_map.2 ⟨w, hw, rfl⟩))
  · refine ⟨5, le_rfl, ?_⟩
    have hm : memberOrTop 5 (fun k => MR k) 5 = ⊤ := by simp [memberOrTop]
    rw [hm, eq_top_iff]
    have hJ : ZJ = ⊤ := by
      rw [hZj]
      have : j = 5 := by omega
      subst this
      simp [memberOrTop]
    have hall : ∀ g, φ (cJ * g * cJ⁻¹) ∈ Z := fun g => (memZJ g).1 (hJ ▸ Subgroup.mem_top g)
    intro z _
    have hr' : ∀ y ∈ φ.range, y ∈ Z := by
      rintro _ ⟨g', rfl⟩
      have e : φ (cJ * (cJ⁻¹ * g' * cJ) * cJ⁻¹) = φ g' := by rw [conj_cancel]
      rw [← e]
      exact hall _
    by_cases hzr : z ∈ φ.range
    · exact hr' z hzr
    · have h1 := hr' _ (mul_inv_mem_range hzr htP)
      rw [← inv_mul_cancel_right z t]
      exact Z.mul_mem h1 (hZ htT)

theorem hfix : ∀ s ∈ rSg, lab 315 (codeSetLab 315) rDelta s = rDelta := by
  have key : ∀ i (hi : i < 3), codeSetAct 315 (tab 315 (sgen i hi)).toArray Δc = Δc := by
    intro i hi
    refine fixCodes_sound codes_ok (good_of_pi (piS hi)) (List.all_eq_true.1 fix_ok _ ?_)
    rw [List.getD_eq_getElem _ _ (by rw [SC_eq]; simpa using hi)]
    exact List.getElem_mem _
  intro s hs
  change codeSetAct 315 (tab 315 s).toArray rDelta = rDelta
  rw [delta_eq]
  simp only [rSg, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact key 0 _
  · exact key 1 _
  · exact key 2 _

theorem hmove : ∀ k, 0 < k → k < AutJ2Lat.RL.mw.length → ∃ w ∈ AutJ2Lat.RL.mw.getD k [],
    lab 315 (codeSetLab 315) rDelta (wordElt xR yR w) ≠ rDelta := by
  intro k h0 hk
  rw [rmw_len] at hk
  obtain ⟨c, hc, hne⟩ := List.any_eq_true.1
    (List.all_eq_true.1 move_ok k (List.mem_range'_1.2 ⟨h0, by omega⟩))
  obtain ⟨w, hw, hpi⟩ := fa_right (mem_fa hk) c hc
  refine ⟨w, hw, ?_⟩
  change codeSetAct 315 (tab 315 (wordElt xR yR w)).toArray rDelta ≠ rDelta
  rw [delta_eq, codeSetAct_eq_codeSetF codes_ok (good_of_pi hpi)]
  simpa [fixCodes] using hne

theorem htop : lab 315 (codeSetLab 315) rDelta xR ≠ rDelta ∨
    lab 315 (codeSetLab 315) rDelta yR ≠ rDelta := by
  change codeSetAct 315 (tab 315 xR).toArray rDelta ≠ rDelta ∨
    codeSetAct 315 (tab 315 yR).toArray rDelta ≠ rDelta
  rw [delta_eq, codeSetAct_eq_codeSetF codes_ok (good_of_pi piX),
    codeSetAct_eq_codeSetF codes_ok (good_of_pi piY)]
  have h := top_ok
  rw [topB.eq_1] at h
  simp only [fixCodes, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact h

theorem rK_stab : ∀ g : R, lab 315 (codeSetLab 315) rDelta g = rDelta ↔
    g ∈ Subgroup.closure {x | x ∈ rSg} :=
  stab_of_complete codeSetLab_lawful rDelta_valid xR yR rSg AutJ2Lat.RL.mw r_complete hfix
    (eq_of_beq (by quickRfl : (AutJ2Lat.RL.mw.getD 0 [] == []) = true)) hmove htop

theorem rK_comp : ∀ Z : Subgroup R, Subgroup.closure {x | x ∈ rSg} ≤ Z →
    ∃ j ≤ rLatD.mw.size, Z = memberOrTop rLatD.mw.size
      (fun j => Subgroup.closure {x | x ∈ rSg ++ (rLatD.mw[j]!).map (wordElt xR yR)}) j := by
  intro Z hZ
  obtain ⟨j, hj, e⟩ := r_complete Z hZ
  have hs : rLatD.mw.size = AutJ2Lat.RL.mw.length := List.size_toArray
  refine ⟨j, by rw [hs]; exact hj, ?_⟩
  rw [e, hs]
  simp only [rD_mw_get]

theorem rD_facts : LatFactsK (codeSetLab 315) 315 (tab 315 xR).toArray (tab 315 yR).toArray rDelta
    xR yR rSg (genTabs 315 rSg) rLatD :=
  ⟨rfl, rK_membersOK, rK_stab, rK_comp⟩

theorem rD_Om_size : rLatD.Om.map (fun o => o.lbl.size) = #[1, 9, 15, 3, 3] := by
  have h : [(Om 0).lbl.size, (Om 1).lbl.size, (Om 2).lbl.size, (Om 3).lbl.size,
      (Om 4).lbl.size] = [1, 9, 15, 3, 3] := eq_of_beq om_sizes
  apply Array.toList_inj.1
  change (Array.map _ #[Om 0, Om 1, Om 2, Om 3, Om 4]).toList = _
  simpa using h

theorem rD_o2OK : O2OK (codeSetAct 315) rLatD rOtD := by
  refine ⟨by rw [rD_mw_size]; rfl, fun j hj => ?_⟩
  have hj' : j < 5 := by rwa [rD_mw_size] at hj
  have hcb := (om_spec hj').2
  rw [rD_Om_get hj', otD_get hj']
  refine ⟨by interval_cases j <;> rfl, ?_⟩
  have hX0 : ∀ x ∈ (Om j).lbl.toList, codesBelow 315 x = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hx)
    have := hcb i hi
    rwa [getElem!_pos _ i hi] at this
  refine (omOKG_sound (act := tupAct (codeSetAct 315)) (letters := rLatD.sTabs.toArray)
    (actF := fun l X => X.map (codeSetF 315 (imgW 9 (K.SC.getD l 0))))
    (fun X => ∀ x ∈ X, codesBelow 315 x = true) hX0 (fun l hl X hX => ?_)
    (List.all_eq_true.1 ots j (List.mem_range.2 hj'))).1
  have hl' : l < 3 := by simpa [rLatD, genTabs, rSg] using hl
  have hg : Good 315 (rLatD.sTabs.toArray[l]!) (imgW 9 (K.SC.getD l 0)) := by
    have e : rLatD.sTabs.toArray[l]! = (tab 315 (sgen l hl')).toArray := by
      interval_cases l <;> rfl
    rw [e]
    exact good_of_pi (piS hl')
  refine ⟨fun y hy => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact codesBelow_codeSetF (fun p hp => (hg.2 p hp).2) (hX x hx)
  · unfold tupAct
    exact List.map_congr_left fun x hx => codeSetAct_eq_codeSetF (hX x hx) hg

theorem rD_rows : (List.range 5).map (defaultRow 8 rLatD rOtD) = mems := by
  have e : ∀ j ∈ List.range 5, defaultRow 8 rLatD rOtD j =
      ⟨(Om j).lbl.size * 2 ^ 8, 2 ^ 8 / (OtD j).lbl.size, (Om j).lbl.size * 2 ^ 8⟩ := by
    intro j hj
    have hj' := List.mem_range.1 hj
    unfold defaultRow
    rw [rD_Om_get hj', otD_get hj']
  rw [List.map_congr_left e]
  rfl

theorem gensIn_of {j jj : ℕ} (hj : j < 5) (hjj : jj < 5) (h : gensB j jj = true) :
    GensIn (codeSetAct 315) rDelta rLatD j jj := by
  intro t ht
  rw [rD_mt_get hj, rD_mw_get, List.mem_map] at ht
  obtain ⟨w, hw, rfl⟩ := ht
  obtain ⟨c, hc, hpi⟩ := fa_left (mem_fa hj) w hw
  rw [tab_word (rmw_lt2 w hw), delta_eq, codeSetAct_eq_codeSetF codes_ok (good_of_pi hpi),
    rD_Om_get hjj]
  have hm := List.all_eq_true.1 h c hc
  rw [List.contains_iff_mem, Array.mem_toList_iff, Array.mem_iff_getElem] at hm
  obtain ⟨x, hx, e⟩ := hm
  exact ⟨x, hx, by rw [getElem!_pos _ x hx, e]⟩

theorem gen_xy : Subgroup.closure ({xR, yR} : Set R) = ⊤ := by
  set H := Subgroup.closure ({xR, yR} : Set R)
  have hx : xR ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : yR ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have ha : φ ga ∈ H := by
    rw [← wordElt_WA]
    refine evalElt_mem _ (fun l hl => ?_) WA (by decide)
    obtain rfl | rfl : l = 0 ∨ l = 1 := by
      simp at hl
      omega
    · exact hx
    · exact hy
  rw [φ_ga] at ha
  apply Subgroup.map_injective R.subtype_injective
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply le_antisymm
  · exact Subgroup.map_subtype_le H
  · have hR : R ≤ Subgroup.closure {permA, permB, permU} := le_rfl
    refine hR.trans ?_
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact Subgroup.mem_map_of_mem _ ha
    · exact Subgroup.mem_map_of_mem _ hy
    · have h := Subgroup.mem_map_of_mem R.subtype (H.mul_mem hx (H.inv_mem ha))
      have e : R.subtype (xR * (⟨permA, P_le_R (Subgroup.subset_closure (Set.mem_insert _ _))⟩ :
          R)⁻¹) = permU := by
        change permU * permA * permA⁻¹ = permU
        rw [mul_inv_cancel_right]
      rwa [e] at h

theorem stmt40702 :
    Subgroup.closure ({xR, yR} : Set R) = ⊤ ∧
    LatFactsK (codeSetLab 315) 315 (tab 315 xR).toArray (tab 315 yR).toArray rDelta xR yR rSg
      (genTabs 315 rSg) rLatD ∧
    rLatD.Om.map (fun o => o.lbl.size) = #[1, 9, 15, 3, 3] ∧
    O2OK (codeSetAct 315) rLatD rOtD ∧ (List.range 5).map (defaultRow 8 rLatD rOtD) = mems ∧
    GensIn (codeSetAct 315) rDelta rLatD 3 1 ∧ GensIn (codeSetAct 315) rDelta rLatD 4 1 ∧
    GensIn (codeSetAct 315) rDelta rLatD 4 2 :=
  ⟨gen_xy, rD_facts, rD_Om_size, rD_o2OK, rD_rows, gensIn_of (by decide) (by decide) gens31,
    gensIn_of (by decide) (by decide) gens41, gensIn_of (by decide) (by decide) gens42⟩

end CFSG.KD.AutJ2Lat

end
