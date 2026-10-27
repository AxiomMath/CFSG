
module

public import CFSG.Sporadic.Co1.Module.TwoBCertBase1
import all CFSG.Sporadic.Co1.Module.TwoBCertBase1

public import CFSG.Sporadic.Co1.Module.InvReps
public import CFSG.Sporadic.Co1.Module.OddBuild

public section

namespace CFSG.Sporadic.Co1.Module.TwoB

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.OddCentNative Matrix

attribute [local irreducible] rowsSB

section

attribute [local irreducible] regsGB regsRowsB

end

attribute [local irreducible] rrB regsRowsB

section Kernel

open CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.Module.TwoBFrame CFSG.KC.Co1M
  CFSG.KC.Co1F2 Equiv

@[expose] def TwoBFacts (s : NativeSporadic.Co1) : Prop :=
  Nat.card ↥(Subgroup.centralizer ({s} : Set NativeSporadic.Co1)) = 2012774400 ∧
  (∀ v : Vec24, co1Act s v = v → v ≠ 0 →
    v ∈ Set.range fun g : NativeSporadic.Co1 => co1Act g v₄) ∧
  (∀ v w : Vec24, co1Act s v = v → co1Act s w = w → v ≠ 0 → w ≠ 0 →
    ∃ g ∈ Subgroup.centralizer ({s} : Set NativeSporadic.Co1), co1Act g v = w) ∧
  ∃ S T : Subgroup NativeSporadic.Co1, S ≤ Subgroup.centralizer ({s} : Set NativeSporadic.Co1) ∧
    T ≤ Subgroup.centralizer ({s} : Set NativeSporadic.Co1) ∧ Nat.card ↥S = 2 ^ 15 ∧
    Nat.card ↥T = 2 ^ 15 ∧ Nat.card ↥(S ⊓ T) ≤ 2 ^ 11

theorem twoBFacts_conj {t : NativeSporadic.Co1} (h : TwoBFacts t) (x : NativeSporadic.Co1) :
    TwoBFacts (x * t * x⁻¹) := by
  obtain ⟨hcard, hb, hc, S, T, hS, hT, hSc, hTc, hint⟩ := h
  have hfix : ∀ v : Vec24, co1Act (x * t * x⁻¹) v = v ↔ co1Act t (co1Act x⁻¹ v) = co1Act x⁻¹ v := by
    intro v
    constructor
    · intro hv
      have h1 : v ∈ {v : Vec24 | co1Act (x * t * x⁻¹) v = v} := hv
      rw [fixSet_conj] at h1
      obtain ⟨w, hw, rfl⟩ := h1
      rw [co1Act_inv_apply]
      exact hw
    · intro hv
      have h1 : co1Act x⁻¹ v ∈ {w : Vec24 | co1Act t w = w} := hv
      have h2 : co1Act x (co1Act x⁻¹ v) ∈ {v : Vec24 | co1Act (x * t * x⁻¹) v = v} := by
        rw [fixSet_conj]
        exact ⟨_, h1, rfl⟩
      rwa [co1Act_apply_inv] at h2
  have hne : ∀ v : Vec24, v ≠ 0 → co1Act x⁻¹ v ≠ 0 := by
    intro v hv h0
    apply hv
    have := congrArg (co1Act x) h0
    rw [co1Act_apply_inv] at this
    rw [this]
    simp [co1Act_eq_mulVec]
  refine ⟨?_, fun v hv hv0 => ?_, fun v w hv hw hv0 hw0 => ?_, ?_⟩
  · rw [card_centralizer_conj]
    exact hcard
  · obtain ⟨g, hg⟩ := hb (co1Act x⁻¹ v) ((hfix v).1 hv) (hne v hv0)
    refine ⟨x * g, ?_⟩
    show co1Act (x * g) v₄ = v
    have hg' : co1Act g v₄ = co1Act x⁻¹ v := hg
    rw [co1Act_mul, hg', co1Act_apply_inv]
  · obtain ⟨g, hg, hgv⟩ := hc (co1Act x⁻¹ v) (co1Act x⁻¹ w) ((hfix v).1 hv) ((hfix w).1 hw)
      (hne v hv0) (hne w hw0)
    refine ⟨x * g * x⁻¹, conj_mem_centralizer hg x, ?_⟩
    rw [co1Act_mul, co1Act_mul, hgv, co1Act_apply_inv]
  · refine ⟨S.map (MulAut.conj x).toMonoidHom, T.map (MulAut.conj x).toMonoidHom,
      map_conj_le_centralizer hS x, map_conj_le_centralizer hT x, ?_, ?_, ?_⟩
    · rw [card_map_conj, hSc]
    · rw [card_map_conj, hTc]
    · rw [← map_conj_inf, card_map_conj]
      exact hint

theorem card_cent_le :
    Nat.card ↥(Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1)) ≤ 2012774400 := by
  have ok := ok77
  obtain ⟨hwH, hwG, hwW, hwE, -⟩ := ok.wd
  obtain ⟨hlEW, -, -, hlM01, hlM0⟩ := ok.lens
  obtain ⟨htr1, htr2, htrS, -, -, htrE, -⟩ := tr77
  obtain ⟨hp1, hp⟩ := andB_true ok.perm
  obtain ⟨hp2, hp⟩ := andB_true hp
  obtain ⟨hpS, hp⟩ := andB_true hp
  obtain ⟨hpH0, hp⟩ := andB_true hp
  obtain ⟨hpH1, hpW⟩ := andB_true hp
  obtain ⟨ρ₁, e1, -⟩ := permP_of_check hp1
  obtain ⟨ρ₂, e2, -⟩ := permP_of_check hp2
  obtain ⟨ρs, eS, -⟩ := permP_of_check hpS
  have hI1 : F77.Ind (regB 3) ρ₁ := ind_of_check _ (pm_regB (by norm_num)) htr1 e1 ok.ind1 ok.sym
  have hI2 : F77.Ind (regB 4) ρ₂ := ind_of_check _ (pm_regB (by norm_num)) htr2 e2 ok.ind2 ok.sym
  have hIS : F77.Ind sBc ρs := ind_of_check _ pm_sBc htrS eS ok.indS ok.sym
  let ng : ℕ → Perm (Fin 24) := fun l => if l = 0 then ρ₁ else ρ₂
  have hng : ∀ l, ng l ∈ F77.indSub := fun l => by
    by_cases h : l = 0
    · simp only [ng, h, ↓reduceIte]
      exact ⟨_, hI1⟩
    · simp only [ng, h, ↓reduceIte]
      exact ⟨_, hI2⟩
  have hPN : ∀ l < 2, PermP (getL 0 W77.PN l) (ng l) := fun l hl => by
    rcases l with _ | _ | l
    · exact e1
    · exact e2
    · omega
  have hword : ∀ w : List ℕ, (w.map ng).prod ∈ F77.indSub := fun w =>
    F77.indSub.list_prod_mem fun x hx => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
      exact hng l
  obtain ⟨hwd1, hw⟩ := andB_true ok.words
  obtain ⟨hwd2, hw⟩ := andB_true hw
  obtain ⟨hwd3, hwd4⟩ := andB_true hw
  have hH : ∀ l < 2, PermP (getL 0 W77.H l) ((W77.M01W.getD l []).map ng).prod := fun l hl => by
    have e := Nat.eq_of_beq_eq_true ((zip_spec [] hwd1).2 l (by rw [hlM01]; exact hl))
    rw [getL_eq, ← e]
    exact permP_pwK _ ng 2 hPN (hwH l hl).1 (hwH l hl).2
  have hHi : ∀ l < 2, PermP (getL 0 W77.Hi l) (((W77.M01W.getD l []).map ng).prod)⁻¹ := by
    intro l hl
    have hk : permK (getL 0 W77.H l) (getL 0 W77.Hi l) = true := by
      rcases l with _ | _ | l
      · exact hpH0
      · exact hpH1
      · omega
    obtain ⟨ρ', e, ei⟩ := permP_of_check hk
    rw [permP_unique (hH l hl) e]
    exact ei
  have hG : ∀ l < 3, PermP (getL 0 W77.G l) ((W77.M0W.getD l []).map ng).prod := fun l hl => by
    have e := Nat.eq_of_beq_eq_true ((zip_spec [] hwd2).2 l (by rw [hlM0]; exact hl))
    rw [getL_eq, ← e]
    exact permP_pwK _ ng 2 hPN (hwG l hl).1 (hwG l hl).2
  obtain ⟨hf1, hf⟩ := andB_true ok.fix
  obtain ⟨hf2, hf3⟩ := andB_true hf
  have hHfix : ∀ l < 2, ((W77.M01W.getD l []).map ng).prod 0 = 0 ∧
      ((W77.M01W.getD l []).map ng).prod 1 = 1 := by
    intro l hl
    obtain ⟨a, b⟩ := andB_true (allN_true hf1 l hl)
    refine ⟨Fin.ext ?_, Fin.ext ?_⟩
    · rw [← hH l hl 0]
      exact Nat.eq_of_beq_eq_true a
    · rw [← hH l hl 1]
      exact Nat.eq_of_beq_eq_true b
  have hGfix : ∀ l < 3, ((W77.M0W.getD l []).map ng).prod 0 = 0 := by
    intro l hl
    refine Fin.ext ?_
    rw [← hG l hl 0]
    exact Nat.eq_of_beq_eq_true (allN_true hf2 l hl)
  let gW : Perm (Fin 24) := (W77.W0.map ng).prod
  have hWP : PermP W77.WP gW := by
    rw [← Nat.eq_of_beq_eq_true hwd3]
    exact permP_pwK _ ng 2 hPN hwW.1 hwW.2
  have hWPi : PermP W77.WPi gW⁻¹ := by
    obtain ⟨ρ', e, ei⟩ := permP_of_check hpW
    rw [permP_unique hWP e]
    exact ei
  have hTP : W77.TP = ppc (ppc W77.WP W77.PS) W77.WPi := (Nat.eq_of_beq_eq_true hwd4).symm
  have hτ : PermP W77.TP (gW * ρs * gW⁻¹) := by
    rw [hTP]
    exact permP_ppc (permP_ppc hWP eS) hWPi
  have hτ0 : (gW * ρs * gW⁻¹) 0 = 1 := Fin.ext (by
    rw [← hτ 0]
    exact Nat.eq_of_beq_eq_true hf3)
  let C01 : Subgroup (Perm (Fin 24)) := F77.indSub ⊓ MulAction.stabilizer (Perm (Fin 24)) (0 : Fin 24) ⊓
    MulAction.stabilizer (Perm (Fin 24)) (1 : Fin 24)
  obtain ⟨tX, htX, hdX⟩ := tree_family_conj C01 ok.tx (fun l => ((W77.M01W.getD l []).map ng).prod)
    (fun l hl => Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hword _,
      MulAction.mem_stabilizer_iff.2 (hHfix l hl).1⟩, MulAction.mem_stabilizer_iff.2 (hHfix l hl).2⟩)
    hH hHi hτ (by rw [hTP]; exact ppc_shr _ _)
  rw [ok.txl] at htX hdX
  let κ : ℕ → Perm (Fin 24) := fun j => tX j * gW
  have hκ : ∀ j < 1385 + 1, κ j ∈ F77.indSub := fun j hj =>
    F77.indSub.mul_mem (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (htX j hj)).1).1 (hword _)
  have hκe : ∀ j, κ j * ρs * (κ j)⁻¹ = tX j * (gW * ρs * gW⁻¹) * (tX j)⁻¹ := fun j => by
    simp only [κ]
    group
  have hκq : ∀ j < 1385 + 1, (κ j * ρs * (κ j)⁻¹) 0 = 1 := by
    intro j hj
    have h0 : tX j • (0 : Fin 24) = 0 :=
      MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (htX j hj)).1).2
    have h1 : tX j • (1 : Fin 24) = 1 := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (htX j hj)).2
    rw [Perm.smul_def] at h0 h1
    have h0' : (tX j)⁻¹ 0 = 0 := by
      rw [Perm.inv_eq_iff_eq, h0]
    rw [hκe, Perm.mul_apply, Perm.mul_apply, h0', hτ0, h1]
  have hκinj : ∀ j < 1385 + 1, ∀ j' < 1385 + 1,
      κ j * ρs * (κ j)⁻¹ = κ j' * ρs * (κ j')⁻¹ → j = j' := fun j hj j' hj' e =>
    hdX j hj j' hj' (by rw [← hκe, ← hκe]; exact e)
  let C0 : Subgroup (Perm (Fin 24)) := F77.indSub ⊓ MulAction.stabilizer (Perm (Fin 24)) (0 : Fin 24)
  obtain ⟨tP, htP, hdP⟩ := tree_family_pts C0 ok.tp (fun l => ((W77.M0W.getD l []).map ng).prod)
    (fun l hl => Subgroup.mem_inf.2 ⟨hword _, MulAction.mem_stabilizer_iff.2 (hGfix l hl)⟩) hG
  rw [ok.tpl] at htP hdP
  let eE : ℕ → NativeSporadic.Co1 := fun k =>
    ((W77.EW.getD k ([], 0)).1.map nB).prod ^ (W77.EW.getD k ([], 0)).2
  have hpmE : ∀ k < 5, PM (eE k) (W77.EM.getD k 0) := by
    intro k hk
    have h := (zip_spec ([], 0) ok.e).2 k (by rw [hlEW]; exact hk)
    have hw := hwE k hk
    simp only [eE]
    revert h hw
    generalize W77.EW.getD k ([], 0) = p
    obtain ⟨w, m⟩ := p
    intro h hw
    rw [← Nat.eq_of_beq_eq_true h]
    exact pm_pow (pm_wK _ nB 2 (fun l hl => pm_nB hl) w hw) m
  have hIE : ∀ k < 5, F77.Ind (eE k) 1 := fun k hk => by
    have h := ok.indE k hk
    rw [getL_eq] at h
    exact ind1_of_check _ (hpmE k hk) (htrE k hk) h ok.sym
  have hsub : ∀ M ∈ prodsK W77.EM 5, ∃ x, F77.Ind x 1 ∧ PM x M :=
    mem_prodsK W77.EM (fun x => F77.Ind x 1) Frame.ind_one
      (fun x y hx hy => by
        have h := Frame.ind_mul hx hy
        rwa [mul_one] at h) 5
      (fun h hh => ⟨eE h, hIE h hh, by rw [getL_eq]; exact hpmE h hh⟩)
  have hlen32 := ok.elen
  have hE : ∀ k < 32, ∃ x, F77.Ind x 1 ∧ PM x ((prodsK W77.EM 5).getD k 0) := fun k hk =>
    hsub _ (by
      rw [List.getD_eq_getElem _ _ (by rw [hlen32]; exact hk)]
      exact List.getElem_mem _)
  choose! ee hee using hE
  have hinvs := invs_spec ok.einv
  have hconj := CFSG.KC.TreeK.distinctK_sound ok.econj
  rw [conjK_eq] at hconj
  have hinv : ∀ k < 32, (ee k)⁻¹ = ee k := fun k hk => by
    have hk1 : k < (prodsK W77.EM 5).length := by rw [hlen32]; exact hk
    refine inv_eq_of_mul_eq_one_right (pm_mul_self (hee k hk).2 (hinvs _ ?_))
    rw [List.getD_eq_getElem _ _ hk1]
    exact List.getElem_mem _
  have heinj : ∀ k < 32, ∀ k' < 32, ee k * sBc * (ee k)⁻¹ = ee k' * sBc * (ee k')⁻¹ → k = k' := by
    intro k hk k' hk' e
    rw [hinv k hk, hinv k' hk'] at e
    have hp := pm_eq (pm_mul (pm_mul (hee k hk).2 pm_sBc) (hee k hk).2)
      (pm_mul (pm_mul (hee k' hk').2 pm_sBc) (hee k' hk').2) (canon_mulF _ _) (canon_mulF _ _) e
    have hk1 : k < (prodsK W77.EM 5).length := by rw [hlen32]; exact hk
    have hk1' : k' < (prodsK W77.EM 5).length := by rw [hlen32]; exact hk'
    rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk1'] at hp
    refine (hconj.getElem_inj_iff (i := k) (j := k') (hi := by simpa using hk1)
      (hj := by simpa using hk1')).1 ?_
    simp only [List.getElem_map]
    exact hp
  have bB := frame_card_bound F77 rfl ncard_orbit_code4 hIS 0 1 tP
    (fun c hc => (Subgroup.mem_inf.1 (htP c hc)).1)
    (fun c hc => MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 (htP c hc)).2) hdP κ hκ hκq
    hκinj ee (fun k hk => (hee k hk).1) heinj ncard_fix_orbit_le
  rw [CFSG.Sporadic.Co1.card_Co1] at bB
  norm_num at bB ⊢
  generalize Nat.card ↥(Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1)) = n at bB ⊢
  omega

end Kernel

section

attribute [local irreducible] regB regsGB

end

section KernelS

open CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.Module.TwoBFrame CFSG.KC.Co1M
  CFSG.KC.Co1F2

attribute [local instance] Odd.vecAct Odd.vecSMul

end KernelS

section Order

attribute [local instance] Odd.vecAct Odd.vecSMul

end Order

theorem card_cent :
    Nat.card ↥(Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1)) = 2012774400 :=
  le_antisymm card_cent_le card_cent_ge

theorem card_SB :
    Nat.card ↥SB = 2 ^ 15 := by
  obtain ⟨m, hm⟩ := SB_two_pow
  have hd : Nat.card ↥SB ∣ 2 ^ 15 * 61425 := by
    have h := Subgroup.card_dvd_of_le SB_le_cent
    rw [card_cent] at h
    exact h
  exact CFSG.Sporadic.Co1.Module.TwoBFrame.eq_two_pow_of_dvd hm SB_ge ⟨30712, by norm_num⟩ hd

section KernelInter

attribute [local instance] Odd.vecAct Odd.vecSMul

theorem card_SB_inter :
    Nat.card ↥(SB ⊓ SB.map (MulAut.conj (regB gIdx)).toMonoidHom) ≤ 2 ^ 11 := by
  have := finite_co1
  obtain ⟨t, ht, hd⟩ := exists_S_family
  have hS : ∀ x ∈ SB, x • toVecD 24 code4 = toVecD 24 code4 := fun x hx => SB_fix hx
  have hdist : ∀ i < 2048, ∀ j < 2048, t i • (regB gIdx • toVecD 24 code4) =
      t j • (regB gIdx • toVecD 24 code4) → i = j := by
    intro i hi j hj e
    rw [Odd.smul_eq_co1Act, Odd.smul_eq_co1Act, Odd.smul_eq_co1Act, ← gw77] at e
    exact hd i hi j hj e
  have h := CFSG.Sporadic.Co1.Module.TwoBFrame.card_inf_conj_le SB (toVecD 24 code4) hS (regB gIdx)
    t ht hdist
  have h16 := Nat.le_of_mul_le_mul_left
    ((h.trans_eq card_SB).trans_eq (by norm_num : (2 : ℕ) ^ 15 = 2048 * 16)) (by norm_num)
  exact h16.trans (by norm_num)

end KernelInter

theorem omega_mem_orbit4 :
    toVecD 24 code4 ∈ Set.range fun g : NativeSporadic.Co1 => co1Act g v₄ := by
  rw [range_co1Act]
  exact Odd.omega0_mem

theorem twoBFacts_sBc :
    TwoBFacts sBc := by
  have hg : regB gIdx ∈ Subgroup.centralizer ({sBc} : Set NativeSporadic.Co1) :=
    regB_mem_cent (by simp [yIdx, gIdx])
  refine ⟨card_cent, fun v hv hv0 => ?_, fun v w hv hw hv0 hw0 => ?_, ?_⟩
  · obtain ⟨t, -, rfl⟩ := fix_eq_orbit hv hv0
    obtain ⟨g₀, hg₀⟩ := omega_mem_orbit4
    refine ⟨t * g₀, ?_⟩
    show co1Act (t * g₀) v₄ = _
    rw [co1Act_mul]
    exact congrArg (co1Act t) hg₀
  · obtain ⟨t, ht, rfl⟩ := fix_eq_orbit hv hv0
    obtain ⟨u, hu, rfl⟩ := fix_eq_orbit hw hw0
    refine ⟨u * t⁻¹, Subgroup.mul_mem _ hu (Subgroup.inv_mem _ ht), ?_⟩
    rw [co1Act_mul, co1Act_inv_apply]
  · refine ⟨SB, SB.map (MulAut.conj (regB gIdx)).toMonoidHom, SB_le_cent,
      (Subgroup.map_mono SB_le_cent).trans ?_, card_SB, ?_, card_SB_inter⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact conj_mem_of_mem hg hy
    · rw [card_map_conj, card_SB]

end CFSG.Sporadic.Co1.Module.TwoB
