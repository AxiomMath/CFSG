module

public import Certificates.Kernel.B433Alt.FCentC
public import Certificates.Kernel.B433Alt.FixLab
public import Certificates.Kernel.B433Alt.FixMain
public import CFSG.Certificates.Kernel.YModel.SchCard
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBFiveCentSyl

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC CFSG.KC.B4A CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.YGroups
  CFSG.Certificates.CosetEnumeration CertificateChecks.KernelY442 CFSG.KC.YModel.Sem CFSG.KC.Y333
  CFSG.KC.B433Alt CFSG.HardMathSupport.Dickson.I271.TabBFiveCent

#kc_forall_tree fc_ok (fun k => CFSG.KD.B4AZ.stepChk k = true) 43 CFSG.KD.B4AZ.step

theorem fc_data : CFSG.KD.B4AZ.PT.length = 43 ∧ CFSG.KD.B4AZ.PT.Nodup ∧
    (∀ i < 43, CFSG.KD.B4AZ.PT.getD i 0 < 31671 ∧ (∀ c ∈ CFSG.KD.B4AZ.TW.getD i [], c < 10) ∧
      (CFSG.KD.B4AZ.SK.getD i 0 = 0 ∨ CFSG.KD.B4AZ.SK.getD i 0 = 1)) ∧
    CFSG.KD.B4AZ.TW.length = 43 ∧ (∀ m < 5, ∃ i < 43, CFSG.KD.B4AZ.PT.getD i 0 = b5 m) := by
  decide +kernel

theorem fc_prod : ∏ l ∈ Finset.range 43,
    (if CFSG.KD.B4AZ.SK.getD l 0 = 0 then CFSG.KD.B4AZ.SA.getD l 0 else 1) = 25200 := by
  decide +kernel

theorem fc_words : (∀ l ∈ [fiveWL, (List.replicate 5 fiveWL).flatten, CFSG.KD.B4AZ.e7W,
      (List.replicate 7 CFSG.KD.B4AZ.e7W).flatten,
      CFSG.KD.B4AZ.e7W ++ fiveWL ++ CFSG.KD.B4AZ.e7W.reverse ++ fiveWL.reverse],
      wInH (wOfL l) = true ∧ wList (wOfL l) = l) ∧ (∀ c ∈ fiveWL, c < 10) := by
  decide +kernel

theorem fc_ord : CFSG.KD.B4AZ.ordChk = true := CFSG.KD.B4AZ.ord_ok

theorem testBit_ptSet (r : ℕ) : ∀ pts : List ℕ, (ptSet pts).testBit r = decide (r ∈ pts)
  | [] => by simp [ptSet]
  | p :: pts => by
    change (Nat.lor (ptSet pts) (Nat.shiftLeft 1 p)).testBit r = _
    rw [nlor, Nat.testBit_or, testBit_ptSet r pts, shl1, Nat.testBit_two_pow]
    by_cases h : p = r
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem testBit_sideAt (X b : ℕ) {r : ℕ} (hr : r < 31671) :
    (sideAt X b).testBit r = (X.testBit r == X.testBit b) := by
  unfold sideAt
  rw [sN_eq', CFSG.KC.YModel.Chain.bitB_eq]
  cases h : X.testBit b
  · change (Nat.xor allP X).testBit r = _
    rw [nxor, Nat.testBit_xor, testBit_allP hr]
    cases X.testBit r <;> rfl
  · cases X.testBit r <;> rfl

theorem testBit_sideAt_ge {X b r : ℕ} (hr : 31671 ≤ r) (hX : X.testBit r = false) :
    (sideAt X b).testBit r = false := by
  unfold sideAt
  rw [sN_eq', CFSG.KC.YModel.Chain.bitB_eq]
  have hA : allP.testBit r = false := testBit_ones_sub_ge hr
  cases X.testBit b
  · change (Nat.xor allP X).testBit r = _
    rw [nxor, Nat.testBit_xor, hA, hX]
    rfl
  · exact hX

section
variable (F0 FS b : ℕ) (pts : List ℕ)

theorem testBit_codeSet {r : ℕ} (hr : r < 31671) : ∀ taus : List (List ℕ),
    (codeSet CFSG.KD.YMY432F.Nf F0 FS b taus pts).testBit r = true ↔
      (FS.testBit r = FS.testBit b ∧ r ∉ pts) ∧
        ∀ τ ∈ taus, (apP CFSG.KD.YMY432F.Nf 1 τ.reverse F0).testBit r =
          (apP CFSG.KD.YMY432F.Nf 1 τ.reverse F0).testBit b
  | [] => by
    change (Nat.land (sideAt FS b) (Nat.xor allP (ptSet pts))).testBit r = true ↔ _
    rw [nland, Nat.testBit_and, testBit_sideAt _ _ hr, nxor, Nat.testBit_xor, testBit_allP hr,
      testBit_ptSet]
    simp
  | τ :: taus => by
    change (sN (codeSet CFSG.KD.YMY432F.Nf F0 FS b taus pts) (fun acc => Nat.land acc
      (sideAt (apP CFSG.KD.YMY432F.Nf 1 τ.reverse F0) b))).testBit r = true ↔ _
    rw [sN_eq', nland, Nat.testBit_and, Bool.and_eq_true, testBit_codeSet hr taus,
      testBit_sideAt _ _ hr, beq_iff_eq]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem testBit_codeSet_ge (hFS : ∀ r, 31671 ≤ r → FS.testBit r = false) {r : ℕ} (hr : 31671 ≤ r) :
    ∀ taus : List (List ℕ), (codeSet CFSG.KD.YMY432F.Nf F0 FS b taus pts).testBit r = false
  | [] => by
    change (Nat.land (sideAt FS b) (Nat.xor allP (ptSet pts))).testBit r = false
    rw [nland, Nat.testBit_and, testBit_sideAt_ge hr (hFS r hr), Bool.false_and]
  | τ :: taus => by
    change (sN (codeSet CFSG.KD.YMY432F.Nf F0 FS b taus pts) (fun acc => Nat.land acc
      (sideAt (apP CFSG.KD.YMY432F.Nf 1 τ.reverse F0) b))).testBit r = false
    rw [sN_eq', nland, Nat.testBit_and, testBit_codeSet_ge hFS hr taus, Bool.false_and]

end

theorem card_popc {X : ℕ} (hge : ∀ r, 31671 ≤ r → X.testBit r = false) :
    (Finset.univ.filter fun ω : Fin 31671 => X.testBit ω = true).card = popc 15 X := by
  have hlt : X < 2 ^ 2 ^ 15 := Nat.lt_pow_two_of_testBit _ fun r hr => hge r (by
    have : (2 : ℕ) ^ 15 = 32768 := by norm_num
    omega)
  rw [Sch.popc_eq 15 _ hlt]
  have hsplit : ∑ r ∈ Finset.range (2 ^ 15), (X.testBit r).toNat =
      ∑ r ∈ Finset.range 31671, (X.testBit r).toNat := by
    have e : Finset.range (2 ^ 15) = Finset.range 31671 ∪ Finset.Ico 31671 (2 ^ 15) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by norm_num)
        (by norm_num)]
    rw [e, Finset.sum_union (by
      rw [Finset.range_eq_Ico]
      exact Finset.Ico_disjoint_Ico_consecutive _ _ _)]
    have h0 : ∑ r ∈ Finset.Ico 31671 (2 ^ 15), (X.testBit r).toNat = 0 :=
      Finset.sum_eq_zero fun r hr => by
        rw [hge r (Finset.mem_Ico.1 hr).1]
        rfl
    rw [h0, add_zero]
  rw [hsplit, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  cases X.testBit r <;> rfl

theorem fix_comm {c π : Equiv.Perm (Fin 31671)} (h : c * π = π * c) (y : Fin 31671) :
    π (c y) = c y ↔ π y = y := by
  have e : π (c y) = c (π y) := by
    have := congrArg (fun σ : Equiv.Perm (Fin 31671) => σ y) h
    simpa only [Equiv.Perm.mul_apply] using this.symm
  rw [e, c.injective.eq_iff]

section

theorem fixW_spec {w : List ℕ} (hw : ∀ c ∈ w, c < 10) (x : Fin 31671) :
    (fixW CFSG.KD.YMY432F.Nf w).testBit x =
      decide (rho432F (evalWord (yGen 4 3 2) w) x = x) := by
  unfold fixW
  rw [nland, Nat.testBit_and, testBit_allP x.2, Bool.and_true]
  unfold fixedSet
  rw [shl1, nxor, Nat.testBit_xor, Sch.testBit_ones', decide_eq_true (by omega : (x : ℕ) < 2 ^ 15),
    Bool.true_xor]
  have hrec := Sch.testBit_orRec (fun b => Nat.land (Nat.xor (Nat.shiftRight
    (apP CFSG.KD.YMY432F.Nf 15 w (idP 15)) (Nat.mul b (2 ^ 15))) (idPlane (2 ^ 15) b))
    (CFSG.KC.MonsterConv.Perm.ones (2 ^ 15))) x 15
  have hb : ∀ b < 15, (Nat.land (Nat.xor (Nat.shiftRight (apP CFSG.KD.YMY432F.Nf 15 w (idP 15))
      (Nat.mul b (2 ^ 15))) (idPlane (2 ^ 15) b)) (CFSG.KC.MonsterConv.Perm.ones (2 ^ 15))).testBit x =
      ((rho432F (evalWord (yGen 4 3 2) w) x : ℕ).testBit b != (x : ℕ).testBit b) := by
    intro b hb
    have hm : b * 2 ^ 15 + (x : ℕ) = 2 ^ 15 * b + x := by ring
    rw [nland, nxor, nshr, nmul, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight,
      Sch.testBit_ones', decide_eq_true (by omega : (x : ℕ) < 2 ^ 15), Bool.and_true,
      idPlane_testBit hb, decide_eq_true (by omega : (x : ℕ) < 2 ^ 15), Bool.true_and,
      hm, apP_spec w hw 15 _ b x hb x.2,
      testBit_idP hb (by omega)]
  set y := rho432F (evalWord (yGen 4 3 2) w) x with hy
  cases hfx : decide (y = x)
  · rw [Bool.not_eq_false']
    rw [decide_eq_false_iff_not] at hfx
    have : ∃ b < 15, (y : ℕ).testBit b ≠ (x : ℕ).testBit b := by
      by_contra hall
      push Not at hall
      exact hfx (Fin.ext (eq_of_bits (k := 15) (by omega) (by omega) hall))
    obtain ⟨b, hb', hne⟩ := this
    exact (hrec.2 ⟨b, hb', by rw [hb b hb']; cases h1 : (y : ℕ).testBit b <;>
      cases h2 : (x : ℕ).testBit b <;> simp_all⟩)
  · rw [decide_eq_true_iff] at hfx
    rw [Bool.not_eq_true']
    by_contra hne
    rw [Bool.not_eq_false] at hne
    obtain ⟨b, hb', h1⟩ := hrec.1 hne
    rw [hb b hb', hfx] at h1
    simp at h1

theorem testBit_FS_ge {r : ℕ} (hr : 31671 ≤ r) : CFSG.KD.B4AZ.FS.testBit r = false := by
  change (Nat.land _ allP).testBit r = false
  have hA : allP.testBit r = false := testBit_ones_sub_ge hr
  rw [nland, Nat.testBit_and, hA, Bool.and_false]

@[expose] noncomputable def sF : Equiv.Perm (Fin 31671) := rho432F (evalWord (yGen 4 3 2) fiveWL)

theorem comm_lab {c : Equiv.Perm (Fin 31671)} (hc : c ∈ rho432F.range) {x : Fin 31671}
    (hx : c x = x) : c * lab x = lab x * c := by
  obtain ⟨g, rfl⟩ := hc
  have h := lab_conj jComm g x
  rw [hx] at h
  calc rho432F g * lab x = rho432F g * lab x * (rho432F g)⁻¹ * rho432F g := by group
    _ = lab x * rho432F g := by rw [← h]

theorem fix_lab {p : ℕ} {τ : List ℕ} (hτ : ∀ c ∈ τ, c < 10) (hp : p < 31671)
    (h : hubOK CFSG.KD.YMY432F.Nf p τ = true) (r : Fin 31671) :
    (apP CFSG.KD.YMY432F.Nf 1 τ.reverse CFSG.KD.B4AX.F0).testBit r =
      decide (lab ⟨p, hp⟩ r = r) := by
  have hτ' : ∀ c ∈ τ.reverse, c < 10 := fun c hc => hτ c (List.mem_reverse.1 hc)
  rw [apP1_spec hτ', f0_spec, evalWord_rev, map_inv, lab_eq jComm (hubOK_spec hτ hp h)]
  congr 1
  apply propext
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  constructor
  · intro e
    rw [e]
    simp
  · intro e
    calc d0 ((rho432F (evalWord (yGen 4 3 2) τ))⁻¹ r)
        = (rho432F (evalWord (yGen 4 3 2) τ))⁻¹
            (rho432F (evalWord (yGen 4 3 2) τ) (d0 ((rho432F (evalWord (yGen 4 3 2) τ))⁻¹ r))) := by
          simp
      _ = (rho432F (evalWord (yGen 4 3 2) τ))⁻¹ r := by rw [e]

@[expose] noncomputable def βF (l : ℕ) : Fin 31671 :=
  ⟨CFSG.KD.B4AZ.PT.getD l 0 % 31671, Nat.mod_lt _ (by norm_num)⟩

theorem βF_val {l : ℕ} (hl : l < 43) : (βF l : ℕ) = CFSG.KD.B4AZ.PT.getD l 0 :=
  Nat.mod_eq_of_lt (fc_data.2.2.1 l hl).1

@[expose] noncomputable def CF : Subgroup (Equiv.Perm (Fin 31671)) :=
  Subgroup.centralizer {sF} ⊓ rho432F.range

theorem step_spec {i : ℕ} (hi : i < 43) :
    hubOK CFSG.KD.YMY432F.Nf (CFSG.KD.B4AZ.PT.getD i 0) (CFSG.KD.B4AZ.TW.getD i []) = true ∧
      (CFSG.KD.B4AZ.SK.getD i 0 = 0 → CFSG.KD.B4AZ.levelChk i = true) ∧
      (CFSG.KD.B4AZ.SK.getD i 0 = 1 → CFSG.KD.B4AZ.deriveChk i = true) := by
  have h := fc_ok i hi
  unfold CFSG.KD.B4AZ.stepChk at h
  rw [andB_iff] at h
  refine ⟨h.1, fun h0 => ?_, fun h1 => ?_⟩
  · have hb : Nat.beq (CFSG.KD.B4AZ.SK.getD i 0) 0 = true := by rw [h0]; rfl
    rw [hb] at h
    exact h.2
  · have hb : Nat.beq (CFSG.KD.B4AZ.SK.getD i 0) 0 = false := by rw [h1]; rfl
    rw [hb] at h
    exact h.2

theorem lab_step {j : ℕ} (hj : j < 43) :
    rho432F (evalWord (yGen 4 3 2) (dpW (CFSG.KD.B4AZ.TW.getD j []))) = lab (βF j) := by
  have hp := (fc_data.2.2.1 j hj).1
  rw [rho_dpW jComm (fc_data.2.2.1 j hj).2.1 hp (step_spec hj).1]
  congr 1
  exact Fin.ext (βF_val hj).symm

theorem stab_comm {l : ℕ} (hl : l ≤ 43) {c : Equiv.Perm (Fin 31671)}
    (hc : c ∈ chainStab CF βF l) :
    c * sF = sF * c ∧ ∀ j < l, c * lab (βF j) = lab (βF j) * c := by
  obtain ⟨hcC, hfix⟩ := mem_chainStab.1 hc
  have hcC' := Subgroup.mem_inf.1 hcC
  exact ⟨Subgroup.mem_centralizer_singleton_iff.1 hcC'.1,
    fun j hj => comm_lab hcC'.2 (hfix j hj)⟩

theorem orbit_level {l : ℕ} (hl : l < 43) :
    (MulAction.orbit (chainStab CF βF l) (βF l)).ncard ≤
      popc 15 (codeSet CFSG.KD.YMY432F.Nf CFSG.KD.B4AX.F0 CFSG.KD.B4AZ.FS
        (CFSG.KD.B4AZ.PT.getD l 0) (CFSG.KD.B4AZ.TW.take l) (CFSG.KD.B4AZ.PT.take l)) := by
  set X := codeSet CFSG.KD.YMY432F.Nf CFSG.KD.B4AX.F0 CFSG.KD.B4AZ.FS
    (CFSG.KD.B4AZ.PT.getD l 0) (CFSG.KD.B4AZ.TW.take l) (CFSG.KD.B4AZ.PT.take l) with hX
  have hge : ∀ r, 31671 ≤ r → X.testBit r = false := fun r hr =>
    testBit_codeSet_ge _ _ _ _ (fun r hr => testBit_FS_ge hr) hr _
  have hsub : MulAction.orbit (chainStab CF βF l) (βF l) ⊆
      ((Finset.univ.filter fun x : Fin 31671 => X.testBit x = true : Finset (Fin 31671)) :
        Set (Fin 31671)) := by
    rintro _ ⟨⟨c, hc⟩, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change X.testBit (c (βF l) : ℕ) = true
    obtain ⟨hcs, hcl⟩ := stab_comm hl.le hc
    have hfix := (mem_chainStab.1 hc).2
    rw [← βF_val hl] at hX
    rw [hX, testBit_codeSet _ _ _ _ (c (βF l)).2]
    have hfs : ∀ y : Fin 31671, CFSG.KD.B4AZ.FS.testBit y = decide (sF y = y) := fun y =>
      fixW_spec fc_words.2 y
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hfs, hfs]
      exact decide_eq_decide.2 (fix_comm hcs _)
    · intro hm
      obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.1 hm
      have hjl : j < l := by
        rw [List.length_take] at hj
        omega
      have hjv' : CFSG.KD.B4AZ.PT.getD j 0 = (c (βF l) : ℕ) := by
        rw [List.getElem_take] at hjv
        rw [List.getD_eq_getElem _ _ (by rw [fc_data.1]; omega), hjv]
      have e : c (βF j) = c (βF l) := by
        rw [hfix j hjl]
        exact Fin.ext (by rw [βF_val (by omega), hjv'])
      have e2 := c.injective e
      have hv := congrArg Fin.val e2
      rw [βF_val (by omega), βF_val hl] at hv
      have hnd := fc_data.2.1
      rw [List.nodup_iff_injective_get] at hnd
      have hlen := fc_data.1
      have := @hnd ⟨j, by omega⟩ ⟨l, by omega⟩ (by
        simp only [List.get_eq_getElem]
        rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
        exact hv)
      have := congrArg Fin.val this
      simp at this
      omega
    · intro τ hτ
      obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.1 hτ
      have hjl : j < l := by
        rw [List.length_take] at hj
        omega
      have hτj : τ = CFSG.KD.B4AZ.TW.getD j [] := by
        rw [← hjv, List.getElem_take, List.getD_eq_getElem _ _ (by rw [fc_data.2.2.2.1]; omega)]
      have hp := (fc_data.2.2.1 j (by omega)).1
      rw [hτj, fix_lab (fc_data.2.2.1 j (by omega)).2.1 hp (step_spec (by omega)).1,
        fix_lab (fc_data.2.2.1 j (by omega)).2.1 hp (step_spec (by omega)).1]
      have e : (⟨CFSG.KD.B4AZ.PT.getD j 0, hp⟩ : Fin 31671) = βF j :=
        Fin.ext (βF_val (by omega)).symm
      rw [e]
      exact decide_eq_decide.2 (fix_comm (hcl j hjl) _)
  calc (MulAction.orbit (chainStab CF βF l) (βF l)).ncard
      ≤ ((Finset.univ.filter fun x : Fin 31671 => X.testBit x = true : Finset (Fin 31671)) :
          Set (Fin 31671)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = popc 15 X := by rw [Set.ncard_coe_finset, card_popc hge]

theorem fix_derived {l : ℕ} (hl : l < 43) (hd : CFSG.KD.B4AZ.deriveChk l = true)
    {c : Equiv.Perm (Fin 31671)} (hc : c ∈ chainStab CF βF l) : c (βF l) = βF l := by
  unfold CFSG.KD.B4AZ.deriveChk at hd
  rw [andB_iff, andB_iff] at hd
  obtain ⟨hx, hp, he⟩ := hd
  have hx' : CFSG.KD.B4AZ.SA.getD l 0 < l := Nat.blt_eq.mp hx
  have hp' : CFSG.KD.B4AZ.SP.getD l 0 ≤ l := Nat.ble_eq.mp hp
  set x := CFSG.KD.B4AZ.SA.getD l 0
  set p := CFSG.KD.B4AZ.SP.getD l 0
  obtain ⟨hcs, hcl⟩ := stab_comm hl.le hc
  have hfix := (mem_chainStab.1 hc).2
  obtain ⟨π, hπw, hπr, hπc⟩ : ∃ π : Equiv.Perm (Fin 31671),
      (∀ c ∈ CFSG.KD.B4AZ.permW p, c < 10) ∧ rho432F (evalWord (yGen 4 3 2)
        (CFSG.KD.B4AZ.permW p)) = π ∧ c * π = π * c := by
    by_cases h0 : p = 0
    · have hw : CFSG.KD.B4AZ.permW p = fiveWL.reverse := by
        unfold CFSG.KD.B4AZ.permW
        rw [h0]
        rfl
      refine ⟨sF⁻¹, ?_, ?_, ?_⟩
      · rw [hw]
        exact fun c hc => fc_words.2 c (List.mem_reverse.1 hc)
      · rw [hw, evalWord_rev, map_inv]
        rfl
      · exact (Commute.inv_right hcs).eq
    · have hw : CFSG.KD.B4AZ.permW p = dpW (CFSG.KD.B4AZ.TW.getD (p - 1) []) := by
        unfold CFSG.KD.B4AZ.permW
        have hb : Nat.beq p 0 = false := by
          cases hq : Nat.beq p 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hq) h0
        rw [hb]
        rfl
      refine ⟨lab (βF (p - 1)), ?_, ?_, hcl (p - 1) (by omega)⟩
      · rw [hw]
        exact dpW_lt (fc_data.2.2.1 (p - 1) (by omega)).2.1
      · rw [hw, lab_step (by omega)]
  have hπ : π (βF l) = βF x := by
    have hb := congrArg (fun y => y.testBit (CFSG.KD.B4AZ.PT.getD l 0)) (Nat.eq_of_beq_eq_true he)
    simp only at hb
    rw [← βF_val hl, apP1_spec hπw, hπr, shl1, shl1, Nat.testBit_two_pow_self,
      Nat.testBit_two_pow] at hb
    apply Fin.ext
    rw [βF_val (by omega)]
    exact (of_decide_eq_true hb).symm
  apply π.injective
  have e : π (c (βF l)) = c (π (βF l)) := by
    have := congrArg (fun σ : Equiv.Perm (Fin 31671) => σ (βF l)) hπc
    simpa only [Equiv.Perm.mul_apply] using this.symm
  rw [e, hπ, hfix x hx']

theorem card_CF_le : Nat.card CF ≤ 25200 := by
  have h := card_le_prod_of_chain CF 43 βF
    (fun l => if CFSG.KD.B4AZ.SK.getD l 0 = 0 then CFSG.KD.B4AZ.SA.getD l 0 else 1) ?_ ?_
  · rwa [fc_prod] at h
  · intro l hl
    rcases (fc_data.2.2.1 l hl).2.2 with h0 | h1
    · rw [if_pos h0]
      have hc := (step_spec hl).2.1 h0
      unfold CFSG.KD.B4AZ.levelChk at hc
      exact (orbit_level hl).trans (Nat.ble_eq.mp hc)
    · rw [if_neg (by omega)]
      have hsub : MulAction.orbit (chainStab CF βF l) (βF l) ⊆ {βF l} := by
        rintro _ ⟨⟨c, hc⟩, rfl⟩
        exact fix_derived hl ((step_spec hl).2.2 h1) hc
      calc (MulAction.orbit (chainStab CF βF l) (βF l)).ncard ≤ ({βF l} : Set (Fin 31671)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 1 := Set.ncard_singleton _
  · rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    obtain ⟨hcC, hfix⟩ := mem_chainStab.1 hc
    refine base_eq_one (Subgroup.mem_inf.1 hcC).2 fun m hm => ?_
    obtain ⟨i, hi, hiv⟩ := fc_data.2.2.2.2 m hm
    have e : β5 m = βF i := by
      apply Fin.ext
      rw [β5, dif_pos hm, βF_val hi, hiv]
    rw [e, hfix i hi]

theorem card_centralizer_five :
    Nat.card ↥(Subgroup.centralizer {rho432F (evalWord (yGen 4 3 2) [1, 2, 0, 5])} ⊓
        rho432F.range) ≤ 25200 ∧
      orderOf (rho432F (evalWord (yGen 4 3 2) [1, 2, 0, 5])) = 5 ∧
      ∃ e : YGroup 4 3 2, orderOf (rho432F e) = 7 ∧
        rho432F e * rho432F (evalWord (yGen 4 3 2) [1, 2, 0, 5]) =
          rho432F (evalWord (yGen 4 3 2) [1, 2, 0, 5]) * rho432F e := by
  have ho := fc_ord
  unfold CFSG.KD.B4AZ.ordChk at ho
  simp only [andB_iff] at ho
  obtain ⟨h5, h2, h7, h0, hcm⟩ := ho
  have hw := fc_words.1
  have w1 := hw fiveWL (by simp)
  have w5 := hw (List.replicate 5 fiveWL).flatten (by simp)
  have we := hw CFSG.KD.B4AZ.e7W (by simp)
  have we7 := hw (List.replicate 7 CFSG.KD.B4AZ.e7W).flatten (by simp)
  have wc := hw (CFSG.KD.B4AZ.e7W ++ fiveWL ++ CFSG.KD.B4AZ.e7W.reverse ++ fiveWL.reverse) (by simp)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hs5 : sF ^ 5 = 1 := by
    have := rho_eq_one_of w5.1 w5.2 h5
    rwa [evalWord_replicate, map_pow] at this
  have hs1 : sF ≠ 1 := by
    intro h
    have := rho_apply_of w1.1 w1.2 (x := 2) (by norm_num)
    change (sF ⟨2, _⟩ : ℕ) = _ at this
    rw [h, Equiv.Perm.one_apply] at this
    rw [← this] at h2
    exact absurd h2 (by decide)
  set e := evalWord (yGen 4 3 2) CFSG.KD.B4AZ.e7W
  have he7 : rho432F e ^ 7 = 1 := by
    have := rho_eq_one_of we7.1 we7.2 h7
    rwa [evalWord_replicate, map_pow] at this
  have he1 : rho432F e ≠ 1 := by
    intro h
    have := rho_apply_of we.1 we.2 (x := 0) (by norm_num)
    rw [h, Equiv.Perm.one_apply] at this
    rw [← this] at h0
    exact absurd h0 (by decide)
  have hc : rho432F e * sF * (rho432F e)⁻¹ * sF⁻¹ = 1 := by
    have := rho_eq_one_of wc.1 wc.2 hcm
    rwa [ev_app, ev_app, ev_app, evalWord_rev, evalWord_rev, map_mul, map_mul, map_mul,
      map_inv, map_inv] at this
  have hc' : rho432F e * sF = sF * rho432F e := by
    calc rho432F e * sF = rho432F e * sF * (rho432F e)⁻¹ * sF⁻¹ * (sF * rho432F e) := by group
      _ = sF * rho432F e := by rw [hc, one_mul]
  exact ⟨card_CF_le, orderOf_eq_prime hs5 hs1, e, orderOf_eq_prime he7 he1, hc'⟩

end

end CertificateChecks.KernelB433

end
