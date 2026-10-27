module

public import Certificates.Kernel.B433Alt.FixLab
public import CFSG.Certificates.Kernel.YModel.SchCard

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC CFSG.KC.B4A CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.YGroups
  CFSG.Certificates.CosetEnumeration CertificateChecks.KernelY442 CFSG.KC.YModel.Sem CFSG.KC.Y333
  CFSG.KC.B433Alt CFSG.Certificates.TwDce

@[expose] noncomputable def setStab (Y : ℕ) : Subgroup (Equiv.Perm (Fin 31671)) where
  carrier := {σ | ∀ r : Fin 31671, Y.testBit (σ r) = Y.testBit r}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb r => by
    change Y.testBit (a (b r)) = _
    rw [ha, hb]
  inv_mem' := fun {a} ha r => by
    have h := ha (a⁻¹ r)
    rw [show a (a⁻¹ r) = r by simp] at h
    exact h.symm

theorem testBit_ones_sub_ge {n q : ℕ} (hq : n ≤ q) :
    (Nat.sub (Nat.shiftLeft 1 n) 1).testBit q = false := by
  rw [shl1]
  change (2 ^ n - 1).testBit q = false
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_false (by omega)

@[expose] noncomputable def Xs (k : ℕ) : ℕ :=
  Nat.land (nodeX CFSG.KD.YMY432F.Nf (CFSG.KD.B4AX.NY.getD k 0) CFSG.KD.B4AX.F0
    (CFSG.KD.B4AX.NH.getD k [])) (Nat.xor allP (CFSG.KD.B4AX.stuckSet (CFSG.KD.B4AX.NJ.getD k 0)))

theorem stab_red {g : ℕ} (h : isStab (dKind (CFSG.KD.B4A.RD g)) = true) :
    g % 8192 < 5965 ∧ CFSG.KD.B4A.RD g = CFSG.KD.B4A.RD (g % 8192) ∧
      CFSG.KD.B4A.RW g = CFSG.KD.B4A.RW (g % 8192) := by
  refine ⟨?_, RD_per g, RW_per g⟩
  rw [RD_per] at h
  by_contra h5
  rw [RD_tail _ (Nat.mod_lt _ (by norm_num)) (by omega)] at h
  exact absurd h (by decide)

theorem idxOf_nj {k : ℕ} (hk : k < 22) :
    CFSG.KD.B4AX.NJ.idxOf (CFSG.KD.B4AX.NJ.getD k 0) = k := by
  obtain ⟨hl, hnd, -⟩ := nj_data
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.Nodup.idxOf_getElem hnd k (by omega)

theorem nj_mem {k : ℕ} (hk : k < 22) : CFSG.KD.B4AX.NJ.getD k 0 ∈ CFSG.KD.B4AX.NJ := by
  rw [List.getD_eq_getElem _ _ (by rw [nj_data.1]; exact hk)]
  exact List.getElem_mem _

section

theorem stab_Y {k : ℕ} (hk : k < 22) :
    (nodeSub (CFSG.KD.B4AX.NJ.getD k 0)).map rho432F ≤ setStab (CFSG.KD.B4AX.NY.getD k 0) := by
  rw [nodeSub, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨g, ⟨hs, hj⟩, rfl⟩, rfl⟩
  obtain ⟨h5, hrd, hrw⟩ := stab_red hs
  rw [hrd] at hs hj
  have hmem : g % 8192 ∈ CFSG.KD.B4AX.SR := sr_data.1 _ h5 hs (by rw [hj]; exact nj_mem hk)
  obtain ⟨i, hi, hgi⟩ := sr_data.2.2 _ hmem
  have hc := Nat.eq_of_beq_eq_true (inv_ok i hi)
  unfold CFSG.KD.B4AX.YOf at hc
  rw [hgi, hj, idxOf_nj hk] at hc
  intro r
  have hw := wList_lt (rw_stab_lt _ h5 hs)
  have hb := congrArg (fun x => x.testBit r) hc
  simp only at hb
  rw [apP1_spec hw] at hb
  change (CFSG.KD.B4AX.NY.getD k 0).testBit (rho432F (wVal (yGen 4 3 2) (CFSG.KD.B4A.RW g)) r) = _
  rw [hrw]
  exact hb

end

theorem testBit_planeAt (X i r : ℕ) (hr : r < 2 ^ 15) :
    (planeAt X i).testBit r = X.testBit (2 ^ 15 * i + r) := by
  unfold planeAt
  rw [nland, nshr, nmul, Nat.testBit_and, Nat.testBit_shiftRight, wid_eq,
    show CFSG.KC.B4A.ones (2 ^ 15) = Nat.sub (Nat.shiftLeft 1 (2 ^ 15)) 1 from rfl,
    testBit_ones_sub hr, Bool.and_true, Nat.mul_comm, Nat.add_comm]

theorem rel_planes : (∀ u < 12, planeAt (ptPlanes CFSG.KD.B4AX.RA) u =
      Nat.shiftLeft 1 (CFSG.KD.B4AX.RA.getD u 0)) ∧
    ∀ i < 3, ∀ u < 12,
      planeAt (permPlanes CFSG.KD.B4AX.RP (CFSG.KD.B4AX.RS.getD i (0, [])).2) u =
        planeAt CFSG.KD.B4AX.RP ((CFSG.KD.B4AX.RS.getD i (0, [])).2.getD u 0) ∧
      planeAt (permPlanes (ptPlanes CFSG.KD.B4AX.RA) (CFSG.KD.B4AX.RS.getD i (0, [])).2) u =
        Nat.shiftLeft 1 (CFSG.KD.B4AX.RA.getD ((CFSG.KD.B4AX.RS.getD i (0, [])).2.getD u 0) 0) := by
  decide +kernel

@[expose] def Rel (x y : Fin 31671) : Prop :=
  ∃ u < 12, (x : ℕ) = CFSG.KD.B4AX.RA.getD u 0 ∧ (planeAt CFSG.KD.B4AX.RP u).testBit y = true

theorem ra_inj {u v : ℕ} (hu : u < 12) (hv : v < 12)
    (h : CFSG.KD.B4AX.RA.getD u 0 = CFSG.KD.B4AX.RA.getD v 0) : u = v := by
  obtain ⟨hl, hnd, -⟩ := rel_data
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h
  exact (List.Nodup.getElem_inj_iff hnd).1 h

theorem rel_at {u : ℕ} (hu : u < 12) {x y : Fin 31671} (hx : (x : ℕ) = CFSG.KD.B4AX.RA.getD u 0) :
    Rel x y ↔ (planeAt CFSG.KD.B4AX.RP u).testBit y = true := by
  constructor
  · rintro ⟨v, hv, hxv, hy⟩
    rw [ra_inj hu hv (hx.symm.trans hxv)]
    exact hy
  · exact fun h => ⟨u, hu, hx, h⟩

@[expose] noncomputable def relStab : Subgroup (Equiv.Perm (Fin 31671)) where
  carrier := {σ | ∀ x y, Rel (σ x) (σ y) ↔ Rel x y}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x y => by
    change Rel (a (b x)) (a (b y)) ↔ _
    rw [ha, hb]
  inv_mem' := fun {a} ha x y => by
    have h := ha (a⁻¹ x) (a⁻¹ y)
    rw [show a (a⁻¹ x) = x by simp, show a (a⁻¹ y) = y by simp] at h
    exact h.symm

section

theorem planeAt_apP {w : List ℕ} (hw : ∀ c ∈ w, c < 10) (X u : ℕ) (hu : u < 12) (r : Fin 31671) :
    (planeAt (apP CFSG.KD.YMY432F.Nf 12 w X) u).testBit r =
      (planeAt X u).testBit (rho432F (evalWord (yGen 4 3 2) w) r) := by
  rw [testBit_planeAt _ _ _ (by omega), testBit_planeAt _ _ _ (by omega)]
  exact apP_spec w hw 12 X u r hu r.2

theorem stab_rel : (nodeSub 33).map rho432F ≤ relStab := by
  rw [nodeSub, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨g, ⟨hs, hj⟩, rfl⟩, rfl⟩
  obtain ⟨h5, hrd, hrw⟩ := stab_red hs
  rw [hrd] at hs hj
  obtain ⟨hl, hnd, hlt, hl3, hall, hperm, hlen⟩ := rel_data
  obtain ⟨i, hi, hgi⟩ := hall _ h5 hs hj
  obtain ⟨hpt, hpl⟩ := rel_planes
  have hc := rel_ok i hi
  unfold CFSG.KD.B4AX.relChk at hc
  rw [andB_iff, hgi] at hc
  have hw := wList_lt (rw_stab_lt _ h5 hs)
  set σ := (CFSG.KD.B4AX.RS.getD i (0, [])).2
  set ρg := rho432F (evalWord (yGen 4 3 2) (wList (CFSG.KD.B4A.RW (g % 8192))))
  have hval : rho432F (wVal (yGen 4 3 2) (CFSG.KD.B4A.RW g)) = ρg := by rw [wVal, hrw]
  rw [hval]
  have hR : ∀ u < 12, ∀ r : Fin 31671, (planeAt CFSG.KD.B4AX.RP u).testBit (ρg r) =
      (planeAt CFSG.KD.B4AX.RP (σ.getD u 0)).testBit r := by
    intro u hu r
    rw [← planeAt_apP hw _ u hu, Nat.eq_of_beq_eq_true hc.1, (hpl i hi u hu).1]
  have hA : ∀ u < 12, ∀ r : Fin 31671, ((ρg r : ℕ) = CFSG.KD.B4AX.RA.getD u 0) ↔
      ((r : ℕ) = CFSG.KD.B4AX.RA.getD (σ.getD u 0) 0) := by
    intro u hu r
    have h1 := planeAt_apP hw (ptPlanes CFSG.KD.B4AX.RA) u hu r
    rw [Nat.eq_of_beq_eq_true hc.2, (hpl i hi u hu).2, hpt u hu, shl1, shl1,
      Nat.testBit_two_pow, Nat.testBit_two_pow] at h1
    simp only [decide_eq_decide] at h1
    constructor <;> intro h <;> [exact (h1.2 h.symm).symm; exact (h1.1 h.symm).symm]
  have hσlt : ∀ u < 12, σ.getD u 0 < 12 := by
    intro u hu
    have := hperm i hi
    have hm : σ.getD u 0 ∈ σ := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen i hi]; exact hu)]
      exact List.getElem_mem _
    have := (List.Perm.mem_iff this).1 hm
    simpa using this
  have hσsurj : ∀ v < 12, ∃ u < 12, σ.getD u 0 = v := by
    intro v hv
    have hm : v ∈ σ := (List.Perm.mem_iff (hperm i hi)).2 (by simpa using hv)
    obtain ⟨u, hu, rfl⟩ := List.mem_iff_getElem.1 hm
    exact ⟨u, by rw [hlen i hi] at hu; exact hu, by rw [List.getD_eq_getElem _ _ hu]⟩
  intro x y
  constructor
  · rintro ⟨u, hu, hxu, hyu⟩
    refine ⟨σ.getD u 0, hσlt u hu, (hA u hu x).1 hxu, ?_⟩
    rw [← hR u hu]
    exact hyu
  · rintro ⟨v, hv, hxv, hyv⟩
    obtain ⟨u, hu, rfl⟩ := hσsurj v hv
    exact ⟨u, hu, (hA u hu x).2 hxv, by rw [hR u hu]; exact hyv⟩

theorem wit_not_mem {i : ℕ} (hi : i < 12) :
    lab ⟨CFSG.KD.B4AX.WW.getD i 0, (hub_data.2.1 i hi).1⟩ ∉ (nodeSub 33).map rho432F := by
  intro hm
  obtain ⟨hw, hτ, hu, hb⟩ := hub_data.2.1 i hi
  have hc := wit_ok i hi
  unfold CFSG.KD.B4AX.witChk at hc
  simp only [andB_iff] at hc
  obtain ⟨hhub, hbit, hfa, hfb⟩ := hc
  have hl := rho_dpW jComm hτ hw hhub
  set L := lab ⟨CFSG.KD.B4AX.WW.getD i 0, hw⟩
  have ha : CFSG.KD.B4AX.RA.getD (CFSG.KD.B4AX.WI.getD i 0) 0 < 31671 :=
    rel_data.2.2.1 _ (by
      rw [List.getD_eq_getElem _ _ (by rw [rel_data.1]; exact hu)]
      exact List.getElem_mem _)
  obtain ⟨a, ha'⟩ : ∃ a : Fin 31671, (a : ℕ) = CFSG.KD.B4AX.RA.getD (CFSG.KD.B4AX.WI.getD i 0) 0 :=
    ⟨⟨_, ha⟩, rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b : Fin 31671, (b : ℕ) = CFSG.KD.B4AX.WB.getD i 0 := ⟨⟨_, hb⟩, rfl⟩
  rw [← ha'] at hfa
  rw [← hb'] at hfb hbit
  have hLa : L a = a := by
    have h1 := congrArg (fun x => x.testBit a) (Nat.eq_of_beq_eq_true hfa)
    rw [apP1_spec (dpW_lt hτ), hl, shl1, Nat.testBit_two_pow_self,
      Nat.testBit_two_pow] at h1
    exact Fin.ext (of_decide_eq_true h1).symm
  have hLb : (planeAt CFSG.KD.B4AX.RP (CFSG.KD.B4AX.WI.getD i 0)).testBit (L b) = false := by
    have h1 := congrArg (fun x => x.testBit (L b)) (Nat.eq_of_beq_eq_true hfb)
    rw [nland, Nat.testBit_and, Nat.zero_testBit, apP1_spec (dpW_lt hτ), hl] at h1
    have hLL : L (L b) = b := by
      rw [← Equiv.Perm.mul_apply, lab_sq labFacts, Equiv.Perm.one_apply]
    rw [hLL, shl1, Nat.testBit_two_pow_self, Bool.true_and] at h1
    exact h1
  have hR0 : ∀ x y, Rel (L x) (L y) ↔ Rel x y := stab_rel hm
  have hR := hR0 a b
  rw [hLa, rel_at hu ha', rel_at hu ha'] at hR
  have hbit' : (planeAt CFSG.KD.B4AX.RP (CFSG.KD.B4AX.WI.getD i 0)).testBit b = true := by
    rwa [CFSG.KC.YModel.Chain.bitB_eq] at hbit
  rw [hR.2 hbit'] at hLb
  exact absurd hLb (by decide)

theorem hubsOK_spec : ∀ {H : List (ℕ × List ℕ)}, CFSG.KD.B4AX.hubsOK H = true →
    ∀ h ∈ H, hubOK CFSG.KD.YMY432F.Nf h.1 h.2 = true
  | [], _, _, hh => absurd hh (by simp)
  | h' :: H, hH, h, hh => by
    change CFSG.KC.B4A.andB (hubOK CFSG.KD.YMY432F.Nf h'.1 h'.2) (CFSG.KD.B4AX.hubsOK H) = true at hH
    rw [andB_iff] at hH
    rcases List.mem_cons.1 hh with rfl | hh
    · exact hH.1
    · exact hubsOK_spec hH.2 h hh

theorem node_spec {k : ℕ} (hk : k < 22) :
    (∀ h ∈ CFSG.KD.B4AX.NH.getD k [], hubOK CFSG.KD.YMY432F.Nf h.1 h.2 = true) ∧
    popc 15 (Xs k) = CFSG.KD.B4AX.NX.getD k 0 := by
  have h := node_ok k hk
  unfold CFSG.KD.B4AX.nodeChk at h
  rw [andB_iff] at h
  exact ⟨hubsOK_spec h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem testBit_stuck {j r : ℕ} (h : (CFSG.KD.B4AX.stuckSet j).testBit r = true) :
    j = 33 ∧ ∃ i < 12, CFSG.KD.B4AX.WW.getD i 0 = r := by
  unfold CFSG.KD.B4AX.stuckSet at h
  cases hj : Nat.beq j 33
  · rw [hj] at h
    exact absurd h (by simp)
  · rw [hj] at h
    have h : (List.rec (motive := fun _ => ℕ) 0 (fun w _ acc => Nat.lor acc (Nat.shiftLeft 1 w))
      CFSG.KD.B4AX.WW).testBit r = true := h
    refine ⟨Nat.eq_of_beq_eq_true hj, ?_⟩
    have key : ∀ (W : List ℕ), (List.rec (motive := fun _ => ℕ) 0
        (fun w _ acc => Nat.lor acc (Nat.shiftLeft 1 w)) W).testBit r = true → r ∈ W := by
      intro W
      induction W with
      | nil => intro h; exact absurd h (by simp)
      | cons w W ih =>
        intro h
        change (Nat.lor _ (Nat.shiftLeft 1 w)).testBit r = true at h
        rw [nlor, Nat.testBit_or, shl1, Nat.testBit_two_pow, Bool.or_eq_true] at h
        rcases h with h | h
        · exact List.mem_cons_of_mem _ (ih h)
        · exact List.mem_cons.2 (Or.inl (of_decide_eq_true h).symm)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (key CFSG.KD.B4AX.WW h)
    have hl := hub_data.2.2.1
    exact ⟨i, by omega, by rw [List.getD_eq_getElem _ _ hi]⟩

theorem mem_X {k : ℕ} (hk : k < 22) (ω : Fin 31671)
    (hm : lab ω ∈ (nodeSub (CFSG.KD.B4AX.NJ.getD k 0)).map rho432F) : (Xs k).testBit ω = true := by
  by_contra hne
  rw [Bool.not_eq_true] at hne
  unfold Xs at hne
  rw [nland, Nat.testBit_and, nxor, Nat.testBit_xor, testBit_allP ω.2] at hne
  cases hX : (nodeX CFSG.KD.YMY432F.Nf (CFSG.KD.B4AX.NY.getD k 0) CFSG.KD.B4AX.F0
      (CFSG.KD.B4AX.NH.getD k [])).testBit ω
  · obtain ⟨h, hh, he⟩ := nodeX_spec _ ω hX
    obtain ⟨hp, hτ⟩ := hub_data.1 k hk h hh
    obtain ⟨hne', hside⟩ := hubE_spec labFacts hτ hp ((node_spec hk).1 h hh) f0_spec ω he
    refine not_mem_of_hub labFacts (Y := {r | (CFSG.KD.B4AX.NY.getD k 0).testBit r = true})
      (fun σ hσ r => ?_) hne' ?_ hm
    · have := stab_Y hk hσ r
      simp only [Set.mem_setOf_eq, this]
    · simp only [Set.mem_setOf_eq]
      rw [hside]
      cases (CFSG.KD.B4AX.NY.getD k 0).testBit h.1 <;> simp
  · rw [hX, Bool.true_and, Bool.true_xor, Bool.not_eq_false'] at hne
    obtain ⟨h33, i, hi, hw⟩ := testBit_stuck hne
    rw [h33] at hm
    apply wit_not_mem hi
    have e : (⟨CFSG.KD.B4AX.WW.getD i 0, (hub_data.2.1 i hi).1⟩ : Fin 31671) = ω := Fin.ext hw
    rw [e]
    exact hm

theorem testBit_nodeX_ge {Y F0 : ℕ} : ∀ (H : List (ℕ × List ℕ)) {r : ℕ}, 31671 ≤ r →
    (nodeX CFSG.KD.YMY432F.Nf Y F0 H).testBit r = false
  | [], r, hr => by
    change (Nat.sub (Nat.shiftLeft 1 31671) 1).testBit r = false
    exact testBit_ones_sub_ge hr
  | h :: H, r, hr => by
    have ih := testBit_nodeX_ge (Y := Y) (F0 := F0) H hr
    change (Nat.land (nodeX CFSG.KD.YMY432F.Nf Y F0 H) _).testBit r = false
    rw [nland, Nat.testBit_and, ih, Bool.false_and]

theorem card_X {k : ℕ} (hk : k < 22) :
    (Finset.univ.filter fun ω : Fin 31671 => (Xs k).testBit ω = true).card =
      CFSG.KD.B4AX.NX.getD k 0 := by
  have hge : ∀ r, 31671 ≤ r → (Xs k).testBit r = false := by
    intro r hr
    unfold Xs
    rw [nland, Nat.testBit_and, testBit_nodeX_ge _ hr, Bool.false_and]
  have hlt : Xs k < 2 ^ 2 ^ 15 := Nat.lt_pow_two_of_testBit _ fun r hr => hge r (by
    have : (2 : ℕ) ^ 15 = 32768 := by norm_num
    omega)
  rw [← (node_spec hk).2, Sch.popc_eq 15 _ hlt]
  have hsplit : ∑ r ∈ Finset.range (2 ^ 15), ((Xs k).testBit r).toNat =
      ∑ r ∈ Finset.range 31671, ((Xs k).testBit r).toNat := by
    have e : Finset.range (2 ^ 15) = Finset.range 31671 ∪ Finset.Ico 31671 (2 ^ 15) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by norm_num)
        (by norm_num)]
    rw [e, Finset.sum_union (by
      rw [Finset.range_eq_Ico]
      exact Finset.Ico_disjoint_Ico_consecutive _ _ _)]
    have h0 : ∑ r ∈ Finset.Ico 31671 (2 ^ 15), ((Xs k).testBit r).toNat = 0 :=
      Finset.sum_eq_zero fun r hr => by
        rw [hge r (Finset.mem_Ico.1 hr).1]
        rfl
    rw [h0, add_zero]
  rw [hsplit, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  cases (Xs k).testBit r <;> rfl

end

end CertificateChecks.KernelB433

end
