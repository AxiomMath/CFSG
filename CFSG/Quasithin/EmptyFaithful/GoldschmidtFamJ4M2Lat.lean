module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Id

public section

namespace CFSG.Quasithin.J4M2

open CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

@[expose] def Tbar : Subgroup (Equiv.Perm (Fin 77)) := Subgroup.closure {x | x ∈ tPerms}

@[expose] def Mbar : Subgroup (Equiv.Perm (Fin 77)) :=
  Subgroup.closure {x | x ∈ oddPerms ++ tPerms}

@[expose] def Stab0 : Subgroup (Equiv.Perm (Fin 77)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 77)) (0 : Fin 77)

@[expose] def StabI5 : Subgroup (Equiv.Perm (Fin 77)) where
  carrier := {g | ∀ i ∈ i5Fin, g i ∈ i5Fin}
  mul_mem' := fun {g h} hg hh i hi => hg (h i) (hh i hi)
  one_mem' := fun i hi => hi
  inv_mem' := by
    intro g hg i hi
    have hsub : i5Fin.toFinset.image g ⊆ i5Fin.toFinset := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact List.mem_toFinset.2 (hg y (List.mem_toFinset.1 hy))
    have heq : i5Fin.toFinset.image g = i5Fin.toFinset :=
      Finset.eq_of_subset_of_card_le hsub (Finset.card_image_of_injective _ g.injective).ge
    have hi' : i ∈ i5Fin.toFinset.image g := by
      rw [heq]
      exact List.mem_toFinset.2 hi
    obtain ⟨y, hy, hyi⟩ := Finset.mem_image.1 hi'
    have hgi : g⁻¹ i = y := by rw [← hyi]; exact g.symm_apply_apply y
    rw [hgi]
    exact List.mem_toFinset.1 hy

theorem Stab0_iff {g : Equiv.Perm (Fin 77)} : g ∈ Stab0 ↔ g 0 = 0 := by
  rw [Stab0, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

theorem mem_StabI5_iff {g : Equiv.Perm (Fin 77)} : g ∈ StabI5 ↔ ∀ i ∈ i5Fin, g i ∈ i5Fin :=
  Iff.rfl

theorem fix0_iff (σ : Equiv.Perm (Fin 77)) : fix0 (RN.enc σ) = true ↔ σ ∈ Stab0 := by
  have h0 : (RN.enc σ).val[0] = σ 0 := RN.enc_get σ 0
  rw [Stab0_iff, fix0, beq_iff_eq, h0]

theorem presI5_iff (σ : Equiv.Perm (Fin 77)) : presI5 (RN.enc σ) = true ↔ σ ∈ StabI5 := by
  simp only [presI5, List.all_eq_true, List.contains_iff_mem, RN.enc_get]
  exact Iff.rfl

theorem chkT_closed :
    closedH (tPerms.map RN.enc) (elts RN.enc 64 tPerms) = true := by
  have h := chkT_true
  unfold chkT at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := h
  exact h1

theorem chkT_size : (elts RN.enc 64 tPerms).size = 256 := by
  have h := chkT_true
  unfold chkT at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, h2⟩, -⟩, -⟩ := h
  exact beq_iff_eq.1 h2

theorem chkT_tGens :
    ∀ g ∈ tGens, (elts RN.enc 64 tPerms).contains (phiRN g) = true := by
  have h := chkT_true
  unfold chkT at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h4⟩ := h
  exact List.all_eq_true.1 h4

theorem mem_Tbar_iff (x : Equiv.Perm (Fin 77)) :
    x ∈ Tbar ↔ RN.enc x ∈ elts RN.enc 64 tPerms :=
  mem_closure_iff_H (rawIsEnc 77) tPerms 64 chkT_closed x

theorem card_Tbar : Nat.card ↥Tbar = 256 := by
  have h := card_closure_of_closedH (rawIsEnc 77) tPerms 64 chkT_closed
  show Nat.card ↥(Subgroup.closure {x | x ∈ tPerms}) = 256
  rw [h]
  exact chkT_size

theorem chkClass_p0 {g : Equiv.Perm (Fin 77)}
    (hg : g ∈ p0Perms) : g ∈ Stab0 ∧ g ∈ StabI5 := by
  have h := chkClass_true
  unfold chkClass at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, h2⟩ := h
  have h3 := List.all_eq_true.1 h2 g hg
  rw [Bool.and_eq_true] at h3
  exact ⟨(fix0_iff g).1 h3.1, (presI5_iff g).1 h3.2⟩

theorem sigPerm_mem_p0Perms {j n : ℕ} (hj : j < 15) (hn : n = 17 + j) :
    sigPerm n ∈ p0Perms := by
  unfold p0Perms
  rw [List.mem_map]
  exact ⟨j, List.mem_range.2 hj, by rw [hn]⟩

theorem tPerms_subset_p0Perms {g : Equiv.Perm (Fin 77)} (hg : g ∈ tPerms) : g ∈ p0Perms := by
  simp only [tPerms, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h
  · rw [h]
    exact sigPerm_mem_p0Perms (j := 11) (by norm_num) (by norm_num)
  · rw [h]
    exact sigPerm_mem_p0Perms (j := 12) (by norm_num) (by norm_num)
  · rw [h]
    exact sigPerm_mem_p0Perms (j := 13) (by norm_num) (by norm_num)
  · rw [h]
    exact sigPerm_mem_p0Perms (j := 0) (by norm_num) (by norm_num)

theorem Tbar_le_Stab0 : Tbar ≤ Stab0 := by
  rw [Tbar, Subgroup.closure_le]
  intro g hg
  exact (chkClass_p0 (tPerms_subset_p0Perms hg)).1

theorem Tbar_le_StabI5 : Tbar ≤ StabI5 := by
  rw [Tbar, Subgroup.closure_le]
  intro g hg
  exact (chkClass_p0 (tPerms_subset_p0Perms hg)).2

theorem MbarP_le_Mbar : MbarP ≤ Mbar :=
  Subgroup.closure_mono fun _ hx => List.mem_append_left _ hx

theorem Tbar_le_Mbar : Tbar ≤ Mbar :=
  Subgroup.closure_mono fun _ hx => List.mem_append_right _ hx

theorem Tbar_not_le_MbarP :
    ¬ Tbar ≤ MbarP := by
  intro h
  have := Subgroup.card_dvd_of_le h
  rw [card_Tbar, card_MbarP] at this
  omega

theorem mem_MbarP_or_mul_inv_mem
    (hMcard : Nat.card ↥Mbar = 887040) {t y : Equiv.Perm (Fin 77)} (ht : t ∈ Mbar)
    (htn : t ∉ MbarP) (hy : y ∈ Mbar) : y ∈ MbarP ∨ y * t⁻¹ ∈ MbarP := by
  have hidx : (MbarP.subgroupOf Mbar).index = 2 := by
    have h1 := Subgroup.card_mul_index (MbarP.subgroupOf Mbar)
    have h2 : Nat.card ↥(MbarP.subgroupOf Mbar) = Nat.card ↥MbarP :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe MbarP_le_Mbar).toEquiv
    rw [h2, card_MbarP, hMcard] at h1
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hidx
  by_cases hyP : y ∈ MbarP
  · exact Or.inl hyP
  · right
    have hy' : (⟨y, hy⟩ : ↥Mbar) ∉ MbarP.subgroupOf Mbar := hyP
    have ht' : (⟨t, ht⟩ : ↥Mbar) ∉ MbarP.subgroupOf Mbar := htn
    have h1 : (⟨y, hy⟩ : ↥Mbar) * a ∈ MbarP.subgroupOf Mbar := by
      rcases ha ⟨y, hy⟩ with ⟨h, -⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hy'
    have h2 : (⟨t, ht⟩ : ↥Mbar) * a ∈ MbarP.subgroupOf Mbar := by
      rcases ha ⟨t, ht⟩ with ⟨h, -⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h ht'
    have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    have h4 : (⟨y, hy⟩ : ↥Mbar) * a * ((⟨t, ht⟩ : ↥Mbar) * a)⁻¹ =
        (⟨y, hy⟩ : ↥Mbar) * (⟨t, ht⟩ : ↥Mbar)⁻¹ := by group
    rw [h4] at h3
    exact Subgroup.mem_subgroupOf.1 h3

theorem le_of_forall_Phi_mem
    (hMcard : Nat.card ↥Mbar = 887040) {Y S : Subgroup (Equiv.Perm (Fin 77))} (hT : Tbar ≤ Y)
    (hM : Y ≤ Mbar) (hTS : Tbar ≤ S)
    (hYS : ∀ x : ↥NativeSporadic.M22, Phi x ∈ Y → Phi x ∈ S) : Y ≤ S := by
  obtain ⟨t, htT, htn⟩ := IsConcreteLE.not_le_iff_exists.1 Tbar_not_le_MbarP
  intro y hy
  rcases mem_MbarP_or_mul_inv_mem hMcard (Tbar_le_Mbar htT) htn (hM hy) with hyP | hyP
  · rw [← range_Phi] at hyP
    obtain ⟨x, rfl⟩ := hyP
    exact hYS x hy
  · have hyt : y * t⁻¹ ∈ Y := Y.mul_mem hy (Y.inv_mem (hT htT))
    rw [← range_Phi] at hyP
    obtain ⟨x, hx⟩ := hyP
    rw [← hx] at hyt
    have h1 : Phi x ∈ S := hYS x hyt
    rw [hx] at h1
    have h2 := S.mul_mem h1 (hTS htT)
    simpa using h2

theorem eq_Mbar_of_MbarP_le
    (hMcard : Nat.card ↥Mbar = 887040) {Y : Subgroup (Equiv.Perm (Fin 77))} (hT : Tbar ≤ Y)
    (hM : Y ≤ Mbar) (hP : MbarP ≤ Y) : Y = Mbar := by
  have hd := Subgroup.card_dvd_of_le hP
  have hle := Subgroup.card_le_of_le hM
  rw [card_MbarP] at hd
  rw [hMcard] at hle
  have hne : Nat.card ↥Y ≠ 443520 := by
    intro h
    have hYP : MbarP = Y := Subgroup.eq_of_le_of_card_ge hP (by rw [h, card_MbarP])
    exact Tbar_not_le_MbarP (hYP ▸ hT)
  have hpos : 0 < Nat.card ↥Y := Nat.card_pos
  exact Subgroup.eq_of_le_of_card_ge hM (by rw [hMcard]; omega)

theorem mem_map_comap_Phi_iff {Y : Subgroup (Equiv.Perm (Fin 77))}
    (x : ↥NativeSporadic.M22) :
    (x : Equiv.Perm (Fin 22)) ∈ (Y.comap Phi).map NativeSporadic.M22.subtype ↔ Phi x ∈ Y := by
  constructor
  · rintro ⟨k, hk, hkx⟩
    have hkx' : k = x := Subtype.ext hkx
    rw [← hkx']
    exact hk
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem Phi_mem_of_mem_closure
    {S : Subgroup (Equiv.Perm (Fin 77))} {L : List (Equiv.Perm (Fin 22))}
    (hLM : Subgroup.closure {g | g ∈ L} ≤ NativeSporadic.M22)
    (hL : ∀ g (hg : g ∈ NativeSporadic.M22), g ∈ L → Phi ⟨g, hg⟩ ∈ S)
    {x : ↥NativeSporadic.M22} (hx : (x : Equiv.Perm (Fin 22)) ∈ Subgroup.closure {g | g ∈ L}) :
    Phi x ∈ S := by
  have h : Subgroup.closure {g | g ∈ L} ≤ (S.comap Phi).map NativeSporadic.M22.subtype := by
    rw [Subgroup.closure_le]
    intro g hg
    exact ⟨⟨g, hLM (Subgroup.subset_closure hg)⟩, hL g _ hg, rfl⟩
  exact (mem_map_comap_Phi_iff x).1 (h hx)

theorem Phi_mem_Stab0_of_fix0 {g : Equiv.Perm (Fin 22)}
    (hg : g ∈ NativeSporadic.M22) (h : fix0 (phiRN g) = true) : Phi ⟨g, hg⟩ ∈ Stab0 := by
  rw [← fix0_iff, RN_enc_Phi]
  exact h

theorem Phi_mem_StabI5_of_presI5 {g : Equiv.Perm (Fin 22)}
    (hg : g ∈ NativeSporadic.M22) (h : presI5 (phiRN g) = true) : Phi ⟨g, hg⟩ ∈ StabI5 := by
  rw [← presI5_iff, RN_enc_Phi]
  exact h

theorem chkClass_members {j : ℕ} (hj : j < 6) (hj4 : j ≠ 4) :
    (∀ g ∈ members.getD j [], fix0 (phiRN g) = true) ∨
      (∀ g ∈ members.getD j [], presI5 (phiRN g) = true) := by
  have h := chkClass_true
  unfold chkClass at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  have h2 := List.all_eq_true.1 h1 j (List.mem_range.2 hj)
  simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h2
  rcases h2 with (h2 | h2) | h2
  · exact absurd h2 hj4
  · exact Or.inl h2
  · exact Or.inr h2

theorem tGens_closure_le_M22 :
    Subgroup.closure {g | g ∈ cert.tGens} ≤ NativeSporadic.M22 := by
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  obtain ⟨j, hj, hLM, hYL, hcard⟩ := cert.overgroup_cases_idx (rawIsEnc 22) hck
    ((Subgroup.closure {g | g ∈ cert.tGens}).subgroupOf
      (Subgroup.closure {g | g ∈ cert.mGens})) le_rfl
  have hLT : Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[j]} ≤
      Subgroup.closure {g | g ∈ cert.tGens} := by
    intro x hx
    have h1 : (⟨x, hLM hx⟩ : ↥(Subgroup.closure {g | g ∈ cert.mGens})) ∈
        (Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[j]}).subgroupOf
          (Subgroup.closure {g | g ∈ cert.mGens}) := Subgroup.mem_subgroupOf.2 hx
    rw [← hYL] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hle := Subgroup.card_le_of_le hLT
  rw [hcard, cert.card_t (rawIsEnc 22) hcl hsz] at hle
  have hlen : (cert.tGens :: cert.lat).length = 6 := rfl
  have hj6 : j < 6 := lt_of_lt_of_eq hj hlen
  rw [← mGens_closure]
  interval_cases j
  · exact hLM
  all_goals exact absurd hle (by decide)

theorem lattice_classification
    (hMcard : Nat.card ↥Mbar = 887040)
    {Y : Subgroup (Equiv.Perm (Fin 77))} (hT : Tbar ≤ Y) (hM : Y ≤ Mbar) :
    Y = Mbar ∨ Y ≤ Stab0 ∨ Y ≤ StabI5 := by
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hTM := tGens_closure_le_M22
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup (Equiv.Perm (Fin 22)),
      Z = (Y.comap Phi).map NativeSporadic.M22.subtype := ⟨_, rfl⟩
  have hZmem : ∀ x : ↥NativeSporadic.M22, (x : Equiv.Perm (Fin 22)) ∈ Z ↔ Phi x ∈ Y := by
    intro x
    rw [hZdef]
    exact mem_map_comap_Phi_iff x
  have hZ22 : Z ≤ NativeSporadic.M22 := by
    rw [hZdef]
    exact Subgroup.map_subtype_le _
  have hTZ : Subgroup.closure {g | g ∈ cert.tGens} ≤ Z := by
    rw [Subgroup.closure_le]
    intro g hg
    have hgM : g ∈ NativeSporadic.M22 := hTM (Subgroup.subset_closure hg)
    refine (hZmem ⟨g, hgM⟩).2 (hT ((mem_Tbar_iff _).2 ?_))
    rw [RN_enc_Phi]
    exact Std.HashSet.contains_iff_mem.1 (chkT_tGens g hg)
  obtain ⟨L, hL, hZL⟩ := cert.overgroups (rawIsEnc 22) hck Z hTZ
    (hZ22.trans mGens_closure.symm.le)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hL
  have hlen : (cert.tGens :: cert.lat).length = 6 := rfl
  have hj6 : j < 6 := lt_of_lt_of_eq hj hlen
  have hLM : Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[j]} ≤ NativeSporadic.M22 :=
    hZL ▸ hZ22
  have hYL : ∀ x : ↥NativeSporadic.M22, Phi x ∈ Y →
      (x : Equiv.Perm (Fin 22)) ∈ Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[j]} :=
    fun x hx => hZL ▸ (hZmem x).2 hx
  by_cases hj4 : j = 4
  · left
    subst hj4
    have hcard := cert.card_member_idx (rawIsEnc 22) hcl hsz 4 hj
    have h4 : cert.sizes.getD 4 0 = 443520 := rfl
    rw [← hZL, h4] at hcard
    have hZeq : Z = NativeSporadic.M22 :=
      Subgroup.eq_of_le_of_card_ge hZ22 (by rw [CFSG.Sporadic.Mathieu.card_M22, hcard])
    have hall : ∀ x : ↥NativeSporadic.M22, Phi x ∈ Y := fun x => (hZmem x).1 (hZeq ▸ x.2)
    refine eq_Mbar_of_MbarP_le hMcard hT hM ?_
    rw [← range_Phi]
    rintro _ ⟨x, rfl⟩
    exact hall x
  · have hmem : members.getD j [] = (cert.tGens :: cert.lat)[j] := List.getD_eq_getElem _ _ hj
    right
    rcases chkClass_members hj6 hj4 with hf | hp
    · left
      refine le_of_forall_Phi_mem hMcard hT hM Tbar_le_Stab0 fun x hx =>
        Phi_mem_of_mem_closure hLM (fun g hg hgL => ?_) (hYL x hx)
      exact Phi_mem_Stab0_of_fix0 hg (hf g (by rw [hmem]; exact hgL))
    · right
      refine le_of_forall_Phi_mem hMcard hT hM Tbar_le_StabI5 fun x hx =>
        Phi_mem_of_mem_closure hLM (fun g hg hgL => ?_) (hYL x hx)
      exact Phi_mem_StabI5_of_presI5 hg (hp g (by rw [hmem]; exact hgL))

end CFSG.Quasithin.J4M2
