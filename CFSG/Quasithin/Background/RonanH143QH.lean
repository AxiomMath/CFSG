module

public import CFSG.Quasithin.Background.RonanH143Hdata
public import CFSG.Quasithin.Background.RonanH143QL2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin

theorem smul_univ_image_of_perm {β : Type*} [DecidableEq β] [MulAction P24 β] {n : ℕ}
    (X : Fin n → β) {g : P24} (σ : Equiv.Perm (Fin n)) (h : ∀ i, g • X i = X (σ i)) :
    g • (Finset.univ.image X) = Finset.univ.image X := by
  ext T
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨T', hT', rfl⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hT'
    exact Finset.mem_image.2 ⟨σ i, Finset.mem_univ _, (h i).symm⟩
  · intro hT
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hT
    refine ⟨X (σ.symm j), Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [h, Equiv.apply_symm_apply]

theorem smul_TotSet_of_perm {g : P24} (σ : Equiv.Perm (Fin 6)) (h : ∀ i, g • Tot i = Tot (σ i)) :
    g • TotSet = TotSet :=
  smul_univ_image_of_perm Tot σ h

theorem exists_Tot_of_smul_TotSet {g : P24} (hg : g • TotSet = TotSet) (i : Fin 6) :
    ∃ j, g • Tot i = Tot j := by
  have hmem : g • Tot i ∈ TotSet := by
    rw [← hg]
    exact Finset.smul_mem_smul_finset (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  obtain ⟨j, hj⟩ := (mem_TotSet_iff _).1 hmem
  exact ⟨j, hj.symm⟩

@[expose] def MHt : Subgroup P24 := MY mog22plus Hstd ⊓ MulAction.stabilizer P24 TotSet

theorem mem_MHt_iff {g : P24} : g ∈ MHt ↔ g ∈ MY mog22plus Hstd ∧ g • TotSet = TotSet := by
  simp [MHt, MulAction.mem_stabilizer_iff]

theorem exists_piHt :
    ∃ π : ↥MHt →* Equiv.Perm (Fin 6), ∀ (g : ↥MHt) (i : Fin 6), Tot (π g i) = (g : P24) • Tot i :=
  exists_labAct Tot Tot_injective MHt fun g hg i =>
    exists_Tot_of_smul_TotSet (mem_MHt_iff.1 hg).2 i

noncomputable def piHt : ↥MHt →* Equiv.Perm (Fin 6) := Classical.choose exists_piHt

theorem piHt_spec (g : ↥MHt) (i : Fin 6) : Tot (piHt g i) = (g : P24) • Tot i :=
  Classical.choose_spec exists_piHt g i

theorem piHt_eq_of_smul (g : ↥MHt) (σ : Equiv.Perm (Fin 6)) (h : ∀ i, (g : P24) • Tot i = Tot (σ i)) :
    piHt g = σ :=
  labAct_eq_of_smul Tot Tot_injective MHt piHt piHt_spec g σ h

theorem mem_MY_H_plus {g : P24} (hg : g ∈ mog22plus) (hH : g • Hstd = Hstd) :
    g ∈ MY mog22plus Hstd :=
  mem_MY_iff.2 ⟨hg, hH⟩

theorem ko_mem_MHt (t : Fin 16) : koPerm t ∈ MHt := by
  rw [mem_MHt_iff]
  exact ⟨mem_MY_H_plus (mog22_le_mog22plus (koPerm_mem_mog22 t)) (ko_smul_Hstd t),
    smul_TotSet_of_perm 1 fun i => by simpa using ko_smul_Tot t i⟩

theorem x6_mem_MHt : x6Perm ∈ MHt := by
  rw [mem_MHt_iff]
  exact ⟨mem_MY_H_plus x6Perm_mem_mog22plus x6_smul_Hstd,
    smul_TotSet_of_perm sigX x6_smul_Tot⟩

theorem tau_mem_MHt : tauPerm ∈ MHt := by
  rw [mem_MHt_iff]
  exact ⟨mem_MY_H_plus tauPerm_mem_mog22plus tau_smul_Hstd,
    smul_TotSet_of_perm sigT tau_smul_Tot⟩

theorem piHt_range_top : piHt.range = ⊤ := by
  have hm := map_closure_eq_top_of_cycle_swap piHt sigX sigX_isCycle sigX_support 1
    ⟨x6Perm, x6_mem_MHt⟩ ⟨tauPerm, tau_mem_MHt⟩ (piHt_eq_of_smul _ _ x6_smul_Tot)
    (by rw [← sigT_eq]; exact piHt_eq_of_smul _ _ tau_smul_Tot)
  exact eq_top_iff.2 (hm ▸ Subgroup.map_le_range _ _)

theorem card_MY_H_le_aux :
    Nat.card (MulAction.stabilizer ↥mog22 Hstd) * 77 ≤ 443520 ∧
      Nat.card (MulAction.stabilizer ↥mog22plus Hstd) * 77 ≤ 887040 := by
  obtain ⟨hH, -, -, hHn, -, -, hHl, -, -, hlen, -, -⟩ := bfs_checks
  have h1 := card_stab_mul_le hH hHn hHl
  have h2 := card_stab_plus_mul_le hH hHn hHl
  rw [hlen] at h1 h2
  exact ⟨h1, h2⟩

theorem card_MY_H_L_le :
    Nat.card ↥(MY mog22 Hstd) ≤ 5760 := by
  have h1 : Nat.card ↥(MY mog22 Hstd) = Nat.card (MulAction.stabilizer ↥mog22 Hstd) :=
    card_inf_stabilizer_eq (Γ := mog22) Hstd
  have := card_MY_H_le_aux.1
  omega

theorem card_MY_H_L2_le :
    Nat.card ↥(MY mog22plus Hstd) ≤ 11520 := by
  have h1 : Nat.card ↥(MY mog22plus Hstd) = Nat.card (MulAction.stabilizer ↥mog22plus Hstd) :=
    card_inf_stabilizer_eq (Γ := mog22plus) Hstd
  have := card_MY_H_le_aux.2
  omega

theorem koPerm_mem_MY_H_plus (t : Fin 16) : koPerm t ∈ MY mog22plus Hstd :=
  mem_MY_H_plus (mog22_le_mog22plus (koPerm_mem_mog22 t)) (ko_smul_Hstd t)

theorem fixO_subgroupOf_le_ker_piHt : fixO.subgroupOf MHt ≤ piHt.ker := by
  intro g hg
  obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (Subgroup.mem_subgroupOf.1 hg)
  rw [MonoidHom.mem_ker]
  refine piHt_eq_of_smul g 1 fun i => ?_
  rw [Equiv.Perm.coe_one, id_eq, ht]
  exact ko_smul_Tot t i

theorem fixO_le_MHt : fixO ≤ MHt := fun g hg => by
  obtain ⟨t, rfl⟩ := (mem_fixO_iff g).1 hg
  exact ko_mem_MHt t

theorem MHt_eq :
    MHt = MY mog22plus Hstd := by
  have hle : MHt ≤ MY mog22plus Hstd := inf_le_left
  have hker := card_eq_card_ker_mul piHt piHt_range_top
  have h16 : Nat.card ↥(fixO.subgroupOf MHt) ≤ Nat.card piHt.ker :=
    Subgroup.card_le_of_le fixO_subgroupOf_le_ker_piHt
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixO_le_MHt).toEquiv, card_fixO'] at h16
  have h2 : Nat.card ↥(MY mog22plus Hstd) ≤ Nat.card ↥MHt := by
    have := card_MY_H_L2_le
    have h720 : Nat.factorial 6 = 720 := by decide
    rw [h720] at hker
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle h2)

theorem MY_mog22_le_plus (Y : Finset (Fin 24)) : MY mog22 Y ≤ MY mog22plus Y :=
  fun g hg => by
    rw [mem_MY_iff] at hg ⊢
    exact ⟨mog22_le_mog22plus hg.1, hg.2⟩

theorem MY_H_smul_TotSet {g : P24}
    (hg : g ∈ MY mog22plus Hstd) : g • TotSet = TotSet := by
  rw [← MHt_eq] at hg
  exact (mem_MHt_iff.1 hg).2

theorem exists_piH2 :
    ∃ π : ↥(MY mog22plus Hstd) →* Equiv.Perm (Fin 6),
      ∀ (g : ↥(MY mog22plus Hstd)) (i : Fin 6), Tot (π g i) = (g : P24) • Tot i :=
  exists_labAct Tot Tot_injective (MY mog22plus Hstd) fun g hg i =>
    exists_Tot_of_smul_TotSet (MY_H_smul_TotSet hg) i

noncomputable def piH2 :
    ↥(MY mog22plus Hstd) →* Equiv.Perm (Fin 6) := Classical.choose exists_piH2

theorem piH2_spec
    (g : ↥(MY mog22plus Hstd)) (i : Fin 6) : Tot (piH2 g i) = (g : P24) • Tot i :=
  Classical.choose_spec exists_piH2 g i

theorem piH2_eq_of_smul
    (g : ↥(MY mog22plus Hstd)) (σ : Equiv.Perm (Fin 6))
    (h : ∀ i, (g : P24) • Tot i = Tot (σ i)) : piH2 g = σ :=
  labAct_eq_of_smul Tot Tot_injective _ piH2 piH2_spec g σ h

theorem x6_mem_MY_H : x6Perm ∈ MY mog22plus Hstd := mem_MY_H_plus x6Perm_mem_mog22plus x6_smul_Hstd

theorem tau_mem_MY_H : tauPerm ∈ MY mog22plus Hstd :=
  mem_MY_H_plus tauPerm_mem_mog22plus tau_smul_Hstd

theorem piH2_range_top :
    piH2.range = ⊤ := by
  have hm := map_closure_eq_top_of_cycle_swap piH2 sigX sigX_isCycle sigX_support 1
    ⟨x6Perm, x6_mem_MY_H⟩ ⟨tauPerm, tau_mem_MY_H⟩ (piH2_eq_of_smul _ _ x6_smul_Tot)
    (by rw [← sigT_eq]; exact piH2_eq_of_smul _ _ tau_smul_Tot)
  exact eq_top_iff.2 (hm ▸ Subgroup.map_le_range _ _)

theorem fixO_le_MY_H_plus : fixO ≤ MY mog22plus Hstd := fun g hg => by
  obtain ⟨t, rfl⟩ := (mem_fixO_iff g).1 hg
  exact koPerm_mem_MY_H_plus t

theorem ker_piH2 :
    piH2.ker = fixO.subgroupOf (MY mog22plus Hstd) := by
  refine ker_eq_of_card_le piH2 piH2_range_top _ ?_ ?_
  · intro g hg
    obtain ⟨t, ht⟩ := (mem_fixO_iff _).1 (Subgroup.mem_subgroupOf.1 hg)
    rw [MonoidHom.mem_ker]
    refine piH2_eq_of_smul g 1 fun i => ?_
    rw [Equiv.Perm.coe_one, id_eq, ht]
    exact ko_smul_Tot t i
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixO_le_MY_H_plus).toEquiv, card_fixO']
    have h720 : Nat.factorial 6 = 720 := by decide
    rw [h720]
    have := card_MY_H_L2_le
    omega

theorem card_MY_H_L2 :
    Nat.card ↥(MY mog22plus Hstd) = 11520 := by
  rw [card_eq_card_ker_mul piH2 piH2_range_top, ker_piH2,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixO_le_MY_H_plus).toEquiv, card_fixO']
  decide

theorem KY_H_L2 :
    KY mog22plus Hstd = fixO :=
  pCoreOf_eq_of_ker (n := 6) (by norm_num) piH2 (Or.inl piH2_range_top) ker_piH2
    fixO_le_MY_H_plus isPGroup_fixO

noncomputable def piH1 :
    ↥(MY mog22 Hstd) →* Equiv.Perm (Fin 6) :=
  piH2.comp (Subgroup.inclusion (MY_mog22_le_plus Hstd))

theorem piH1_spec
    (g : ↥(MY mog22 Hstd)) (i : Fin 6) : Tot (piH1 g i) = (g : P24) • Tot i :=
  piH2_spec _ i

theorem fixO_le_MY_H : fixO ≤ MY mog22 Hstd := fun g hg => by
  obtain ⟨t, rfl⟩ := (mem_fixO_iff g).1 hg
  exact mem_MY_iff.2 ⟨koPerm_mem_mog22 t, ko_smul_Hstd t⟩

theorem ker_piH1 :
    piH1.ker = fixO.subgroupOf (MY mog22 Hstd) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h : piH1 g = piH2 (Subgroup.inclusion (MY_mog22_le_plus Hstd) g) := rfl
  rw [h, ← MonoidHom.mem_ker, ker_piH2, Subgroup.mem_subgroupOf]
  rfl

theorem relIndex_mog22_plus :
    mog22.relIndex mog22plus = 2 := by
  have hle : mog22 ≤ mog22plus := mog22_le_mog22plus
  have h := (mog22.subgroupOf mog22plus).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_mog22, card_mog22plus] at h
  change (mog22.subgroupOf mog22plus).index = 2
  omega

theorem index_MY_mog22_le_two :
    ((MY mog22 Hstd).subgroupOf (MY mog22plus Hstd)).index ≤ 2 := by
  have h1 : MY mog22 Hstd = mog22 ⊓ MY mog22plus Hstd := by
    rw [inf_comm, MY_plus_inf_mog22]
  have h2 : ((MY mog22 Hstd).subgroupOf (MY mog22plus Hstd)).index =
      mog22.relIndex (MY mog22plus Hstd) := by
    rw [h1, ← Subgroup.relIndex, Subgroup.inf_relIndex_right]
  rw [h2, ← relIndex_mog22_plus]
  exact Subgroup.relIndex_le_of_le_right (by
    intro g hg
    exact (mem_MY_iff.1 hg).1) (by rw [relIndex_mog22_plus]; norm_num)

theorem range_piH1 :
    piH1.range = alternatingGroup (Fin 6) := by
  have hge : alternatingGroup (Fin 6) ≤ piH1.range := by
    have h := alternatingGroup_le_map_of_index_le_two piH2 piH2_range_top
      ((MY mog22 Hstd).subgroupOf (MY mog22plus Hstd)) index_MY_mog22_le_two
    have hr : piH1.range = ((MY mog22 Hstd).subgroupOf (MY mog22plus Hstd)).map piH2 := by
      rw [piH1, MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [hr]
    exact h
  refine (Subgroup.eq_of_le_of_card_ge hge ?_).symm
  have hker : Nat.card ↥(MY mog22 Hstd) = Nat.card ↥piH1.range * Nat.card ↥piH1.ker := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup piH1.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange piH1).toEquiv] at h
    exact h
  have h16 : 16 ≤ Nat.card ↥piH1.ker := by
    rw [ker_piH1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixO_le_MY_H).toEquiv, card_fixO']
  have h5760 := card_MY_H_L_le
  have hA : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  rw [hA]
  have : Nat.card ↥piH1.range * 16 ≤ 5760 := by
    calc Nat.card ↥piH1.range * 16 ≤ Nat.card ↥piH1.range * Nat.card ↥piH1.ker :=
          Nat.mul_le_mul_left _ h16
      _ = Nat.card ↥(MY mog22 Hstd) := hker.symm
      _ ≤ 5760 := h5760
  omega

theorem KY_H_L :
    KY mog22 Hstd = fixO :=
  pCoreOf_eq_of_ker (n := 6) (by norm_num) piH1 (Or.inr range_piH1) ker_piH1
    fixO_le_MY_H isPGroup_fixO

end CFSG.Quasithin.RonanH143
