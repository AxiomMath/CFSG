module

public import CFSG.Sporadic.SuzRecog.C1ModelJ0

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.C1Model

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog

@[expose] noncomputable def T0 : Subgroup (Equiv.Perm (Fin 1782)) := J0 ⊓ invE 1

@[expose] noncomputable def t0Gen (i : ℕ) : Equiv.Perm (Fin 1782) :=
  decPerm (C1ModelData.t0Decs.getD i ([], 0))

@[expose] noncomputable def v0Gen (j : ℕ) : Equiv.Perm (Fin 1782) :=
  if j < 4 then t0Gen j else if j = 4 then Model.w0 else if j = 5 then r1 else tau0

@[expose] noncomputable def t0Conj (i : ℕ) : Equiv.Perm (Fin 1782) :=
  ((C1ModelData.t0ConjWords.getD i []).map fun k => if k = 0 then suzInv 1 else zJ0).prod

section T0

theorem decPerm_mem {d : List ℕ × ℕ} (hw : ∀ k ∈ d.1, k < 10) : decPerm d ∈ invE 1 :=
  mul_mem (wPerm_mem hw) (mul_mem (qVec_mem_invE _) (pow_mem suzInv_mem_invE _))

theorem t0Decs_ok {i : ℕ} (hi : i < 4) : (∀ k ∈ (C1ModelData.t0Decs.getD i ([], 0)).1, k < 10) ∧
    (C1ModelData.t0Decs.getD i ([], 0)).2 < 128 := by
  interval_cases i <;> decide

theorem tabRep_t0Tab {i : ℕ} (hi : i < 4) : TabRep (t0Tab i) (t0Gen i) :=
  tabRep_decTab (t0Decs_ok hi).1 (t0Decs_ok hi).2

theorem t0Tabs_get {i : ℕ} (hi : i < 4) : t0Tabs[i]! = t0Tab i := getElem!_ofFn' _ hi

theorem t0Gen_mem_invE {i : ℕ} (hi : i < 4) : t0Gen i ∈ invE 1 := decPerm_mem (t0Decs_ok hi).1

theorem t0_parts : enumOK 1782 t0Tabs t0Enum = true ∧ t0Enum.tabs.size = 64 ∧
    (∀ i < 4, comp 1782 t0Tabs[i]! w0T = comp 1782 w0T t0Tabs[i]! ∧
      comp 1782 t0Tabs[i]! r1T = comp 1782 r1T t0Tabs[i]! ∧
      comp 1782 t0Tabs[i]! rhoT = comp 1782 rhoT t0Tabs[i]!) ∧
    (∀ i < 4, comp 1782 (t0ConjTab i) tTab = comp 1782 t0Tabs[i]! (t0ConjTab i)) ∧
    e3xI.size = 1782 ∧ comp 1782 e3xI e3xT = idTab 1782 ∧
    found (indexOf t0Enum.tabs) t0Enum.tabs e3T = true := by
  have h := c1T0_check
  unfold t0Check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, beq_iff_eq.mp h2, fun i hi => ?_, fun i hi => beq_iff_eq.mp (allBelow_eq_true.mp h4 i hi),
    beq_iff_eq.mp h5, beq_iff_eq.mp h6, h7⟩
  have := allBelow_eq_true.mp h3 i hi
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem t0Gen_mem_J0 {i : ℕ} (hi : i < 4) : t0Gen i ∈ J0 := by
  have hr := tabRep_t0Tab hi
  obtain ⟨h1, h2, h3⟩ := t0_parts.2.2.1 i hi
  rw [t0Tabs_get hi] at h1 h2 h3
  exact mem_J0_iff.mpr ⟨((hr.comp tabRep_w0).eq_iff (tabRep_w0.comp hr)).mp h1,
    ((hr.comp tabRep_r1).eq_iff (tabRep_r1.comp hr)).mp h2,
    ((hr.comp tabRep_rho1).eq_iff (tabRep_rho1.comp hr)).mp h3,
    invE_le_suzM (t0Gen_mem_invE hi)⟩

theorem t0Gen_mem_T0 {i : ℕ} (hi : i < 4) : t0Gen i ∈ T0 :=
  mem_inf.mpr ⟨t0Gen_mem_J0 hi, t0Gen_mem_invE hi⟩

theorem T0_le_J0 : T0 ≤ J0 := inf_le_left

theorem T0_le_invE : T0 ≤ invE 1 := inf_le_right

theorem T0_le_V0 : T0 ≤ V0 := fun _ hg =>
  mem_V0_iff.mpr ⟨(mem_J0_iff.mp (T0_le_J0 hg)).1, T0_le_invE hg⟩

theorem T0_le_centralizer_w0 : T0 ≤ centralizer {Model.w0} := T0_le_J0.trans J0_le_centralizer_w0

theorem T0_inf_R0 : T0 ⊓ Model.R0 = ⊥ :=
  eq_bot_iff.mpr (J0_inf_R0 ▸ inf_le_inf_right _ T0_le_J0)

theorem enumerates_closure_t0Gen :
    Enumerates (closure {g | ∃ i < 4, t0Gen i = g}) t0Enum.tabs.toList := by
  have hsize : t0Tabs.size = 4 := Array.size_ofFn
  refine enumerates_closure (fun a ha => ?_) (fun j hj => ?_) t0_parts.1
  · obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨i, by rw [hsize]; exact hi, by rw [t0Tabs_get hi]; exact tabRep_t0Tab hi⟩
  · rw [hsize] at hj
    exact ⟨_, ⟨j, hj, rfl⟩, by rw [t0Tabs_get hj]; exact tabRep_t0Tab hj⟩

theorem closure_t0Gen_le_T0 : closure {g | ∃ i < 4, t0Gen i = g} ≤ T0 := by
  rw [closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact t0Gen_mem_T0 hi

theorem card_T0_le : Nat.card T0 ≤ 64 := by
  have hcr : ∀ {g : Equiv.Perm (Fin 1782)}, g ∈ T0 → g ∈ centralizer {r1} := fun hg =>
    mem_centralizer_singleton_iff.mpr (mem_J0_iff.mp (T0_le_J0 hg)).2.1
  have h1 : Nat.card T0 * Nat.card Model.R0 ≤ Nat.card ↥(V0 ⊓ centralizer {r1}) :=
    card_mul_card_le_of_inf_eq_bot T0_inf_R0 fun a ha b hb =>
      mem_inf.mpr ⟨mul_mem (T0_le_V0 ha) (R0_le_V0 hb), mul_mem (hcr ha)
        (mem_centralizer_singleton_iff.mpr (R0_comm hb r1_mem_R0))⟩
  have h2 : 2 * Nat.card ↥(V0 ⊓ centralizer {r1}) ≤ Nat.card V0 :=
    two_mul_card_le inf_le_left tau0_mem_V0 fun h =>
      tau0_not_comm_r1 (mem_centralizer_singleton_iff.mp (mem_inf.mp h).2)
  rw [card_R0] at h1
  rw [card_V0] at h2
  omega

theorem card_T0 : Nat.card T0 = 64 := by
  refine le_antisymm card_T0_le ?_
  have h := card_le_of_le closure_t0Gen_le_T0
  rwa [enumerates_closure_t0Gen.card, Array.length_toList, t0_parts.2.1] at h

theorem T0_eq : T0 = closure {g | ∃ i < 4, t0Gen i = g} :=
  (eq_of_le_of_card_ge closure_t0Gen_le_T0 (by
    rw [card_T0, enumerates_closure_t0Gen.card, Array.length_toList, t0_parts.2.1])).symm

theorem enumerates_T0 : Enumerates T0 t0Enum.tabs.toList := by
  rw [T0_eq]
  exact enumerates_closure_t0Gen

theorem tabRep_v0Tab (j : ℕ) : TabRep (v0Tab j) (v0Gen j) := by
  unfold v0Tab v0Gen
  split_ifs with h1 h2 h3
  · exact tabRep_t0Tab h1
  · exact tabRep_w0
  · exact tabRep_r1
  · exact tabRep_tau0

theorem v0Gen_mem_V0 (j : ℕ) : v0Gen j ∈ V0 := by
  unfold v0Gen
  split_ifs with h1 h2 h3
  · exact T0_le_V0 (t0Gen_mem_T0 h1)
  · exact w0_mem_V0
  · exact r1_mem_V0
  · exact tau0_mem_V0

theorem v0_parts : enumOK 1782 v0Tabs v0Enum = true ∧ v0Enum.tabs.size = 512 ∧
    ∀ k < 512, comp 1782 v0Enum.tabs[k]! v0Enum.tabs[k]! ≠ idTab 1782 ∨
      v0Enum.tabs[k]! = idTab 1782 ∨ fixedCount v0Enum.tabs[k]! = 42 ∨
      found (indexOf t0Enum.tabs) t0Enum.tabs v0Enum.tabs[k]! = true := by
  have h := c1V0_check
  unfold v0Check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, beq_iff_eq.mp h2, fun k hk => ?_⟩
  have := allBelow_eq_true.mp h3 k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at this
  rcases this with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem enumerates_closure_v0Gen :
    Enumerates (closure {g | ∃ j < 7, v0Gen j = g}) v0Enum.tabs.toList := by
  have hsize : v0Tabs.size = 7 := Array.size_ofFn
  have hget : ∀ {j : ℕ}, j < 7 → v0Tabs[j]! = v0Tab j := fun hj => getElem!_ofFn' _ hj
  refine enumerates_closure (fun a ha => ?_) (fun j hj => ?_) v0_parts.1
  · obtain ⟨j, hj, rfl⟩ := ha
    exact ⟨j, by rw [hsize]; exact hj, by rw [hget hj]; exact tabRep_v0Tab j⟩
  · rw [hsize] at hj
    exact ⟨_, ⟨j, hj, rfl⟩, by rw [hget hj]; exact tabRep_v0Tab j⟩

theorem closure_v0Gen_le_V0 : closure {g | ∃ j < 7, v0Gen j = g} ≤ V0 := by
  rw [closure_le]
  rintro _ ⟨j, -, rfl⟩
  exact v0Gen_mem_V0 j

theorem V0_eq_closure_v0Gen :
    V0 = closure {g | ∃ j < 7, v0Gen j = g} :=
  (eq_of_le_of_card_ge closure_v0Gen_le_V0 (by
    rw [card_V0, enumerates_closure_v0Gen.card, Array.length_toList, v0_parts.2.1])).symm

theorem enumerates_V0 : Enumerates V0 v0Enum.tabs.toList := by
  rw [V0_eq_closure_v0Gen]
  exact enumerates_closure_v0Gen

theorem mem_T0_of_fix {u : Equiv.Perm (Fin 1782)} (hu : u ∈ V0)
    (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hfix : (Finset.univ.filter fun x : Fin 1782 => u x = x).card ≠ 42) : u ∈ T0 := by
  obtain ⟨k, hk, hrep⟩ := enumerates_V0.exists_pos hu
  rw [v0_parts.2.1] at hk
  rcases v0_parts.2.2 k hk with h | h | h | h
  · exact absurd ((hrep.comp hrep).tab_eq (hu2 ▸ TabRep.idTab)) h
  · exact absurd (hrep.perm_eq (h ▸ TabRep.idTab)) hu1
  · rw [fixedCount_eq hrep.2] at h
    exact absurd h hfix
  · obtain ⟨g, hg, hg'⟩ := enumerates_T0.sound _ (mem_of_found h)
    rwa [hrep.perm_eq hg']

theorem lambdaElt_zero : (LocalR.lambdaElt 0 : Equiv.Perm (Fin 1782)) = suzInv 1 := rfl

theorem rep_t0ConjGen {k : ℕ} (hk : k < (#[tTab, zT] : Array Tab).size) :
    Rep 1782 (#[tTab, zT] : Array Tab)[k]! (if k = 0 then suzInv 1 else zJ0) := by
  have hk' : k < 2 := hk
  interval_cases k
  · rw [getElem!_pair_zero]
    exact rep_tTab
  · rw [getElem!_pair_one]
    exact tabRep_zJ0.2

theorem tabRep_t0ConjTab {i : ℕ} (hi : i < 4) : TabRep (t0ConjTab i) (t0Conj i) :=
  tabRep_wordTab (fun k hk => rep_t0ConjGen hk) _ (by interval_cases i <;> decide)

theorem t0Conj_mem_suzM (i : ℕ) : t0Conj i ∈ suzM :=
  wordProd_mem (fun k => by
    split_ifs
    · exact invE_le_suzM suzInv_mem_invE
    · exact zJ0_mem_suzM) _

theorem t0Conj_conj {i : ℕ} (hi : i < 4) : t0Conj i * suzInv 1 * (t0Conj i)⁻¹ = t0Gen i := by
  have h := t0_parts.2.2.2.1 i hi
  rw [t0Tabs_get hi] at h
  rw [((tabRep_comp' (tabRep_t0ConjTab hi).2 rep_tTab).eq_iff
    ((tabRep_t0Tab hi).comp (tabRep_t0ConjTab hi))).mp h, mul_inv_cancel_right]

theorem suzInv_one_facts : suzInv 1 * suzInv 1 = 1 ∧
    suzInv 1 ≠ 1 ∧ (Finset.univ.filter fun x : Fin 1782 => suzInv 1 x = x).card = 54 := by
  have hr := LocalR.tabRep_lambda (i := 0) (by norm_num)
  obtain ⟨h1, h2, -⟩ := LocalR.reps_facts.1 0 (by norm_num)
  have hfix := LocalR.card_fixed_lambda (i := 0) (by norm_num)
  exact ⟨(hr.comp hr).perm_eq (h1 ▸ TabRep.idTab), fun h => h2 (hr.tab_eq (by rw [lambdaElt_zero, h]; exact TabRep.idTab)),
    hfix⟩

theorem T0_eq_closure_twoA :
    T0 = closure {u | u ∈ V0 ∧ ∃ c ∈ suzM, c * suzInv 1 * c⁻¹ = u} := by
  refine le_antisymm ?_ ((closure_le _).mpr ?_)
  · rw [T0_eq, closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact subset_closure ⟨T0_le_V0 (t0Gen_mem_T0 hi), t0Conj i, t0Conj_mem_suzM i, t0Conj_conj hi⟩
  · rintro u ⟨hu, c, -, rfl⟩
    obtain ⟨h1, h2, h3⟩ := suzInv_one_facts
    refine mem_T0_of_fix hu ?_ ?_ ?_
    · rw [show c * suzInv 1 * c⁻¹ * (c * suzInv 1 * c⁻¹) = c * (suzInv 1 * suzInv 1) * c⁻¹ by
        group, h1, mul_one, mul_inv_cancel]
    · intro h
      apply h2
      calc suzInv 1 = c⁻¹ * (c * suzInv 1 * c⁻¹) * c := by group
        _ = 1 := by rw [h, mul_one, inv_mul_cancel]
    · rw [conj_fixed_card, h3]
      norm_num

end T0

end CFSG.Sporadic.SuzRecog.C1Model
