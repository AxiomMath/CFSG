module

public import CFSG.Sporadic.SuzRecog.RootTwist
public import CFSG.Sporadic.SuzRecog.ModelGroups

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.RootTwist

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.Model CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.RootTwistCheck
  CFSG.Sporadic.SuzRecog.RootTwistData CFSG.Sporadic.SuzRecog.LevelTwoData

@[expose] def kGenA : Equiv.Perm (Fin 1782) := permC 1782 kGenAArr

@[expose] def kGenB : Equiv.Perm (Fin 1782) := permC 1782 kGenBArr

@[expose] def kGen (s : ℕ) : Equiv.Perm (Fin 1782) :=
  if s = 0 then kGenA else if s = 1 then kGenB else if s = 2 then kGenA⁻¹ else kGenB⁻¹

@[expose] def kElt (i : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 kEls[i]!

@[expose] def cElt (i : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 cTr[i]!

@[expose] def cGen (s : ℕ) : Equiv.Perm (Fin 1782) :=
  if s = 0 then ModelGroups.c1a else ModelGroups.c1b

theorem kGen_parts :
    ModelGroupsCheck.permOK kGenAArr = true ∧ ModelGroupsCheck.permOK kGenBArr = true ∧
      inM kGenAArr = true ∧ inM kGenBArr = true ∧
      ModelGroupsCheck.commA kGenAArr ModelGroupsCheck.t1A = true ∧
      ModelGroupsCheck.commA kGenBArr ModelGroupsCheck.t1A = true ∧
      ModelGroupsCheck.commA kGenAArr rhoArr = true ∧
      ModelGroupsCheck.commA kGenBArr rhoArr = true := by
  have h := kGen_check
  simp only [kGenOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem rep_kGenA :
    Rep 1782 kGenAArr kGenA := (rep_permC kGen_parts.1).1

theorem rep_kGenB :
    Rep 1782 kGenBArr kGenB := (rep_permC kGen_parts.2.1).1

theorem rep_kGen
    {s : ℕ} (hs : s < 4) : Rep 1782 kGens[s]! (kGen s) := by
  interval_cases s
  · rw [show kGens[0]! = kGenAArr by simp [kGens]]
    exact rep_kGenA
  · rw [show kGens[1]! = kGenBArr by simp [kGens]]
    exact rep_kGenB
  · rw [show kGens[2]! = invCand 1782 kGenAArr by simp [kGens]]
    exact ModelGroups.rep_invCand rep_kGenA
  · rw [show kGens[3]! = invCand 1782 kGenBArr by simp [kGens]]
    exact ModelGroups.rep_invCand rep_kGenB

theorem kGenA_mem_K :
    kGenA ∈ invE 1 ⊓ Model.Crho1 :=
  mem_inf.2 ⟨ModelGroups.mem_invE_one_iff.2 ⟨(ModelGroups.commA_iff rep_kGenA rep_t1).1
      kGen_parts.2.2.2.2.1,
    (inM_iff rep_kGenA).1 kGen_parts.2.2.1⟩,
    ModelGroups.mem_Crho1_iff.2 ⟨(ModelGroups.commA_iff rep_kGenA rep_rho1).1
      kGen_parts.2.2.2.2.2.2.1, (inM_iff rep_kGenA).1 kGen_parts.2.2.1⟩⟩

theorem kGenB_mem_K :
    kGenB ∈ invE 1 ⊓ Model.Crho1 :=
  mem_inf.2 ⟨ModelGroups.mem_invE_one_iff.2 ⟨(ModelGroups.commA_iff rep_kGenB rep_t1).1
      kGen_parts.2.2.2.2.2.1, (inM_iff rep_kGenB).1 kGen_parts.2.2.2.1⟩,
    ModelGroups.mem_Crho1_iff.2 ⟨(ModelGroups.commA_iff rep_kGenB rep_rho1).1
      kGen_parts.2.2.2.2.2.2.2, (inM_iff rep_kGenB).1 kGen_parts.2.2.2.1⟩⟩

theorem kEnum_facts :
    kEls.size = 3456 ∧ eqA 1782 kEls[0]! (idA 1782) = true ∧
    ∀ i < 3456, ModelGroupsCheck.permOK kEls[i]! = true ∧
      kTab.getD (LevelTwo.fp kEls[i]!) 3456 = i ∧
      (i = 0 ∨ (kPar[i]! < i ∧ kLab[i]! < 2 ∧
        eqA 1782 kEls[i]! (compA 1782 kGens[kLab[i]!]! kEls[kPar[i]!]!) = true)) ∧
      ∀ s < 4, kStep i s = true := by
  have h := kEnum_check
  simp only [kEnumOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun i hi => ?_⟩
  have := allLt_spec h3 hi
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨⟨h4, h5⟩, h6⟩, h7⟩ := this
  exact ⟨h4, h5, h6.imp id (fun h => ⟨h.1.1, h.1.2, h.2⟩), fun s hs => allLt_spec h7 hs⟩

theorem rep_kElt
    {i : ℕ} (hi : i < 3456) : Rep 1782 kEls[i]! (kElt i) :=
  (rep_permC (kEnum_facts.2.2 i hi).1).1

theorem kElt_zero :
    kElt 0 = 1 := eq_of_eqA (rep_kElt (by norm_num)) rep_idA kEnum_facts.2.1

theorem kGen_mem_closure {s : ℕ} (hs : s < 2) : kGen s ∈ closure {kGenA, kGenB} := by
  interval_cases s
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem kElt_mem_closure :
    ∀ i < 3456, kElt i ∈ closure {kGenA, kGenB} := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases (kEnum_facts.2.2 i hi).2.2.1 with rfl | ⟨hp, hl, he⟩
    · rw [kElt_zero]
      exact one_mem _
    · have e : kElt i = kGen kLab[i]! * kElt kPar[i]! :=
        eq_of_eqA (rep_kElt hi) (rep_compA (rep_kGen (by omega)) (rep_kElt (by omega))) he
      rw [e]
      exact mul_mem (kGen_mem_closure hl) (ih _ hp (by omega))

theorem kStep_spec {i s : ℕ} (hi : i < 3456) (hs : s < 4) :
    ∃ j < 3456, kGen s * kElt i = kElt j := by
  have h := (kEnum_facts.2.2 i hi).2.2.2 s hs
  simp only [kStep, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨_, h.1, eq_of_eqA (rep_compA (rep_kGen hs) (rep_kElt hi)) (rep_kElt h.1) h.2⟩

theorem exists_eq_kElt
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ closure {kGenA, kGenB}) :
    ∃ i < 3456, g = kElt i := by
  induction hg using closure_induction_left with
  | one => exact ⟨0, by norm_num, kElt_zero.symm⟩
  | mul_left x hx y _ ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    rcases hx with rfl | rfl
    · obtain ⟨j, hj, e⟩ := kStep_spec (s := 0) hi (by norm_num)
      exact ⟨j, hj, e⟩
    · obtain ⟨j, hj, e⟩ := kStep_spec (s := 1) hi (by norm_num)
      exact ⟨j, hj, e⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    rcases hx with rfl | rfl
    · obtain ⟨j, hj, e⟩ := kStep_spec (s := 2) hi (by norm_num)
      exact ⟨j, hj, e⟩
    · obtain ⟨j, hj, e⟩ := kStep_spec (s := 3) hi (by norm_num)
      exact ⟨j, hj, e⟩

theorem kElt_injective
    {i j : ℕ} (hi : i < 3456) (hj : j < 3456) (h : kElt i = kElt j) : i = j := by
  have hf : LevelTwo.fp kEls[i]! = LevelTwo.fp kEls[j]! :=
    LevelTwo.fp_eq_of_rep (rep_kElt hi) (h ▸ rep_kElt hj)
  rw [← (kEnum_facts.2.2 i hi).2.1, ← (kEnum_facts.2.2 j hj).2.1, hf]

theorem le_card_closure_k :
    3456 ≤ Nat.card (closure {kGenA, kGenB}) := by
  have := Nat.card_le_card_of_injective
    (fun i : Fin 3456 => (⟨kElt i, kElt_mem_closure i i.2⟩ : closure {kGenA, kGenB}))
    (fun i j h => Fin.ext (kElt_injective i.2 j.2 (congrArg Subtype.val h)))
  simpa using this

theorem class_facts :
    ModelGroupsCheck.permOK ModelGroupsCheck.aA = true ∧
    ModelGroupsCheck.permOK ModelGroupsCheck.bA = true ∧ inM ModelGroupsCheck.aA = true ∧
    inM ModelGroupsCheck.bA = true ∧
    ModelGroupsCheck.commA ModelGroupsCheck.aA ModelGroupsCheck.t1A = true ∧
    ModelGroupsCheck.commA ModelGroupsCheck.bA ModelGroupsCheck.t1A = true ∧
    cTr.size = 960 ∧ eqA 1782 cTr[0]! (idA 1782) = true ∧
    ∀ i < 960, ModelGroupsCheck.permOK cTr[i]! = true ∧
      cTab.getD (LevelTwo.fp (ModelGroupsCheck.conjA cTr[i]! rhoArr)) 960 = i ∧
      (i = 0 ∨ (cPar[i]! < i ∧ cLab[i]! < 2 ∧
        eqA 1782 cTr[i]! (compA 1782 cGens[cLab[i]!]! cTr[cPar[i]!]!) = true)) := by
  have h := class_check
  simp only [classOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun i hi => ?_⟩
  have := allLt_spec h9 hi
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨h10, h11⟩, h12⟩ := this
  exact ⟨h10, h11, h12.imp id (fun h => ⟨h.1.1, h.1.2, h.2⟩)⟩

theorem rep_cGen
    {s : ℕ} (hs : s < 2) : Rep 1782 cGens[s]! (cGen s) := by
  interval_cases s
  · rw [show cGens[0]! = ModelGroupsCheck.aA by simp [cGens]]
    exact (rep_permC class_facts.1).1
  · rw [show cGens[1]! = ModelGroupsCheck.bA by simp [cGens]]
    exact (rep_permC class_facts.2.1).1

theorem rep_c1a' :
    Rep 1782 ModelGroupsCheck.aA ModelGroups.c1a := (rep_permC class_facts.1).1

theorem rep_c1b' :
    Rep 1782 ModelGroupsCheck.bA ModelGroups.c1b := (rep_permC class_facts.2.1).1

theorem cGen_mem_invE
    (s : ℕ) : cGen s ∈ invE 1 := by
  unfold cGen
  split_ifs
  · exact ModelGroups.mem_invE_one_iff.2 ⟨(ModelGroups.commA_iff rep_c1a' rep_t1).1
      class_facts.2.2.2.2.1,
      (inM_iff rep_c1a').1 class_facts.2.2.1⟩
  · exact ModelGroups.mem_invE_one_iff.2 ⟨(ModelGroups.commA_iff rep_c1b' rep_t1).1
      class_facts.2.2.2.2.2.1,
      (inM_iff rep_c1b').1 class_facts.2.2.2.1⟩

theorem rep_cElt
    {i : ℕ} (hi : i < 960) : Rep 1782 cTr[i]! (cElt i) :=
  (rep_permC (class_facts.2.2.2.2.2.2.2.2 i hi).1).1

theorem cElt_mem_invE :
    ∀ i < 960, cElt i ∈ invE 1 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases (class_facts.2.2.2.2.2.2.2.2 i hi).2.2 with rfl | ⟨hp, hl, he⟩
    · rw [show cElt 0 = 1 from eq_of_eqA (rep_cElt (by norm_num)) rep_idA
        class_facts.2.2.2.2.2.2.2.1]
      exact one_mem _
    · have e : cElt i = cGen cLab[i]! * cElt cPar[i]! :=
        eq_of_eqA (rep_cElt hi) (rep_compA (rep_cGen hl) (rep_cElt (by omega))) he
      rw [e]
      exact mul_mem (cGen_mem_invE _) (ih _ hp (by omega))

theorem cElt_conj_injective {i j : ℕ} (hi : i < 960) (hj : j < 960)
    (h : cElt i * rho1 * (cElt i)⁻¹ = cElt j * rho1 * (cElt j)⁻¹) : i = j := by
  have hf : LevelTwo.fp (ModelGroupsCheck.conjA cTr[i]! rhoArr) =
      LevelTwo.fp (ModelGroupsCheck.conjA cTr[j]! rhoArr) :=
    LevelTwo.fp_eq_of_rep (ModelGroups.rep_conjA (rep_cElt hi) rep_rho1)
      (h ▸ ModelGroups.rep_conjA (rep_cElt hj) rep_rho1)
  rw [← (class_facts.2.2.2.2.2.2.2.2 i hi).2.1, ← (class_facts.2.2.2.2.2.2.2.2 j hj).2.1, hf]

theorem card_K_le :
    Nat.card ↥(invE 1 ⊓ Model.Crho1) ≤ 3456 := by
  have h := ModelGroups.mul_card_le_of_inv_mul_mem (H := invE 1) (K := invE 1 ⊓ Model.Crho1)
    inf_le_left (fun i : Fin 960 => cElt i) (fun i => cElt_mem_invE i i.2) (fun i j hij => ?_)
  · rw [card_invE (by norm_num : 1 < 4)] at h
    have e : invInnerOrders.getD 1 0 = 3317760 := rfl
    omega
  · apply Fin.ext
    apply cElt_conj_injective i.2 j.2
    have hc := ModelGroups.conj_eq_of_mul_comm (ModelGroups.mem_Crho1_iff.1 (mem_inf.1 hij).2).1
    calc cElt i * rho1 * (cElt i)⁻¹ =
        cElt i * ((cElt i)⁻¹ * cElt j * rho1 * ((cElt i)⁻¹ * cElt j)⁻¹) * (cElt i)⁻¹ := by
          rw [hc]
      _ = cElt j * rho1 * (cElt j)⁻¹ := by group

theorem K_eq_closure :
    invE 1 ⊓ Model.Crho1 = closure {kGenA, kGenB} := by
  refine (eq_of_le_of_card_ge ((closure_le _).2 ?_) (card_K_le.trans le_card_closure_k)).symm
  rintro x (rfl | rfl)
  · exact kGenA_mem_K
  · exact kGenB_mem_K

theorem card_K :
    Nat.card ↥(invE 1 ⊓ Model.Crho1) = 3456 :=
  le_antisymm card_K_le (by rw [K_eq_closure]; exact le_card_closure_k)

theorem mem_zpowers_rho1_of_mem_centralizer
    {c : Equiv.Perm (Fin 1782)} (hc : c ∈ invE 1)
    (hcent : ∀ g ∈ invE 1 ⊓ Model.Crho1, c * g = g * c) (h3 : c ^ 3 = 1) : c ∈ zpowers rho1 := by
  have hρ : rho1 ∈ invE 1 ⊓ Model.Crho1 :=
    mem_inf.2 ⟨CW_le_invE rho1_mem_CW, ModelGroups.mem_Crho1_iff.2 ⟨rfl,
      (mem_inf.1 rho1_mem_CW).2⟩⟩
  have hcK : c ∈ invE 1 ⊓ Model.Crho1 :=
    mem_inf.2 ⟨hc, ModelGroups.mem_Crho1_iff.2 ⟨hcent _ hρ, (ModelGroups.mem_invE_one_iff.1 hc).2⟩⟩
  rw [K_eq_closure] at hcK
  obtain ⟨i, hi, rfl⟩ := exists_eq_kElt hcK
  have hA := (ModelGroups.commA_iff (rep_kElt hi) rep_kGenA).2 (hcent _ kGenA_mem_K)
  have hB := (ModelGroups.commA_iff (rep_kElt hi) rep_kGenB).2 (hcent _ kGenB_mem_K)
  have hC := (eqA_iff (rep_powA (rep_kElt hi) 3) rep_idA).2 h3
  have h := allLt_spec kCentre_check hi
  simp only [hA, hB, hC, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · rw [eq_of_eqA (rep_kElt hi) rep_idA h]
    exact one_mem _
  · rw [eq_of_eqA (rep_kElt hi) rep_rho1 h]
    exact mem_zpowers _
  · rw [eq_of_eqA (rep_kElt hi) (rep_compA rep_rho1 rep_rho1) h]
    exact mul_mem (mem_zpowers _) (mem_zpowers _)

end CFSG.Sporadic.SuzRecog.RootTwist
