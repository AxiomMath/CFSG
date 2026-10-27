module

public import CFSG.Sporadic.SuzRecog.LevelTwoComplex

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwo

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData CFSG.Sporadic.SuzRecog.ElimCert
  CFSG.ComponentClassification.AS81.SuzB0

attribute [local irreducible] nbr vtab vtabs aPts wPts trips aIdx vIdx

local notation "ρ" => Model.rho1

theorem groupOK_parts :
    eqA 1782 (compA 1782 w0Arr (rhoConj w0Arr)) (rhoConj (rhoConj w0Arr)) = true ∧
    (∀ y < 2997, adjB nbr 0 y = true →
      (y < 2835 → y ≠ 0 ∧ ∃ j < 128, eqA 1782 aPts[y]! qElts[j]! = true) ∧
      (¬ y < 2835 → commA t1Arr wPts[y - 2835]! = true)) ∧
    (∀ j < 128, aIdx.getD (fp qElts[j]!) 2835 < 2835 → aIdx.getD (fp qElts[j]!) 2835 ≠ 0 →
      eqA 1782 aPts[aIdx.getD (fp qElts[j]!) 2835]! qElts[j]! = true →
      adjB nbr 0 (aIdx.getD (fp qElts[j]!) 2835) = true) ∧
    (∀ j < 162, commA t1Arr wPts[j]! = true → adjB nbr 0 (2835 + j) = true) ∧
    commA aPts[p1]! t1Arr = true ∧ bIdx < 2835 ∧ eqA 1782 aPts[bIdx]! bArr = true ∧
    adjB nbr bIdx cellReps[0]! = true := by
  have h := group_check
  simp only [groupOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, fun y hy hadj => ?_, fun j hj e1 e2 e3 => ?_, fun j hj hc => ?_, h5, h6, h7, h8⟩
  · have := allLt_spec h2 hy
    simp only [hadj, Bool.not_true, Bool.false_or] at this
    constructor
    · intro hlt
      simp only [hlt, ↓reduceIte, Bool.and_eq_true, bne_iff_ne, List.any_eq_true,
        List.mem_range] at this
      exact this
    · intro hlt
      simpa [hlt] using this
  · have := allLt_spec h3 hj
    have e2' : (aIdx.getD (fp qElts[j]!) 2835 != 0) = true := bne_iff_ne.2 e2
    simp only [e1, e2', e3, decide_true, Bool.and_self, Bool.not_true, Bool.false_or] at this
    exact this
  · have := allLt_spec h4 hj
    simpa [hc] using this

theorem rep_t1 :
    Rep 1782 t1Arr (suzInv 1) :=
  rep_tTab

theorem aP_zero :
    aP 0 = suzInv 1 :=
  eq_of_eqA (rep_aP (by norm_num)) rep_t1 aOK_parts.2.1

theorem rep_w0 : Rep 1782 w0Arr Model.w0 :=
  (rep_permC basicOK_parts.2.2.2.2.2.2.2.1).1

theorem wP_zero : wP 0 = Model.w0 :=
  eq_of_eqA (rep_wP (by norm_num)) rep_w0 vOK_parts.2.1

theorem conj_eq_one {g a : Equiv.Perm (Fin 1782)} (h : g * a * g⁻¹ = 1) : a = 1 := by
  simpa [mul_assoc] using congrArg (fun x => g⁻¹ * x * g) h

theorem coe_closure_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    ((Subgroup.closure {a, b} : Subgroup G) : Set G) = {1, a, b, a * b} := by
  have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h2 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
  have h3 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
  have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h2, hb]
  have h6 : b * a = a * b := hab.symm
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  let K : Subgroup G :=
    { carrier := {1, a, b, a * b}
      one_mem' := Set.mem_insert _ _
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp only [one_mul, mul_one, ha, hb, h1, h2, h3, h4, h5, h6, true_or, or_true]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;>
          simp only [inv_one, ia, ib, mul_inv_rev, h6, true_or, or_true] }
  have hK : Subgroup.closure {a, b} = K := by
    refine Subgroup.closure_eq_of_le K ?_ ?_
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · intro x hx
      change x ∈ ({1, a, b, a * b} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  rw [hK]
  rfl

theorem w0_mul_self : Model.w0 * Model.w0 = 1 := by
  have h := rep_inv_of_isInvA rep_w0 basicOK_parts.2.2.2.2.2.2.2.1
  have e : Model.w0 = Model.w0⁻¹ := rep_w0.unique h
  calc Model.w0 * Model.w0 = Model.w0 * Model.w0⁻¹ := by rw [← e]
    _ = 1 := mul_inv_cancel _

theorem w0_commute :
    Model.w0 * (ρ * Model.w0 * ρ⁻¹) = ρ * Model.w0 * ρ⁻¹ * Model.w0 :=
  eq_of_eqA (rep_compA rep_w0 (rep_rhoConj rep_w0)) (rep_compA (rep_rhoConj rep_w0) rep_w0)
    basicOK_parts.2.2.2.2.2.2.2.2.2.1

theorem w0_ne : Model.w0 ≠ ρ * Model.w0 * ρ⁻¹ := by
  intro h
  have := (eqA_iff rep_w0 (rep_rhoConj rep_w0)).2 h
  rw [basicOK_parts.2.2.2.2.2.2.2.2.2.2] at this
  exact Bool.noConfusion this

theorem w0_mul :
    Model.w0 * (ρ * Model.w0 * ρ⁻¹) = ρ * (ρ * Model.w0 * ρ⁻¹) * ρ⁻¹ :=
  eq_of_eqA (rep_compA rep_w0 (rep_rhoConj rep_w0)) (rep_rhoConj (rep_rhoConj rep_w0))
    groupOK_parts.1

theorem coe_R0 :
    (Model.R0 : Set (Equiv.Perm (Fin 1782))) = insert 1 (rhoTrip Model.w0) := by
  have hb : ρ * Model.w0 * ρ⁻¹ * (ρ * Model.w0 * ρ⁻¹) = 1 := by
    calc ρ * Model.w0 * ρ⁻¹ * (ρ * Model.w0 * ρ⁻¹) = ρ * (Model.w0 * Model.w0) * ρ⁻¹ := by
          group
      _ = 1 := by rw [w0_mul_self, mul_one, mul_inv_cancel]
  rw [Model.R0, coe_closure_pair w0_mul_self hb w0_commute, w0_mul]
  rfl

theorem one_notMem_rhoTrip_w0 :
    (1 : Equiv.Perm (Fin 1782)) ∉ rhoTrip Model.w0 := by
  have h0 : Model.w0 ≠ 1 := fun h => w0_ne (by rw [h, mul_one, mul_inv_cancel])
  simp only [rhoTrip, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun h => h0 h.symm, fun h => h0 (conj_eq_one h.symm), fun h => h0 ?_⟩
  exact conj_eq_one (conj_eq_one h.symm)

theorem insert_eq_insert_iff {α : Type*} {a : α} {s t : Set α} (hs : a ∉ s) (ht : a ∉ t) :
    insert a s = insert a t ↔ s = t := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext x
  constructor
  · intro hx
    rcases (h ▸ Set.mem_insert_of_mem a hx : x ∈ insert a t) with rfl | hx'
    · exact absurd hx hs
    · exact hx'
  · intro hx
    rcases (h.symm ▸ Set.mem_insert_of_mem a hx : x ∈ insert a s) with rfl | hx'
    · exact absurd hx ht
    · exact hx'

theorem mem_normalizer_R0_iff (g : Equiv.Perm (Fin 1782)) :
    g ∈ Subgroup.normalizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) ↔
      conjSet g (rhoTrip Model.w0) = rhoTrip Model.w0 := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq, coe_R0]
  have hconj : (⇑(MulAut.conj g) : Equiv.Perm (Fin 1782) → Equiv.Perm (Fin 1782)) =
      fun a => g * a * g⁻¹ := funext fun a => MulAut.conj_apply g a
  rw [hconj, Set.image_insert_eq, show g * 1 * g⁻¹ = 1 by group]
  refine insert_eq_insert_iff ?_ one_notMem_rhoTrip_w0
  rintro ⟨x, hx, e⟩
  exact one_notMem_rhoTrip_w0 (conj_eq_one e ▸ hx)

theorem vset_pV :
    vset (pV : ℕ) = {suzInv 1} := by
  rw [← aP_zero]
  simp [vset, pV]

theorem vset_qV : vset (qV : ℕ) = rhoTrip Model.w0 := by
  rw [← wP_zero]
  simp [vset, qV]

theorem mem_Xp_iff_commute
    (g : xGroup) :
    g ∈ Xp ↔ Commute (g : Equiv.Perm (Fin 1782)) (suzInv 1) := by
  rw [mem_Xp, smul_eq_iff, vset_pV]
  simp only [conjSet, Set.image_singleton, Set.singleton_eq_singleton_iff]
  rw [eq_comm, mul_inv_eq_iff_eq_mul]
  exact Iff.rfl

theorem mem_Xp_iff
    (g : xGroup) : g ∈ Xp ↔ (g : Equiv.Perm (Fin 1782)) ∈ invE 1 := by
  rw [mem_Xp_iff_commute, invE_eq_centM (by norm_num : 1 < 4), centM, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h, xGroup_le_suzM g.2⟩, fun h => h.1⟩

theorem mem_Xq_iff_conjSet (g : xGroup) :
    g ∈ Xq ↔ conjSet g.1 (rhoTrip Model.w0) = rhoTrip Model.w0 := by
  rw [mem_Xq, smul_eq_iff, vset_qV, eq_comm]

theorem mem_Xq_iff
    (g : xGroup) :
    g ∈ Xq ↔ (g : Equiv.Perm (Fin 1782)) ∈ Model.NR0 := by
  rw [mem_Xq_iff_conjSet, ← mem_normalizer_R0_iff]
  unfold Model.NR0
  rw [Subgroup.mem_inf]
  exact ⟨fun h => ⟨xGroup_le_suzM g.2, h⟩, fun h => h.2⟩

theorem mem_Xp_inf_Xq_iff
    (g : xGroup) : g ∈ Xp ⊓ Xq ↔ (g : Equiv.Perm (Fin 1782)) ∈ Model.B0 := by
  rw [Subgroup.mem_inf, mem_Xp_iff, mem_Xq_iff_conjSet, ← mem_normalizer_R0_iff]
  unfold Model.B0
  rw [Subgroup.mem_inf]

theorem exists_mem_Xp
    {y : Equiv.Perm (Fin 1782)}
    (hy : y ∈ Model.Crho1) (h1 : y ∈ invE 1) : ∃ x ∈ Xp, (x : Equiv.Perm (Fin 1782)) = y := by
  have hX : y ∈ xGroup := xGroup_eq_Crho1 ▸ hy
  exact ⟨⟨y, hX⟩, (mem_Xp_iff _).2 h1, rfl⟩

theorem exists_mem_Xq
    {y : Equiv.Perm (Fin 1782)} (hy : y ∈ Model.Crho1)
    (h1 : y ∈ Model.NR0) : ∃ x ∈ Xq, (x : Equiv.Perm (Fin 1782)) = y := by
  have hX : y ∈ xGroup := xGroup_eq_Crho1 ▸ hy
  exact ⟨⟨y, hX⟩, (mem_Xq_iff _).2 h1, rfl⟩

theorem p1_lt_2835 : p1 < 2835 := by
  have h := locOK_parts.2.2.2.2.2.1
  unfold sendsB at h
  simp only [show (0 : ℕ) < 2835 by norm_num, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h.1

theorem vset_p1V : vset (p1V : ℕ) = {aP p1} := by
  simp [vset, p1V, p1_lt_2835]

theorem commute_aP_p1 :
    Commute (aP p1) (suzInv 1) :=
  eq_of_eqA (rep_compA (rep_aP p1_lt_2835) rep_t1) (rep_compA rep_t1 (rep_aP p1_lt_2835))
    groupOK_parts.2.2.2.2.1

theorem bIdx_lt : bIdx < 2835 :=
  groupOK_parts.2.2.2.2.2.1

@[expose] def bV : Fin 2997 :=
  ⟨bIdx, by have := bIdx_lt; omega⟩

theorem aP_bIdx :
    aP bIdx = suzInv 1 * aP p1 :=
  eq_of_eqA (rep_aP bIdx_lt) (rep_compA rep_t1 (rep_aP p1_lt_2835)) groupOK_parts.2.2.2.2.2.2.1

theorem vset_bV :
    vset (bV : ℕ) = {suzInv 1 * aP p1} := by
  rw [← aP_bIdx]
  simp [vset, bV, bIdx_lt]

theorem smul_bV_of_mem_Xe
    {g : xGroup} (hg : g ∈ Xe) : g • bV = bV := by
  rw [smul_eq_iff, vset_bV]
  simp only [conjSet, Set.image_singleton, Set.singleton_eq_singleton_iff]
  have hp := smul_spec g pV
  have hp1 := smul_spec g p1V
  rcases (mem_Xe g).1 hg with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · rw [e0, vset_pV, conjSet, Set.image_singleton, Set.singleton_eq_singleton_iff] at hp
    rw [e1, vset_p1V, conjSet, Set.image_singleton, Set.singleton_eq_singleton_iff] at hp1
    calc suzInv 1 * aP p1 = (g.1 * suzInv 1 * g.1⁻¹) * (g.1 * aP p1 * g.1⁻¹) := by
          rw [← hp, ← hp1]
      _ = g.1 * (suzInv 1 * aP p1) * g.1⁻¹ := by group
  · rw [e0, vset_p1V, vset_pV, conjSet, Set.image_singleton,
      Set.singleton_eq_singleton_iff] at hp
    rw [e1, vset_pV, vset_p1V, conjSet, Set.image_singleton,
      Set.singleton_eq_singleton_iff] at hp1
    calc suzInv 1 * aP p1 = aP p1 * suzInv 1 := commute_aP_p1.eq.symm
      _ = (g.1 * suzInv 1 * g.1⁻¹) * (g.1 * aP p1 * g.1⁻¹) := by rw [← hp, ← hp1]
      _ = g.1 * (suzInv 1 * aP p1) * g.1⁻¹ := by group

theorem mem_centM_of_mem_Xe
    {g : xGroup} (hg : g ∈ Xe) :
    (g : Equiv.Perm (Fin 1782)) ∈ centM (suzInv 1 * aP p1) := by
  have h := (smul_eq_iff g bV bV).1 (smul_bV_of_mem_Xe hg)
  rw [vset_bV] at h
  simp only [conjSet, Set.image_singleton, Set.singleton_eq_singleton_iff] at h
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, xGroup_le_suzM g.2⟩
  rw [eq_comm, mul_inv_eq_iff_eq_mul] at h
  exact h

end CFSG.Sporadic.SuzRecog.LevelTwo
