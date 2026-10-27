module

public import CFSG.Sporadic.HeldB.OuterCentRestrict
public import CFSG.Sporadic.HeldB.ClassCount

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native Pointwise

abbrev heDq : Subgroup (Equiv.Perm (Fin 98)) := heQD.originalSubgroup

theorem heDq_eq : heDq = Subgroup.closure {heTauP 0, heTauP 1, heTauP 2} := heQD_eq

@[expose] def heZP : Equiv.Perm (Fin 98) := permOrId 98 heZ

theorem rep_heZ :
    Rep 98 heZ heZP := (permChk_spec heOuterCent_small.2.2.2.2.2.2.2.2.1).1

theorem heZP_mem : heZP ∈ heDq :=
  (heQD.sift_eq_true_iff_mem_original heQD_valid heZP).1 heOuterCent_small.2.2.2.2.2.2.2.2.2.1

theorem heZP_comm
    {j : ℕ} (hj : j < 3) : heZP * heTauP j = heTauP j * heZP :=
  eq_of_eqA (rep_compA rep_heZ (rep_heTau hj)) (rep_compA (rep_heTau hj) rep_heZ)
    (heOuterCent_small.2.2.2.2.2.2.2.2.2.2.1 j hj)

theorem heZP_ne_one : heZP ≠ 1 := by
  intro h
  have h' := (eqA_iff rep_heZ rep_idA).2 h
  rw [heOuterCent_small.2.2.2.2.2.2.2.2.2.2.2.1] at h'
  exact absurd h' (by decide)

theorem heZP_pow_three : heZP ^ 3 = 1 := by
  have h := eq_of_eqA (rep_compA rep_heZ (rep_compA rep_heZ rep_heZ)) rep_idA
    heOuterCent_small.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [pow_succ, pow_two, mul_assoc]
  exact h

theorem orderOf_heZP : orderOf heZP = 3 :=
  orderOf_eq_prime heZP_pow_three heZP_ne_one

theorem heDq_le_centralizer :
    heDq ≤ Subgroup.centralizer {heZP} := by
  rw [heDq_eq, Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  refine ⟨?_, ?_, ?_⟩ <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  · exact (heZP_comm (j := 0) (by norm_num)).symm
  · exact (heZP_comm (j := 1) (by norm_num)).symm
  · exact (heZP_comm (j := 2) (by norm_num)).symm

@[expose] def heZq : heDq := ⟨heZP, heZP_mem⟩

theorem heZq_mem_center : heZq ∈ Subgroup.center heDq := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have := Subgroup.mem_centralizer_singleton_iff.1 (heDq_le_centralizer g.2)
  simpa [heZq] using this

theorem mem_center_heDq_iff (x : heDq) :
    x ∈ Subgroup.center heDq ↔ ∀ g ∈ heTauGens, (x : Equiv.Perm (Fin 98)) * g = g * x := by
  constructor
  · intro hx g hg
    have hgD : g ∈ heDq := by
      rw [heDq_eq]
      apply Subgroup.subset_closure
      simp only [heTauGens, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h <;> rw [h] <;> simp [heTauP]
    have := Subgroup.mem_center_iff.1 hx ⟨g, hgD⟩
    exact (congrArg Subtype.val this).symm
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : heDq ≤ Subgroup.centralizer {(x : Equiv.Perm (Fin 98))} := by
      have hcl : Subgroup.closure {heTauP 0, heTauP 1, heTauP 2} ≤
          Subgroup.centralizer {(x : Equiv.Perm (Fin 98))} := ?_
      · exact heDq_eq.le.trans hcl
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have ht' : t ∈ heTauGens := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        rcases ht with h | h | h <;> rw [h] <;> simp [heTauGens, heTauP]
      exact (hx t ht').symm
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle g.2))

theorem card_center_heDq : Nat.card (Subgroup.center heDq) = 3 := by
  have hn : (98 : ℕ) < 2 ^ 32 := by norm_num
  have hcount := heOuterCent_small.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hreps : ∀ g ∈ heTauGens, CFSG.Sporadic.Th.Rep 98 (toTable g) g := fun g _ =>
    rep_toTable hn g
  have h1 : (allTables heQD).countP (commAll 98 (heTauGens.map toTable)) =
      (enumeration heQD).reverse.countP
        fun y => decide (∀ g ∈ heTauGens, y * g = g * y) :=
    countP_eq_of_forall₂ (forall₂_allTables hn heQD) fun T y hT _ => by
      rw [decide_eq_true_iff]
      simp only [commAll, List.all_map, List.all_eq_true, Function.comp_apply]
      exact ⟨fun h g hg => (commT_iff hT (hreps g hg)).1 (h g hg),
        fun h g hg => (commT_iff hT (hreps g hg)).2 (h g hg)⟩
  rw [h1, List.countP_reverse, ← card_subtype_eq_countP heDq (enumeration heQD)
    (enumeration_nodup heQD heQD_valid) (mem_enumeration_iff heQD heQD_valid)] at hcount
  rw [← hcount]
  exact Nat.card_congr ⟨fun x => ⟨x.1, (mem_center_heDq_iff x.1).1 x.2⟩,
    fun x => ⟨x.1, (mem_center_heDq_iff x.1).2 x.2⟩, fun x => rfl, fun x => rfl⟩

theorem orderOf_heZq : orderOf heZq = 3 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_heZP

theorem center_heDq_eq :
    Subgroup.center heDq = Subgroup.zpowers heZq := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · exact (Subgroup.zpowers_le).2 heZq_mem_center
  · rw [card_center_heDq, Nat.card_zpowers, orderOf_heZq]

theorem heFixZ_list : fixListOK 98 35 heZ heFixZ = true :=
  heOuterCent_small.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem heFixZ_injective :
    Function.Injective (listPt 98 heFixZ (m := 35)) :=
  listPt_injective heFixZ_list

@[expose] def heUpsP (j : ℕ) : Equiv.Perm (Fin 35) := permOrId 35 (heUpsilon.getD j #[])

theorem rep_heUps
    {j : ℕ} (hj : j < 3) : Rep 35 (heUpsilon.getD j #[]) (heUpsP j) :=
  (permChk_spec (heOuterCent_small.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj).1).1

theorem heTau_agreeZ {j : ℕ} (hj : j < 3) (k : Fin 35) :
    heTauP j (listPt 98 heFixZ k) = listPt 98 heFixZ (heUpsP j k) :=
  agreeOK_spec heFixZ_list (rep_heTau hj) (rep_heUps hj)
    (heOuterCent_small.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj).2 k

theorem heDq_le_stabilizer :
    heDq ≤ MulAction.stabilizer (Equiv.Perm (Fin 98)) (Set.range (listPt 98 heFixZ (m := 35))) := by
  rw [heDq_eq, Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  exact ⟨mem_stabilizer_of_agree (heTau_agreeZ (j := 0) (by norm_num)),
    mem_stabilizer_of_agree (heTau_agreeZ (j := 1) (by norm_num)),
    mem_stabilizer_of_agree (heTau_agreeZ (j := 2) (by norm_num))⟩

@[expose] def heResZ : heDq →* Equiv.Perm (Fin 35) :=
  restrictHom heFixZ_injective heDq heDq_le_stabilizer

theorem heQY_valid :
    ValidSchreier heQY := heOuterCent_small.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem card_heQY : Nat.card heQY.originalSubgroup = 2520 := by
  rw [← heQY.orderCertificate_eq_card heQY_valid,
    heOuterCent_small.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]

theorem heUpsGens_eq : heUpsGens = [heUpsP 0, heUpsP 1, heUpsP 2] := by
  rw [heUpsGens, heUpsilon]
  rfl

theorem heQY_eq : heQY.originalSubgroup = Subgroup.closure {heUpsP 0, heUpsP 1, heUpsP 2} := by
  rw [heQY, certificate_originalSubgroup, heUpsGens_eq]
  congr 1
  ext g
  simp

theorem heTau_mem_heDq {j : ℕ} (hj : j < 3) : heTauP j ∈ heDq := by
  rw [heDq_eq]
  apply Subgroup.subset_closure
  interval_cases j <;> simp

theorem heResZ_tau
    {j : ℕ} (hj : j < 3) : heResZ ⟨heTauP j, heTau_mem_heDq hj⟩ = heUpsP j :=
  restrictHom_eq_of_agree heFixZ_injective heDq_le_stabilizer _ (heTau_agreeZ hj)

theorem heResZ_range : heResZ.range = heQY.originalSubgroup := by
  rw [heResZ, restrictHom_range heFixZ_injective heDq_le_stabilizer heDq_eq, heQY_eq, ← heResZ,
    ← heResZ_tau (j := 0) (by norm_num), ← heResZ_tau (j := 1) (by norm_num),
    ← heResZ_tau (j := 2) (by norm_num)]
  congr 1
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh ⊢
    rcases hh with hh | hh | hh
    · exact Or.inl (congrArg heResZ (Subtype.ext hh))
    · exact Or.inr (Or.inl (congrArg heResZ (Subtype.ext hh)))
    · exact Or.inr (Or.inr (congrArg heResZ (Subtype.ext hh)))
  · intro hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Set.mem_singleton _)), rfl⟩

theorem heZq_mem_ker : heZq ∈ heResZ.ker := by
  rw [MonoidHom.mem_ker, heResZ, restrictHom_eq_one_iff]
  intro k
  apply Fin.ext
  change (heZP (listPt 98 heFixZ k) : ℕ) = _
  rw [← rep_heZ, listPt_val heFixZ_list]
  exact ((fixListOK_parts heFixZ_list).2.1 k k.2).2

theorem heResZ_ker : heResZ.ker = Subgroup.center heDq := by
  rw [center_heDq_eq]
  symm
  apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 heZq_mem_ker)
  have h1 := Subgroup.card_mul_index heResZ.ker
  rw [Subgroup.index_ker, heResZ_range, card_heQY] at h1
  have h2 : Nat.card heDq = 7560 := card_heQD
  rw [h2] at h1
  rw [Nat.card_zpowers, orderOf_heZq]
  omega

@[expose] def heDqQuotEquiv :
    heDq ⧸ Subgroup.center heDq ≃* heQY.originalSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq heResZ_ker.symm).trans
    ((QuotientGroup.quotientKerEquivRange heResZ).trans (MulEquiv.subgroupCongr heResZ_range))

@[expose] def heYSizes : List ℕ := [630, 210, 360, 360, 504, 105, 70, 280, 1]

@[expose] def heYCents : List ℕ := [4, 12, 7, 7, 5, 24, 36, 9, 2520]

theorem heYSizes_mul_cents : ∀ i (_ : i < heYSizes.length) (hj : i < heYCents.length),
    heYSizes[i] * heYCents[i] = 2520 := by
  decide

theorem heYGens_eq : heYGens = #[toTable (heUpsP 0), toTable (heUpsP 1), toTable (heUpsP 2)] := by
  rw [heYGens, heUpsGens_eq]
  rfl

theorem heYGensInv_eq :
    heYGensInv = #[toTable (heUpsP 0)⁻¹, toTable (heUpsP 1)⁻¹, toTable (heUpsP 2)⁻¹] := by
  rw [heYGensInv, heUpsGens_eq]
  rfl

theorem heYGens_rep : ∀ l < heYGens.size,
    CFSG.Sporadic.Th.Rep 35 heYGens[l]! ([heUpsP 0, heUpsP 1, heUpsP 2].getD l 1) ∧
      CFSG.Sporadic.Th.Rep 35 heYGensInv[l]! ([heUpsP 0, heUpsP 1, heUpsP 2].getD l 1)⁻¹ ∧
      [heUpsP 0, heUpsP 1, heUpsP 2].getD l 1 ∈ heQY.originalSubgroup := by
  have hn : (35 : ℕ) < 2 ^ 32 := by norm_num
  intro l hl
  rw [heYGens_eq] at hl
  have hl' : l < 3 := hl
  rw [heYGens_eq, heYGensInv_eq, heQY_eq]
  interval_cases l
  · rw [arr3_get0, arr3_get0, list3_getD0]
    exact ⟨rep_toTable hn _, rep_toTable hn _, Subgroup.subset_closure (by simp)⟩
  · rw [arr3_get1, arr3_get1, list3_getD1]
    exact ⟨rep_toTable hn _, rep_toTable hn _, Subgroup.subset_closure (by simp)⟩
  · rw [arr3_get2, arr3_get2, list3_getD2]
    exact ⟨rep_toTable hn _, rep_toTable hn _, Subgroup.subset_closure (by simp)⟩

theorem heY_classes :
    ∃ e : Fin heYSizes.length ≃ ConjClasses heQY.originalSubgroup,
    ∀ i, (e i).carrier.ncard = heYSizes[i] := by
  obtain ⟨hok, hsz, hct⟩ := heOuterCent_classes
  exact conjClasses_equiv_of_classOK (by norm_num) heQY heQY_valid heYGens_rep 3000 hok
    (sizes := heYSizes) hsz (cents := heYCents) hct fun i hi hj => by
      rw [card_heQY]
      exact heYSizes_mul_cents i hi hj

end CFSG.Sporadic.HeldB
