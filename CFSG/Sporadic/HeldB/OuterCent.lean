module

public import CFSG.Sporadic.HeldB.OuterCentQuot
public import CFSG.Sporadic.HeldB.OuterClass

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native Pointwise
open scoped commutatorElement

theorem injective_of_card_range {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (h : Nat.card f.range = Nat.card G) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, h] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (one_mul _).symm)

theorem commutator_le_of_relIndex_two {M : Type*} [Group M] {C D : Subgroup M}
    (h : D.relIndex C = 2) : ⁅C, C⁆ ≤ D := by
  have hidx : (D.subgroupOf C).index = 2 := h
  rw [Subgroup.commutator_le]
  intro g hg k hk
  have hinv : ∀ a : C, (a⁻¹ ∈ D.subgroupOf C ↔ a ∈ D.subgroupOf C) := fun a =>
    Subgroup.inv_mem_iff _
  let a : C := ⟨g, hg⟩
  let b : C := ⟨k, hk⟩
  have hab : ⁅a, b⁆ ∈ D.subgroupOf C := by
    rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx, hinv, hinv]
    tauto
  exact Subgroup.mem_subgroupOf.1 hab

theorem card_heOuterC_ge :
    15120 ≤ Nat.card heOuterC := by
  rw [← card_heQC, ← heResF_range]
  exact Nat.card_le_card_of_surjective _ heResF.rangeRestrict_surjective

theorem heOuterC_eq :
    heOuterC = heP ⊓ Subgroup.centralizer {heAutU} := by
  apply Subgroup.eq_of_le_of_card_ge heOuterC_le_centralizer
  rw [card_heP_centralizer_heAutU]
  exact card_heOuterC_ge

theorem card_heOuterC :
    Nat.card heOuterC = 15120 := by
  rw [heOuterC_eq, card_heP_centralizer_heAutU]

theorem heResF_injective :
    Function.Injective heResF :=
  injective_of_card_range heResF (by rw [heResF_range, card_heQC, card_heOuterC])

theorem heOuterD_eq_closure : heOuterD =
    Subgroup.closure {heOuterDGen 0, heOuterDGen 1, heOuterDGen 2} := rfl

theorem heResF_image_D :
    heResF '' {c : heOuterC | (c : Equiv.Perm (Fin 8330)) ∈
      ({heOuterDGen 0, heOuterDGen 1, heOuterDGen 2} : Set _)} =
      {heTauP 0, heTauP 1, heTauP 2} := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
    rcases hc with hc | hc | hc
    · left
      rw [← heResF_d (j := 0) (by norm_num)]
      exact congrArg heResF (Subtype.ext hc)
    · right; left
      rw [← heResF_d (j := 1) (by norm_num)]
      exact congrArg heResF (Subtype.ext hc)
    · right; right
      rw [← heResF_d (j := 2) (by norm_num)]
      exact congrArg heResF (Subtype.ext hc)
  · intro hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨_, Or.inl rfl, heResF_d (by norm_num)⟩
    · exact ⟨_, Or.inr (Or.inl rfl), heResF_d (by norm_num)⟩
    · exact ⟨_, Or.inr (Or.inr (Set.mem_singleton _)), heResF_d (by norm_num)⟩

theorem card_heOuterD :
    Nat.card heOuterD = 7560 := by
  rw [card_eq_card_closure_image heOuterD_le_C heResF heResF_injective heOuterD_eq_closure
    heResF_image_D, ← heQD_eq, card_heQD]

theorem heOuterDGen_mem_D (j : ℕ) (hj : j < 3) : heOuterDGen j ∈ heOuterD := by
  apply Subgroup.subset_closure
  interval_cases j <;> simp

@[expose] def heOuterE : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure {⁅heOuterDGen 0, heOuterDGen 2⁆, ⁅heOuterDGen 1, heOuterDGen 2⁆}

theorem heOuterE_le_commutator : heOuterE ≤ ⁅heOuterD, heOuterD⁆ := by
  rw [heOuterE, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨Subgroup.commutator_mem_commutator (heOuterDGen_mem_D 0 (by norm_num))
      (heOuterDGen_mem_D 2 (by norm_num)),
    Subgroup.commutator_mem_commutator (heOuterDGen_mem_D 1 (by norm_num))
      (heOuterDGen_mem_D 2 (by norm_num))⟩

theorem heOuterE_le_C : heOuterE ≤ heOuterC :=
  heOuterE_le_commutator.trans ((Subgroup.commutator_le_self _).trans heOuterD_le_C)

theorem heResF_comm
    {i j : ℕ} (hi : i < 3) (hj : j < 3) (h : ⁅heOuterDGen i, heOuterDGen j⁆ ∈
    heOuterC) : heResF ⟨⁅heOuterDGen i, heOuterDGen j⁆, h⟩ = ⁅heTauP i, heTauP j⁆ := by
  have e : (⟨⁅heOuterDGen i, heOuterDGen j⁆, h⟩ : heOuterC) =
      ⁅(⟨heOuterDGen i, heOuterDGen_mem_C i⟩ : heOuterC), ⟨heOuterDGen j, heOuterDGen_mem_C j⟩⁆ :=
    Subtype.ext rfl
  rw [e, map_commutatorElement, heResF_d hi, heResF_d hj]

theorem heResF_image_E :
    heResF '' {c : heOuterC | (c : Equiv.Perm (Fin 8330)) ∈
      ({⁅heOuterDGen 0, heOuterDGen 2⁆, ⁅heOuterDGen 1, heOuterDGen 2⁆} : Set _)} =
      {⁅heTauP 0, heTauP 2⁆, ⁅heTauP 1, heTauP 2⁆} := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
    rcases hc with hc | hc
    · left
      have e : c = ⟨_, hc ▸ c.2⟩ := Subtype.ext hc
      rw [e, heResF_comm (by norm_num) (by norm_num)]
    · right
      have e : c = ⟨_, hc ▸ c.2⟩ := Subtype.ext hc
      rw [e, heResF_comm (by norm_num) (by norm_num)]
  · intro hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have h0 : ⁅heOuterDGen 0, heOuterDGen 2⁆ ∈ heOuterC :=
      heOuterE_le_C (Subgroup.subset_closure (Set.mem_insert _ _))
    have h1 : ⁅heOuterDGen 1, heOuterDGen 2⁆ ∈ heOuterC :=
      heOuterE_le_C (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    rcases hg with rfl | rfl
    · exact ⟨⟨_, h0⟩, Or.inl rfl, heResF_comm (by norm_num) (by norm_num) h0⟩
    · exact ⟨⟨_, h1⟩, Or.inr rfl, heResF_comm (by norm_num) (by norm_num) h1⟩

theorem card_heOuterE :
    Nat.card heOuterE = 7560 := by
  rw [card_eq_card_closure_image heOuterE_le_C heResF heResF_injective rfl heResF_image_E,
    ← heQE_eq, card_heQE]

theorem heOuterD_perfect :
    ⁅heOuterD, heOuterD⁆ = heOuterD := by
  apply le_antisymm (Subgroup.commutator_le_self _)
  have h := Subgroup.eq_of_le_of_card_ge (heOuterE_le_commutator.trans
    (Subgroup.commutator_le_self _)) (by rw [card_heOuterD, card_heOuterE])
  exact (le_of_eq h.symm).trans heOuterE_le_commutator

theorem heOuterD_relIndex :
    heOuterD.relIndex heOuterC = 2 := by
  have h := Subgroup.relIndex_mul_index (H := heOuterD.subgroupOf heOuterC) le_rfl
  have hc : Nat.card (heOuterD.subgroupOf heOuterC) = 7560 := by
    rw [← card_heOuterD]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe heOuterD_le_C).toEquiv
  have hi := Subgroup.card_mul_index (heOuterD.subgroupOf heOuterC)
  rw [hc, card_heOuterC] at hi
  rw [Subgroup.relIndex]
  omega

theorem heOuterD_eq_commutator :
    heOuterD = ⁅heOuterC, heOuterC⁆ := by
  apply le_antisymm
  · rw [← heOuterD_perfect]
    exact Subgroup.commutator_mono heOuterD_le_C heOuterD_le_C
  · exact commutator_le_of_relIndex_two heOuterD_relIndex

theorem heResF_map_D :
    (heOuterD.subgroupOf heOuterC).map heResF = heDq := by
  rw [subgroupOf_eq_closure heOuterD_le_C heOuterD_eq_closure, MonoidHom.map_closure,
    heResF_image_D, ← heQD_eq]

@[expose] def heOuterDEquiv :
    heOuterD ≃* heDq :=
  (Subgroup.subgroupOfEquivOfLe heOuterD_le_C).symm.trans
    (((heOuterD.subgroupOf heOuterC).equivMapOfInjective heResF heResF_injective).trans
      (MulEquiv.subgroupCongr heResF_map_D))

theorem card_center_heOuterD :
    Nat.card (Subgroup.center heOuterD) = 3 := by
  rw [← card_center_heDq]
  exact Nat.card_congr (Subgroup.centerCongr heOuterDEquiv).toEquiv

@[expose] def heOuterQuotEquiv :
    heOuterD ⧸ Subgroup.center heOuterD ≃* heQY.originalSubgroup :=
  (QuotientGroup.congr _ _ heOuterDEquiv (Subgroup.map_center_eq heOuterDEquiv)).trans
    heDqQuotEquiv

theorem card_heOuterD_quot :
    Nat.card (heOuterD ⧸ Subgroup.center heOuterD) = 2520 := by
  rw [Nat.card_congr heOuterQuotEquiv.toEquiv, card_heQY]

@[expose] def heOuterClassSizes : Fin 9 → ℕ := ![1, 70, 105, 210, 280, 360, 360, 504, 630]

@[expose] def heYOrder : Fin 9 → Fin 9 := ![8, 6, 5, 1, 7, 2, 3, 4, 0]

theorem heYOrder_bijective : Function.Bijective heYOrder := by decide

theorem heYSizes_length : heYSizes.length = 9 := rfl

theorem heYOrder_sizes (i : Fin 9) :
    heYSizes[(heYOrder i : ℕ)]'(by rw [heYSizes_length]; exact (heYOrder i).2) =
      heOuterClassSizes i := by
  revert i
  decide

theorem heOuterQuot_classes :
    ∃ e : Fin 9 ≃ ConjClasses (heOuterD ⧸ Subgroup.center heOuterD),
    ∀ i, (e i).carrier.ncard = heOuterClassSizes i := by
  obtain ⟨eY, heY⟩ := heY_classes
  obtain ⟨eT, heT⟩ := conjClasses_equiv_of_mulEquiv heOuterQuotEquiv.symm
  refine ⟨(((Equiv.ofBijective heYOrder heYOrder_bijective).trans
    (finCongr heYSizes_length.symm)).trans eY).trans eT, fun i => ?_⟩
  simp only [Equiv.trans_apply, Equiv.ofBijective_apply, finCongr_apply]
  rw [heT, heY, ← heYOrder_sizes]
  rfl

theorem heOuterClass_divisors : ∀ I : Finset (Fin 8),
    (1 + ∑ i ∈ I, heOuterClassSizes i.succ) ∣ 2520 →
      1 + ∑ i ∈ I, heOuterClassSizes i.succ = 1 ∨ 1 + ∑ i ∈ I, heOuterClassSizes i.succ = 2520 := by
  decide +kernel

@[expose] def heResSym :
    heOuterC →* Equiv.Perm {x : Fin 8330 | heAutU x = x} :=
  (Equiv.permCongrHom (Set.equivOfEq heFixPt_range)).toMonoidHom.comp
    ((MulAction.toPermHom (MulAction.stabilizer (Equiv.Perm (Fin 8330))
      (Set.range (listPt 8330 heFixU (m := 98)))) (Set.range (listPt 8330 heFixU (m := 98)))).comp
        (Subgroup.inclusion heOuterC_le_stabilizer))

theorem heResSym_apply
    (c : heOuterC) (x : {x : Fin 8330 | heAutU x = x}) :
    ((heResSym c x : {x : Fin 8330 | heAutU x = x}) : Fin 8330) =
      (c : Equiv.Perm (Fin 8330)) x := rfl

theorem heResSym_injective :
    Function.Injective heResSym := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  apply heResF_injective
  rw [map_one, heResF, restrictHom_eq_one_iff]
  intro k
  have hk : listPt 8330 heFixU k ∈ {x : Fin 8330 | heAutU x = x} := by
    rw [← heFixPt_range]
    exact ⟨k, rfl⟩
  have := congrArg (fun σ : Equiv.Perm {x : Fin 8330 | heAutU x = x} =>
    ((σ ⟨_, hk⟩ : {x : Fin 8330 | heAutU x = x}) : Fin 8330))
    (MonoidHom.mem_ker.1 hc)
  simpa [heResSym_apply] using this

theorem ncard_heFixSet :
    {x : Fin 8330 | heAutU x = x}.ncard = 98 := by
  rw [← heFixPt_range, Set.ncard_range_of_injective heFixPt_injective, Nat.card_fin]

theorem ctbh_outer_centralizer_small_action_arithmetic :
    heOuterC = heP ⊓ Subgroup.centralizer {heAutU} ∧ Nat.card heOuterC = 15120 ∧
    heOuterD = ⁅heOuterC, heOuterC⁆ ∧ ⁅heOuterD, heOuterD⁆ = heOuterD ∧
    Nat.card heOuterD = 7560 ∧ Nat.card (Subgroup.center heOuterD) = 3 ∧
    {i : Fin 8330 | heAutU i = i}.ncard = 98 ∧
    (∃ ρ : heOuterC →* Equiv.Perm {i : Fin 8330 | heAutU i = i}, Function.Injective ρ ∧
      ∀ c x, ((ρ c x : {i : Fin 8330 | heAutU i = i}) : Fin 8330) =
        (c : Equiv.Perm (Fin 8330)) x) ∧
    Nat.card (heOuterD ⧸ Subgroup.center heOuterD) = 2520 ∧
    (∃ e : Fin 9 ≃ ConjClasses (heOuterD ⧸ Subgroup.center heOuterD),
      ∀ i, (e i).carrier.ncard = heOuterClassSizes i) ∧
    ∀ I : Finset (Fin 8), (1 + ∑ i ∈ I, heOuterClassSizes i.succ) ∣ 2520 →
      1 + ∑ i ∈ I, heOuterClassSizes i.succ = 1 ∨
        1 + ∑ i ∈ I, heOuterClassSizes i.succ = 2520 :=
  ⟨heOuterC_eq, card_heOuterC, heOuterD_eq_commutator, heOuterD_perfect, card_heOuterD,
    card_center_heOuterD, ncard_heFixSet, ⟨heResSym, heResSym_injective, heResSym_apply⟩,
    card_heOuterD_quot, heOuterQuot_classes, heOuterClass_divisors⟩

end CFSG.Sporadic.HeldB
