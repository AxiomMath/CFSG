module

public import CFSG.Sporadic.Schreier.RuSEnum
public import CFSG.Sporadic.Schreier.RuWitness
public import CFSG.Sporadic.Schreier.RuTreeElt
public import CFSG.Sporadic.Schreier.RuWitReps

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

abbrev ruInvS : Set (Equiv.Perm (Fin 4060)) := {t | t ∈ ruS ∧ orderOf t = 2}

abbrev ruInvS92 :
    Set (Equiv.Perm (Fin 4060)) :=
  {t | t ∈ ruS ∧ orderOf t = 2 ∧ (fixSet t).ncard = 92}

abbrev ruInvS0 :
    Set (Equiv.Perm (Fin 4060)) :=
  {t | t ∈ ruS ∧ orderOf t = 2 ∧ (fixSet t).ncard = 0}

abbrev ruXClass (i : ℕ) : Set (Equiv.Perm (Fin 4060)) := conjSet ruS (ruFusX i)

theorem ncard_ruInvS :
    ruInvS.ncard = 687 := by
  rw [ncard_setOf_mem_and ruS (fun t => orderOf t = 2),
    ruS_card_of_count (p := ruIsInvolA) fun t g ht => ruIsInvolA_iff ht]
  exact ruInv_check.2.2.2.1

theorem ncard_ruInvS92 :
    ruInvS92.ncard = 495 := by
  rw [ncard_setOf_mem_and ruS (fun t => orderOf t = 2 ∧ (fixSet t).ncard = 92),
    ruS_card_of_count (P := fun g => orderOf g = 2 ∧ (fixSet g).ncard = 92)
      (p := fun t => ruIsInvolA t && ruFixCount t == 92) fun t g ht => by
      rw [Bool.and_eq_true, ruIsInvolA_iff ht, beq_iff_eq, ruFixCount_eq ht]]
  exact ruInv_check.2.2.2.2.1

theorem ncard_ruInvS0 :
    ruInvS0.ncard = 192 := by
  rw [ncard_setOf_mem_and ruS (fun t => orderOf t = 2 ∧ (fixSet t).ncard = 0),
    ruS_card_of_count (P := fun g => orderOf g = 2 ∧ (fixSet g).ncard = 0)
      (p := fun t => ruIsInvolA t && ruFixCount t == 0) fun t g ht => by
      rw [Bool.and_eq_true, ruIsInvolA_iff ht, beq_iff_eq, ruFixCount_eq ht]]
  exact ruInv_check.2.2.2.2.2.1

theorem mem_ruZP_of_ruInvS92 :
    ∀ g ∈ ruS, orderOf g = 2 ∧ (fixSet g).ncard = 92 → g ∈ ruZP :=
  ruS_forall (p := fun t => !(ruIsInvolA t && ruFixCount t == 92) || ruZWit t)
    (fun t g ht h hg => by
      have hA : ruIsInvolA t = true := (ruIsInvolA_iff ht).2 hg.1
      have hB : (ruFixCount t == 92) = true := by
        rw [beq_iff_eq, ruFixCount_eq ht]
        exact hg.2
      rw [hA, hB] at h
      exact mem_ruZP_of_ruZWit ht (by simpa using h))
    ruInv_check.2.2.2.2.2.2.1

theorem card_inf_centralizer_eq {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    Nat.card (H ⊓ Subgroup.centralizer {x} : Subgroup G) =
      Nat.card {g : H // (g : G) * x = x * g} :=
  Nat.card_congr
    { toFun := fun g => ⟨⟨g, (Subgroup.mem_inf.1 g.2).1⟩,
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2⟩
      invFun := fun g => ⟨g.1, Subgroup.mem_inf.2 ⟨g.1.2,
        Subgroup.mem_centralizer_singleton_iff.2 g.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_ruS_centralizer_X
    {i : ℕ} (hi : i ∈ [1, 2, 3]) :
    Nat.card (ruS ⊓ Subgroup.centralizer {ruFusX i} : Subgroup _) = 256 := by
  rw [card_inf_centralizer_eq, ruS_card_of_count
    (p := fun s => eqA 4060 (compA 4060 s (ruFusXA i)) (compA 4060 (ruFusXA i) s))
    fun t g ht => eqA_iff (rep_compA ht (rep_ruFusX hi)) (rep_compA (rep_ruFusX hi) ht)]
  exact ruInv_check.2.2.2.2.2.2.2.1 i hi

theorem ncard_ruXClass
    {i : ℕ} (hi : i ∈ [1, 2, 3]) : (ruXClass i).ncard = 64 := by
  show (conjSet ruS (ruFusX i)).ncard = 64
  have h := ncard_conjSet_mul_card ruS (ruFusX i)
  rw [card_ruS_centralizer_X hi, card_ruS] at h
  omega

theorem ruFusX_not_mem
    {i j : ℕ} (hi : i ∈ [1, 2, 3]) (hj : j ∈ [1, 2, 3]) (hij : i < j) :
    ruFusX j ∉ ruXClass i := by
  rintro ⟨s, hs, hsx⟩
  have key := ruS_forall
    (p := fun s => !eqA 4060 (compA 4060 s (ruFusXA i)) (compA 4060 (ruFusXA j) s))
    (P := fun g => g * ruFusX i ≠ ruFusX j * g)
    (fun t g ht h heq => by
      rw [(eqA_iff (rep_compA ht (rep_ruFusX hi)) (rep_compA (rep_ruFusX hj) ht)).2 heq] at h
      exact Bool.false_ne_true h)
    (ruInv_check.2.2.2.2.2.2.2.2.1 i hi j hj hij)
  exact key s hs (by rw [← hsx]; group)

theorem ruXClass_disjoint
    {i j : ℕ} (hi : i ∈ [1, 2, 3]) (hj : j ∈ [1, 2, 3]) (hij : i ≠ j) :
    Disjoint (ruXClass i) (ruXClass j) := by
  rcases conjSet_disjoint_or_eq ruS (ruFusX i) (ruFusX j) with h | h
  · exact h
  · exfalso
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · refine ruFusX_not_mem hi hj hlt ?_
      show ruFusX j ∈ conjSet ruS (ruFusX i)
      rw [h]
      exact self_mem_conjSet ruS (ruFusX j)
    · refine ruFusX_not_mem hj hi hlt ?_
      show ruFusX i ∈ conjSet ruS (ruFusX j)
      rw [← h]
      exact self_mem_conjSet ruS (ruFusX i)

theorem ruFusH_conj
    {i : ℕ} (hi : i ∈ [1, 2, 3]) : ruFusH i * ruA0 * (ruFusH i)⁻¹ = ruFusX i := by
  have := eq_of_eqA (rep_compA (rep_ruFusH hi) rep_ruA0) (rep_compA (rep_ruFusX hi) (rep_ruFusH hi))
    (ruInv_check.2.2.2.2.2.2.2.2.2.1 i hi)
  rw [this, mul_inv_cancel_right]

theorem ruA0_sq : ruA0 * ruA0 = 1 :=
  eq_of_eqA (rep_compA rep_ruA0 rep_ruA0) rep_idA ruInv_check.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ruA0_ne_one :
    ruA0 ≠ 1 := fun h => by
  have := (eqA_iff rep_ruA0 rep_idA).2 h
  rw [ruInv_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem orderOf_ruA0 :
    orderOf ruA0 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact ruA0_sq) ruA0_ne_one

theorem fixSet_ruA0 :
    (fixSet ruA0).ncard = 0 := by
  rw [← ruFixCount_eq rep_ruA0]
  exact ruInv_check.2.2.2.2.2.2.2.2.2.2.1

theorem orderOf_conj' {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem ruXClass_sub
    {i : ℕ} (hi : i ∈ [1, 2, 3]) : ruXClass i ⊆ ruInvS0 := by
  rintro t ⟨s, hs, rfl⟩
  rw [← ruFusH_conj hi]
  refine ⟨ruS.mul_mem (ruS.mul_mem hs (ruFusH_conj hi ▸ ruFusX_mem i)) (ruS.inv_mem hs), ?_, ?_⟩
  · rw [orderOf_conj', orderOf_conj', orderOf_ruA0]
  · rw [ncard_fixSet_conj, ncard_fixSet_conj, fixSet_ruA0]

theorem ruXClass_union :
    ruXClass 1 ∪ ruXClass 2 ∪ ruXClass 3 = ruInvS0 := by
  have h1 : (1 : ℕ) ∈ [1, 2, 3] := by decide
  have h2 : (2 : ℕ) ∈ [1, 2, 3] := by decide
  have h3 : (3 : ℕ) ∈ [1, 2, 3] := by decide
  refine Set.eq_of_subset_of_ncard_le (Set.union_subset (Set.union_subset (ruXClass_sub h1)
    (ruXClass_sub h2)) (ruXClass_sub h3)) ?_ (Set.toFinite _)
  rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨ruXClass_disjoint h1 h3 (by decide),
      ruXClass_disjoint h2 h3 (by decide)⟩) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq (ruXClass_disjoint h1 h2 (by decide)) (Set.toFinite _) (Set.toFinite _),
    ncard_ruXClass h1, ncard_ruXClass h2, ncard_ruXClass h3, ncard_ruInvS0]

theorem ruInvS_eq_union :
    ruInvS = ruInvS92 ∪ ruInvS0 := by
  symm
  refine Set.eq_of_subset_of_ncard_le (Set.union_subset (fun t ht => ⟨ht.1, ht.2.1⟩)
    (fun t ht => ⟨ht.1, ht.2.1⟩)) ?_ (Set.toFinite _)
  rw [Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _), ncard_ruInvS, ncard_ruInvS92,
    ncard_ruInvS0]
  rw [Set.disjoint_left]
  intro t h1 h2
  have := h1.2.2.symm.trans h2.2.2
  norm_num at this

theorem ruInvSZ_eq :
    {t | t ∈ ruS ∧ orderOf t = 2 ∧ t ∈ ruZP} = ruInvS92 := by
  ext t
  constructor
  · rintro ⟨hS, h2, hz⟩
    obtain ⟨g, -, rfl⟩ := hz
    exact ⟨hS, h2, by rw [ncard_fixSet_conj]; exact ruFixSet_ncard⟩
  · rintro ⟨hS, h2, h92⟩
    exact ⟨hS, h2, mem_ruZP_of_ruInvS92 t hS ⟨h2, h92⟩⟩

theorem ncard_ruInvSZ :
    {t | t ∈ ruS ∧ orderOf t = 2 ∧ t ∈ ruZP}.ncard = 495 := by
  rw [ruInvSZ_eq, ncard_ruInvS92]

theorem ruInvS_eq :
    ruInvS =
    {t | t ∈ ruS ∧ orderOf t = 2 ∧ t ∈ ruZP} ∪ ruXClass 1 ∪ ruXClass 2 ∪ ruXClass 3 := by
  rw [ruInvS_eq_union, ruInvSZ_eq, ← ruXClass_union]
  simp only [Set.union_assoc]

theorem ruXClass_disjoint_ZP
    {i : ℕ} (hi : i ∈ [1, 2, 3]) : Disjoint (ruXClass i) ruZP := by
  rw [Set.disjoint_left]
  intro t ht hz
  have h0 := (ruXClass_sub hi ht).2.2
  obtain ⟨g, -, rfl⟩ := hz
  rw [ncard_fixSet_conj, ruFixSet_ncard] at h0
  norm_num at h0

end CFSG.Sporadic.RuSchreier
