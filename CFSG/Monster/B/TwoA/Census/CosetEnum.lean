module

public import CFSG.Monster.B.TwoA.Census.CosetEnumCheck

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice CFSG.Monster.Spin
  CFSG.Monster.Griess CFSG.Monster.B.Rep4371

theorem ne_one_of_mem_cosetR
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 7) {f : Gvis}
    (hf : f ∈ cosetR i) : f ≠ 1 := by
  rintro rfl
  rw [mem_cosetR_iff, map_one, eq_comm, ← MonoidHom.mem_ker, ker_piVis,
    Subgroup.mem_subgroupOf] at hf
  exact cosetRep_not_mem hi1 hi hf

theorem cosetInv_eq_orderOf
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 7) :
    cosetInv i = {f | f ∈ cosetR i ∧ orderOf f = 2} := by
  ext f
  show f ∈ cosetR i ∧ f * f = 1 ↔ f ∈ cosetR i ∧ orderOf f = 2
  constructor
  · rintro ⟨hf, h⟩
    exact ⟨hf, orderOf_eq_prime_iff.2 ⟨by rw [pow_two]; exact h, ne_one_of_mem_cosetR hi1 hi hf⟩⟩
  · rintro ⟨hf, h⟩
    exact ⟨hf, by rw [← pow_two]; exact (orderOf_eq_prime_iff.1 h).1⟩

theorem ncard_cosetInv_one :
    (cosetInv 1).ncard = 69632 := by
  rw [ncard_cosetInv (Or.inl rfl), countSq_one]

theorem ncard_cosetInv_two :
    (cosetInv 2).ncard = 8192 := by
  rw [ncard_cosetInv (Or.inr (Or.inl rfl)), countSq_two]

theorem ncard_cosetInv_six :
    (cosetInv 6).ncard = 0 := by
  rw [ncard_cosetInv (Or.inr (Or.inr rfl)), countSq_six]

theorem cosetInv_finite
    {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 6) : (cosetInv i).Finite := by
  rw [cosetInv_eq hi]
  exact ((Set.finite_lt_nat (2 ^ 25)).subset fun n hn => hn.1).image _

theorem cosetElt_mem_cosetInv
    {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 6) {n : ℕ} (hn : n < 2 ^ 25)
    (ht : Native.CosetEnum.sqTest (tT i) (tD i) (wP i) n = true) : cosetElt i n ∈ cosetInv i := by
  rw [cosetInv_eq hi]
  exact ⟨n, ⟨hn, ht⟩, rfl⟩

theorem sqTest_of_mem_cosetInv
    {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 6) {n : ℕ} (hn : n < 2 ^ 25)
    (h : cosetElt i n ∈ cosetInv i) : Native.CosetEnum.sqTest (tT i) (tD i) (wP i) n = true := by
  rw [cosetInv_eq hi] at h
  obtain ⟨m, ⟨hm, ht⟩, e⟩ := h
  rwa [← cosetElt_injective i hm hn e]

@[expose] def classRep
    (k : ℕ) : Gvis := cosetElt 1 (classEnc k)

theorem classCheck_spec {k : ℕ} (hk : k < 137) :
    natCertOK (Native.CosetEnum.act (imgs 1)) 24 (fun n => decide (n < 2 ^ 25)) (classEnc k)
        (classCert 1 (classEnc k)) = true ∧
      (classCert 1 (classEnc k)).pts.size = classSize k ∧
      (∀ j < (classCert 1 (classEnc k)).pts.size, classEnc k ≤ (classCert 1 (classEnc k)).pts[j]!) ∧
      Native.CosetEnum.sqTest (tT 1) (tD 1) (wP 1) (classEnc k) = true := by
  have h := classCheck_eq_true
  simp only [classCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h k hk
  exact ⟨h1, h2, h3, h4⟩

theorem classEnc_lt
    {k : ℕ} (hk : k < 137) : classEnc k < 2 ^ 25 := by
  have h := (classCheck_spec hk).1
  have := natCertOK_valid h (natCertOK_pos h)
  rw [natCertOK_root h] at this
  exact of_decide_eq_true this

theorem classRep_mem
    {k : ℕ} (hk : k < 137) : classRep k ∈ cosetInv 1 :=
  cosetElt_mem_cosetInv (Or.inl rfl) (classEnc_lt hk) (classCheck_spec hk).2.2.2

theorem qmatClass_classRep_subset
    {k : ℕ} (hk : k < 137) : qmatClass (classRep k) ⊆ cosetInv 1 :=
  fun g hg => ⟨(qmatClass_subset 1 (classRep_mem hk).1 g hg).1,
    (qmatClass_subset 1 (classRep_mem hk).1 g hg).2.2 (classRep_mem hk).2⟩

theorem ncard_qmatClass_classRep
    {k : ℕ} (hk : k < 137) :
    (qmatClass (classRep k)).ncard = classSize k := by
  rw [classRep, ncard_qmatClass_of_natCertOK 1 (classCheck_spec hk).1, (classCheck_spec hk).2.1]

theorem classEnc_le_of_mem
    {k : ℕ} (hk : k < 137) {n : ℕ} (hn : n < 2 ^ 25)
    (h : cosetElt 1 n ∈ qmatClass (classRep k)) : classEnc k ≤ n := by
  obtain ⟨j, hj, rfl⟩ := mem_pts_of_natCertOK 1 (classCheck_spec hk).1 hn h
  exact (classCheck_spec hk).2.2.1 j hj

theorem classEnc_strictMono {k k' : ℕ} (h : k < k') (hk' : k' < 137) :
    classEnc k < classEnc k' := by
  induction k' with
  | zero => omega
  | succ k' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · exact (ih h' (by omega)).trans (classEnc_succ k' (by omega))
    · exact classEnc_succ k (by omega)

theorem classEnc_injective {k k' : ℕ} (hk : k < 137) (hk' : k' < 137)
    (h : classEnc k = classEnc k') : k = k' := by
  rcases lt_trichotomy k k' with h' | h' | h'
  · exact absurd h (classEnc_strictMono h' hk').ne
  · exact h'
  · exact absurd h (classEnc_strictMono h' hk).ne'

theorem disjoint_qmatClass_classRep
    {k k' : ℕ} (hk : k < 137) (hk' : k' < 137) (hne : k ≠ k') :
    Disjoint (qmatClass (classRep k)) (qmatClass (classRep k')) := by
  rw [Set.disjoint_left]
  intro g hg hg'
  have e : qmatClass (classRep k) = qmatClass (classRep k') :=
    (qmatClass_eq_of_mem hg).symm.trans (qmatClass_eq_of_mem hg')
  have m1 : classRep k' ∈ qmatClass (classRep k) := by
    rw [e]
    exact mem_qmatClass_self _
  have m2 : classRep k ∈ qmatClass (classRep k') := by
    rw [← e]
    exact mem_qmatClass_self _
  have h1 := classEnc_le_of_mem hk (classEnc_lt hk') m1
  have h2 := classEnc_le_of_mem hk' (classEnc_lt hk) m2
  exact hne (classEnc_injective hk hk' (le_antisymm h1 h2))

@[irreducible] def invEnc : Finset ℕ :=
  (Finset.range (2 ^ 25)).filter fun n => Native.CosetEnum.sqTest (tT 1) (tD 1) (wP 1) n = true

@[irreducible] def classPts (k : ℕ) : Finset ℕ :=
  (Finset.range (classCert 1 (classEnc k)).pts.size).image fun j =>
    (classCert 1 (classEnc k)).pts[j]!

theorem card_invEnc : invEnc.card = 69632 := by
  rw [invEnc, ← countSq_eq, countSq_one]

theorem mem_classPts
    {k : ℕ} (hk : k < 137) {n : ℕ} (hn : n ∈ classPts k) :
    n < 2 ^ 25 ∧ cosetElt 1 n ∈ qmatClass (classRep k) := by
  rw [classPts] at hn
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hn
  rw [Finset.mem_range] at hj
  refine ⟨of_decide_eq_true (natCertOK_valid (classCheck_spec hk).1 hj), ?_⟩
  rw [classRep, qmatClass_eq_of_natCertOK 1 (classCheck_spec hk).1]
  exact ⟨j, hj, rfl⟩

theorem card_classPts
    {k : ℕ} (hk : k < 137) : (classPts k).card = classSize k := by
  rw [classPts, Finset.card_image_of_injOn, Finset.card_range, (classCheck_spec hk).2.1]
  intro j hj j' hj' e
  exact natCertOK_inj (classCheck_spec hk).1 (Finset.mem_range.1 hj) (Finset.mem_range.1 hj') e

theorem classPts_subset
    {k : ℕ} (hk : k < 137) : classPts k ⊆ invEnc := by
  intro n hn
  obtain ⟨hn', hmem⟩ := mem_classPts hk hn
  rw [invEnc, Finset.mem_filter, Finset.mem_range]
  exact ⟨hn', sqTest_of_mem_cosetInv (Or.inl rfl) hn' (qmatClass_classRep_subset hk hmem)⟩

theorem biUnion_classPts :
    (Finset.range 137).biUnion classPts = invEnc := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    obtain ⟨k, hk, hn⟩ := Finset.mem_biUnion.1 hn
    exact classPts_subset (Finset.mem_range.1 hk) hn
  · rw [card_invEnc, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl fun k hk => card_classPts (Finset.mem_range.1 hk), sum_classSize]
    · intro k hk k' hk' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro n hn hn'
      obtain ⟨hn1, h1⟩ := mem_classPts (Finset.mem_range.1 hk) hn
      obtain ⟨-, h2⟩ := mem_classPts (Finset.mem_range.1 hk') hn'
      exact Set.disjoint_left.1 (disjoint_qmatClass_classRep (Finset.mem_range.1 hk)
        (Finset.mem_range.1 hk') hne) h1 h2

theorem mem_qmatClass_of_mem_cosetInv_one
    {f : Gvis} (hf : f ∈ cosetInv 1) :
    ∃ k < 137, f ∈ qmatClass (classRep k) := by
  rw [cosetInv_eq (Or.inl rfl)] at hf
  obtain ⟨n, ⟨hn, ht⟩, rfl⟩ := hf
  have hmem : n ∈ invEnc := by
    rw [invEnc, Finset.mem_filter, Finset.mem_range]
    exact ⟨hn, ht⟩
  rw [← biUnion_classPts, Finset.mem_biUnion] at hmem
  obtain ⟨k, hk, hn'⟩ := hmem
  exact ⟨k, Finset.mem_range.1 hk, (mem_classPts (Finset.mem_range.1 hk) hn').2⟩

theorem ncard_classes :

    {C : Set Gvis | ∃ f ∈ cosetInv 1, C = qmatClass f}.ncard = 137 := by
  have e : {C : Set Gvis | ∃ f ∈ cosetInv 1, C = qmatClass f} =
      (fun k => qmatClass (classRep k)) '' Set.Iio 137 := by
    ext C
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨k, hk, hfk⟩ := mem_qmatClass_of_mem_cosetInv_one hf
      exact ⟨k, hk, (qmatClass_eq_of_mem hfk).symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨classRep k, classRep_mem hk, rfl⟩
  rw [e, Set.InjOn.ncard_image, Set.ncard_Iio_nat]
  intro k hk k' hk' h
  by_contra hne
  have h' : qmatClass (classRep k) = qmatClass (classRep k') := h
  have m : classRep k ∈ qmatClass (classRep k') := by
    rw [← h']
    exact mem_qmatClass_self _
  exact Set.disjoint_left.1 (disjoint_qmatClass_classRep hk hk' hne)
    (mem_qmatClass_self (classRep k)) m

theorem class2Check_spec :
    natCertOK (Native.CosetEnum.act (imgs 2)) 24 (fun n => decide (n < 2 ^ 25)) 734
        (classCert 2 734) = true ∧ (classCert 2 734).pts.size = 8192 ∧
      Native.CosetEnum.sqTest (tT 2) (tD 2) (wP 2) 734 = true := by
  have h := class2Check_eq_true
  simp only [class2Check, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cosetInv_two_eq :
    cosetInv 2 = qmatClass (cosetElt 2 734) := by
  have hmem := cosetElt_mem_cosetInv (Or.inr (Or.inl rfl)) (by norm_num) class2Check_spec.2.2
  have hsub : qmatClass (cosetElt 2 734) ⊆ cosetInv 2 := fun g hg =>
    ⟨(qmatClass_subset 2 hmem.1 g hg).1, (qmatClass_subset 2 hmem.1 g hg).2.2 hmem.2⟩
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (cosetInv_finite (Or.inr (Or.inl rfl)))).symm
  rw [ncard_cosetInv_two, ncard_qmatClass_of_natCertOK 2 class2Check_spec.1, class2Check_spec.2.1]

theorem mem_qmatClass_seventeen :
    cosetElt 1 196668 ∈ qmatClass (classRep 17) := by
  have h := class17Check_eq_true
  simp only [class17Check, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨j, hj, e⟩ := h
  rw [classRep, qmatClass_eq_of_natCertOK 1 (classCheck_spec (k := 17) (by norm_num)).1]
  exact ⟨j, hj, congrArg (cosetElt 1) e⟩

theorem qOfEnc_eq_qP {s A D n : ℕ} (hs : s < 2) (hA : A < 2 ^ 12) (hD : D < 2 ^ 12)
    (hn : pauliEnc s A D = n) : qOfEnc n = qP s A D := by
  rw [← hn]
  exact qOfEnc_pauliEnc hs hA hD

theorem visible_involution_coset_enumeration :
    ((cosetRep 1 * cosetRep 1 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = 1 ∧
    ((cosetRep 2 * cosetRep 2 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv (qP 1 63 0) ∧
    ((cosetRep 6 * cosetRep 6 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = xB ∧
    (∀ r : Q, (rhoGvis r : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv r) ∧
    (∀ f : Gvis, qmatClass f = {g | ∃ u ∈ rhoQ.subgroupOf Gvis, g = u⁻¹ * f * u}) ∧
    (∀ i ∈ ({1, 2, 6} : Finset ℕ), cosetInv i = {f | f ∈ cosetR i ∧ f * f = 1} ∧
      (∀ f ∈ cosetR i, f ≠ 1) ∧ cosetInv i = {f | f ∈ cosetR i ∧ orderOf f = 2}) ∧
    (cosetInv 1).ncard = 69632 ∧ (cosetInv 2).ncard = 8192 ∧ (cosetInv 6).ncard = 0 ∧
    (cosetOrbits 1).length = 137 ∧
    {C : Set Gvis | ∃ f ∈ cosetInv 1, C = qmatClass f}.ncard = 137 ∧
    (∀ k < 137, classRep k = cosetRep 1 * rhoGvis (qOfEnc (classEnc k)) ∧
      classEnc k = ((cosetOrbits 1).map OrbitRecord.rep).getD k 0 ∧ classEnc k < 2 ^ 25 ∧
      classRep k ∈ cosetInv 1 ∧ qmatClass (classRep k) ⊆ cosetInv 1) ∧
    (∀ f ∈ cosetInv 1, ∃ k < 137, f ∈ qmatClass (classRep k)) ∧
    (∀ k < 137, ∀ k' < 137, k ≠ k' →
      Disjoint (qmatClass (classRep k)) (qmatClass (classRep k'))) ∧
    (∀ k < 137, ∀ n < 2 ^ 25,
      cosetRep 1 * rhoGvis (qOfEnc n) ∈ qmatClass (classRep k) → classEnc k ≤ n) ∧
    (∀ k < 136, classEnc k < classEnc (k + 1)) ∧
    (∀ k < 137, (qmatClass (classRep k)).ncard = classSize k ∧
      classSize k = ((cosetOrbits 1).map OrbitRecord.size).getD k 0 ∧
      classSize k = if k = 0 ∨ k = 4 then 256 else 512) ∧
    qOfEnc (classEnc 0) = qP 0 0 0 ∧ qOfEnc (classEnc 4) = qP 0 63 0 ∧
    cosetInv 2 = qmatClass (cosetRep 2 * rhoGvis (qP 0 734 0)) ∧
    (cosetOrbits 2).map OrbitRecord.rep = [734] ∧ (cosetOrbits 2).map OrbitRecord.size = [8192] ∧
    pauliEnc 0 60 48 = 196668 ∧
    cosetRep 1 * rhoGvis (qP 0 60 48) ∈ qmatClass (classRep 17) := by
  obtain ⟨h1, h2, h6⟩ := cosetRep_sq
  have hi : ∀ i ∈ ({1, 2, 6} : Finset ℕ), 1 ≤ i ∧ i < 7 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega
  have q734 : qOfEnc 734 = qP 0 734 0 :=
    qOfEnc_eq_qP (by norm_num) (by norm_num) (by norm_num) (by norm_num [pauliEnc])
  have q196668 : qOfEnc 196668 = qP 0 60 48 :=
    qOfEnc_eq_qP (by norm_num) (by norm_num) (by norm_num) (by norm_num [pauliEnc])
  refine ⟨h1, h2, h6, coe_rhoGvis, fun _ => rfl, fun i hi' => ⟨rfl, fun f hf =>
    ne_one_of_mem_cosetR (hi i hi').1 (hi i hi').2 hf, cosetInv_eq_orderOf (hi i hi').1
      (hi i hi').2⟩, ncard_cosetInv_one, ncard_cosetInv_two, ncard_cosetInv_six,
    cosetOrbits_one_length, ncard_classes, fun k hk => ⟨rfl, rfl, classEnc_lt hk,
      classRep_mem hk, qmatClass_classRep_subset hk⟩,
    fun f hf => mem_qmatClass_of_mem_cosetInv_one hf,
    fun k hk k' hk' hne => disjoint_qmatClass_classRep hk hk' hne,
    fun k hk n hn h => classEnc_le_of_mem hk hn h, classEnc_succ,
    fun k hk => ⟨ncard_qmatClass_classRep hk, rfl, classSize_eq k hk⟩, ?_, ?_, ?_,
    cosetOrbits_two.1, cosetOrbits_two.2, by norm_num [pauliEnc], ?_⟩
  · rw [classEnc_zero]
    exact qOfEnc_eq_qP (by norm_num) (by norm_num) (by norm_num) (by norm_num [pauliEnc])
  · rw [classEnc_four]
    exact qOfEnc_eq_qP (by norm_num) (by norm_num) (by norm_num) (by norm_num [pauliEnc])
  · rw [← q734]
    exact cosetInv_two_eq
  · rw [← q196668]
    exact mem_qmatClass_seventeen

end CFSG.Monster.B.TwoA.Census
