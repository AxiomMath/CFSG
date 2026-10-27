module

public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer

public noncomputable section

namespace CFSG.Timmesfeld.ExceptionalOrders

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem

variable {τ : Tag}

@[expose] def symDiag (τ : Tag) (i : Fin τ.rank) : ℤ := τ.symmetrizer i i

theorem symDiag_pos (i : Fin τ.rank) : 0 < symDiag τ i := by
  cases τ <;> revert i <;> decide

theorem symDiag_mul_cartan (i j : Fin τ.rank) :
    symDiag τ i * τ.cartan i j = symDiag τ j * τ.cartan j i := by
  cases τ <;> revert i j <;> decide

@[expose] def label (τ : Tag) (x : Fin τ.rank → ℤ) (i : Fin τ.rank) : ℤ :=
  ∑ j, τ.cartan i j * x j

@[expose] def pairing (τ : Tag) (γ x : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, γ i * symDiag τ i * label τ x i

theorem reflect_eq_label (k : Fin τ.rank) (x : Fin τ.rank → ℤ) :
    reflect τ k x = x - label τ x k • Pi.single k 1 :=
  rfl

theorem label_reflect (i k : Fin τ.rank) (x : Fin τ.rank → ℤ) :
    label τ (reflect τ k x) i = label τ x i - label τ x k * τ.cartan i k := by
  rw [reflect_eq_label]
  simp only [label, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem pairing_reflect (k : Fin τ.rank) (γ x : Fin τ.rank → ℤ) :
    pairing τ (reflect τ k γ) (reflect τ k x) = pairing τ γ x := by
  set c := label τ γ k
  set m := label τ x k
  have h1 : ∑ i, γ i * symDiag τ i * τ.cartan i k = symDiag τ k * c := by
    simp only [c, label, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, symDiag_mul_cartan]
    ring
  have expand : ∀ i, reflect τ k γ i * symDiag τ i * label τ (reflect τ k x) i =
      γ i * symDiag τ i * label τ x i - m * (γ i * symDiag τ i * τ.cartan i k) -
        (if k = i then c * symDiag τ k * (label τ x k - m * τ.cartan k k) else 0) := by
    intro i
    rw [label_reflect, reflect_eq_label]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases h : i = k
    · subst h
      simp only [ite_true]
      ring
    · simp only [h, ite_false, Ne.symm h]
      ring
  rw [pairing, Finset.sum_congr rfl fun i _ => expand i, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, h1, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true, Tag.cartan_self]
  simp only [pairing]
  ring

theorem pairing_smul (w : WeylGroup τ) (γ x : Fin τ.rank → ℤ) :
    pairing τ (w • γ) (w • x) = pairing τ γ x := by
  induction w using (coxeterSystem τ).simple_induction_left generalizing γ x with
  | one => simp
  | mul_simple_left w i ih =>
    rw [mul_smul, mul_smul]
    change pairing τ (simple τ i • _) (simple τ i • _) = _
    rw [simple_smul, simple_smul, pairing_reflect, ih]

theorem pairing_neg (γ x : Fin τ.rank → ℤ) : pairing τ (-γ) x = -pairing τ γ x := by
  simp [pairing, ← Finset.sum_neg_distrib]

theorem pairing_nonneg {J : Set (Fin τ.rank)} {β x : Fin τ.rank → ℤ} (hβ : ∀ i, 0 ≤ β i)
    (hsupp : ∀ i ∉ J, β i = 0) (hx : ∀ i ∈ J, 0 ≤ label τ x i) : 0 ≤ pairing τ β x := by
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hi : i ∈ J
  · exact mul_nonneg (mul_nonneg (hβ i) (symDiag_pos i).le) (hx i hi)
  · rw [hsupp i hi, zero_mul, zero_mul]

theorem pairing_pos {J : Set (Fin τ.rank)} {β x : Fin τ.rank → ℤ} (hβ : ∀ i, 0 ≤ β i)
    (hsupp : ∀ i ∉ J, β i = 0) (hx : ∀ i ∈ J, 0 ≤ label τ x i) {k : Fin τ.rank}
    (hβk : 0 < β k) (hxk : 0 < label τ x k) : 0 < pairing τ β x := by
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ β i * symDiag τ i * label τ x i := fun i _ => by
    by_cases hi : i ∈ J
    · exact mul_nonneg (mul_nonneg (hβ i) (symDiag_pos i).le) (hx i hi)
    · rw [hsupp i hi, zero_mul, zero_mul]
  have hk' : 0 < β k * symDiag τ k * label τ x k :=
    mul_pos (mul_pos hβk (symDiag_pos k)) hxk
  exact lt_of_lt_of_le hk' (Finset.single_le_sum hnn (Finset.mem_univ k))

@[expose] def rootList (τ : Tag) : List (Fin τ.rank → ℤ) :=
  (List.range τ.rootCertificate.roots.length).map τ.rootCertificate.root

theorem mem_rootList {v : Fin τ.rank → ℤ} : v ∈ rootList τ ↔ IsRoot τ v := by
  rw [rootList, List.mem_map, RootCertificate.isRoot_iff τ.rootCertificate_check]
  simp only [List.mem_range]

theorem nodup_rootList : (rootList τ).Nodup := by
  have h := τ.rootCertificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at h
  refine List.Nodup.of_map (fun v => List.ofFn v) ?_
  rw [rootList, List.map_map]
  exact h

theorem ncard_setOf_isRoot_and (P : (Fin τ.rank → ℤ) → Prop) [DecidablePred P] :
    {v | IsRoot τ v ∧ P v}.ncard = (rootList τ).countP fun v => decide (P v) := by
  classical
  have hset : {v | IsRoot τ v ∧ P v} = (((rootList τ).filter fun v => decide (P v)).toFinset :
      Set (Fin τ.rank → ℤ)) := by
    ext v
    simp [mem_rootList]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_rootList.filter _),
    List.countP_eq_length_filter]

theorem parabolic_eq_parabolicWeylGroup (J : Set (Fin τ.rank)) :
    (coxeterSystem τ).parabolic J = parabolicWeylGroup τ J := by
  refine le_antisymm ((coxeterSystem τ).parabolic_le_iff.2 fun i hi =>
    Subgroup.subset_closure ⟨i, hi, rfl⟩) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨i, hi, rfl⟩
  exact (coxeterSystem τ).simple_mem_parabolic hi

theorem smul_apply_of_mem_parabolic {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ (coxeterSystem τ).parabolic J) (v : Fin τ.rank → ℤ) {i : Fin τ.rank}
    (hi : i ∉ J) : (w • v) i = v i :=
  smul_apply_of_mem_parabolicWeylGroup ((parabolic_eq_parabolicWeylGroup J) ▸ hw) v hi

theorem smul_eq_self_of_mem_parabolic {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ (coxeterSystem τ).parabolic J) {x : Fin τ.rank → ℤ}
    (hx : ∀ i ∈ J, label τ x i = 0) : w • x = x := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).mem_parabolic_iff_exists_wordProd_eq.1 hw
  clear hw
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [wordProd_cons, mul_smul, ih fun j hj => hω j (List.mem_cons_of_mem i hj)]
    change simple τ i • x = x
    rw [simple_smul, reflect_eq_label, hx i (hω i List.mem_cons_self), zero_smul, sub_zero]

theorem height_smul_pos_of_ne_zero {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ (coxeterSystem τ).parabolic J) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hpos : 0 < height γ) {k : Fin τ.rank} (hk : k ∉ J) (hγk : γ k ≠ 0) :
    0 < height (w • γ) := by
  have hγk' : 0 < γ k := lt_of_le_of_ne ((IsRoot.height_pos_iff hγ).1 hpos k) (Ne.symm hγk)
  have h := smul_apply_of_mem_parabolic hw γ hk
  have hr := IsRoot.smul hγ w
  rcases hr.nonneg_or_nonpos with hs | hs
  · exact (IsRoot.height_pos_iff hr).2 hs
  · have := hs k
    omega

theorem height_smul_pos_of_isMinimalCosetRep {J' : Set (Fin τ.rank)} {u : WeylGroup τ}
    (hu : (coxeterSystem τ).IsMinimalCosetRep J' u) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hpos : 0 < height β) (hsupp : ∀ i ∉ J', β i = 0) : 0 < height (u • β) := by
  have hnn : ∀ i ∈ J', ∀ j, 0 ≤ (u • (Pi.single i 1 : Fin τ.rank → ℤ)) j := fun i hi j => by
    rw [smul_def]
    exact CFSG.LieType.RootSystem.nonneg_of_not_isRightDescent _ u i
      ((coxeterSystem τ).isMinimalCosetRep_iff.1 hu i hi) j
  have hβnn := (IsRoot.height_pos_iff hβ).1 hpos
  have h0 : ∀ j, 0 ≤ (u • β) j := fun j => by
    rw [smul_eq_sum_smul_single, Finset.sum_apply]
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases hi : i ∈ J'
    · rw [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (hβnn i) (hnn i hi j)
    · rw [hsupp i hi, zero_smul, Pi.zero_apply]
  exact (IsRoot.height_pos_iff (IsRoot.smul hβ u)).2 h0

theorem label_eq_of_forall_pairing {x y : Fin τ.rank → ℤ}
    (h : ∀ δ, pairing τ δ x = pairing τ δ y) : label τ x = label τ y := by
  funext i
  have hi := h (Pi.single i 1)
  simp only [pairing, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at hi
  exact mul_left_cancel₀ (symDiag_pos i).ne' hi

section Coset

variable {J J' : Set (Fin τ.rank)} {lam : Fin τ.rank → ℤ}

theorem mem_inversionSet_inv_iff (h0 : ∀ i ∈ J', label τ lam i = 0)
    (hpos : ∀ i ∈ J, i ∉ J' → 0 < label τ lam i) {u : WeylGroup τ}
    (hu : u ∈ (coxeterSystem τ).parabolic J) (hmin : (coxeterSystem τ).IsMinimalCosetRep J' u)
    (γ : Fin τ.rank → ℤ) :
    γ ∈ inversionSet u⁻¹ ↔
      IsRoot τ γ ∧ 0 < height γ ∧ (∀ k ∉ J, γ k = 0) ∧ pairing τ γ (u • lam) < 0 := by
  have hu' : u⁻¹ ∈ (coxeterSystem τ).parabolic J := inv_mem hu
  have hpair : pairing τ γ (u • lam) = pairing τ (u⁻¹ • γ) lam := by
    rw [← pairing_smul u⁻¹, inv_smul_smul]
  have hlab : ∀ i ∈ J, 0 ≤ label τ lam i := fun i hi => by
    by_cases hi' : i ∈ J'
    · exact (h0 i hi').ge
    · exact (hpos i hi hi').le
  constructor
  · rintro ⟨hγ, hγpos, -, hneg⟩
    have hsupp : ∀ k ∉ J, γ k = 0 := fun k hk => by
      by_contra hγk
      have := height_smul_pos_of_ne_zero hu' hγ hγpos hk hγk
      omega
    refine ⟨hγ, hγpos, hsupp, ?_⟩
    set β := -(u⁻¹ • γ) with hβdef
    have hβ : IsRoot τ β := IsRoot.neg (IsRoot.smul hγ u⁻¹)
    have hβpos : 0 < height β := by rw [hβdef, height_neg]; omega
    have hβnn := (IsRoot.height_pos_iff hβ).1 hβpos
    have hβsupp : ∀ k ∉ J, β k = 0 := fun k hk => by
      rw [hβdef, Pi.neg_apply, smul_apply_of_mem_parabolic hu' γ hk, hsupp k hk, neg_zero]
    obtain ⟨k, hk, hβk⟩ : ∃ k, k ∉ J' ∧ β k ≠ 0 := by
      by_contra! hall
      have h1 := height_smul_pos_of_isMinimalCosetRep hmin hβ hβpos hall
      rw [hβdef, smul_neg, smul_inv_smul, height_neg] at h1
      omega
    have hkJ : k ∈ J := by
      by_contra hkJ
      exact hβk (hβsupp k hkJ)
    have hp := pairing_pos (J := J) hβnn hβsupp hlab
      (lt_of_le_of_ne (hβnn k) (Ne.symm hβk)) (hpos k hkJ hk)
    rw [hpair, show u⁻¹ • γ = -β by rw [hβdef, neg_neg], pairing_neg]
    omega
  · rintro ⟨hγ, hγpos, hsupp, hneg⟩
    refine ⟨hγ, hγpos, IsRoot.smul hγ u⁻¹, ?_⟩
    have hr := IsRoot.smul hγ u⁻¹
    rcases IsRoot.height_pos_or_neg hr with h | h
    · have hnn := (IsRoot.height_pos_iff hr).1 h
      have hsupp' : ∀ k ∉ J, (u⁻¹ • γ) k = 0 := fun k hk => by
        rw [smul_apply_of_mem_parabolic hu' γ hk, hsupp k hk]
      have := pairing_nonneg (J := J) hnn hsupp' hlab
      rw [← hpair] at this
      omega
    · exact h

theorem length_eq_ncard (h0 : ∀ i ∈ J', label τ lam i = 0)
    (hpos : ∀ i ∈ J, i ∉ J' → 0 < label τ lam i) {u : WeylGroup τ}
    (hu : u ∈ (coxeterSystem τ).parabolic J) (hmin : (coxeterSystem τ).IsMinimalCosetRep J' u) :
    (coxeterSystem τ).length u =
      {γ | IsRoot τ γ ∧ 0 < height γ ∧ (∀ k ∉ J, γ k = 0) ∧ pairing τ γ (u • lam) < 0}.ncard := by
  rw [← (coxeterSystem τ).length_inv, (weyl_inversion_length τ).1]
  congr 1
  ext γ
  exact mem_inversionSet_inv_iff h0 hpos hu hmin γ

end Coset

section Sums

variable (τ) [Fintype (WeylGroup τ)]

open Classical in
@[expose] def parabolicSum (J : Set (Fin τ.rank)) (q : ℕ) : ℕ :=
  ∑ w ∈ Finset.univ.filter (· ∈ (coxeterSystem τ).parabolic J), q ^ (coxeterSystem τ).length w

open Classical in
@[expose] def cosetSum (J J' : Set (Fin τ.rank)) (q : ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u => u ∈ (coxeterSystem τ).parabolic J ∧
    (coxeterSystem τ).IsMinimalCosetRep J' u), q ^ (coxeterSystem τ).length u

variable {τ}

theorem parabolicSum_eq_mul {J J' : Set (Fin τ.rank)} (hJ : J' ⊆ J) (q : ℕ) :
    parabolicSum τ J q = cosetSum τ J J' q * parabolicSum τ J' q := by
  classical
  set cs := coxeterSystem τ
  rw [parabolicSum, cosetSum, parabolicSum, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_
  · rintro ⟨u, v⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact mul_mem h.1.1 (cs.parabolic_mono hJ h.2)
  · rintro ⟨u, v⟩ h ⟨u', v'⟩ h' huv
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h h'
    obtain ⟨_, -, huniq⟩ := cs.existsUnique_isMinimalCosetRep_mul J' (u * v)
    exact (huniq (u, v) ⟨h.1.2, h.2, rfl⟩).trans (huniq (u', v') ⟨h'.1.2, h'.2, huv⟩).symm
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨⟨u, v⟩, ⟨hu, hv, rfl⟩, -⟩ := cs.existsUnique_isMinimalCosetRep_mul J' w
    refine ⟨(u, v), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, hu⟩, hv⟩
    have := mul_mem hw (inv_mem (cs.parabolic_mono hJ hv))
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨u, v⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [cs.length_mul_of_isMinimalCosetRep h.1.2 h.2, pow_add]

theorem parabolicSum_empty (q : ℕ) : parabolicSum τ ∅ q = 1 := by
  classical
  rw [parabolicSum, (coxeterSystem τ).parabolic_empty]
  have : Finset.univ.filter (· ∈ (⊥ : Subgroup (WeylGroup τ))) = {1} := by
    ext w
    simp
  rw [this, Finset.sum_singleton, (coxeterSystem τ).length_one, pow_zero]

theorem parabolicSum_univ (q : ℕ) :
    parabolicSum τ Set.univ q = ∑ w : WeylGroup τ, q ^ (coxeterSystem τ).length w := by
  classical
  rw [parabolicSum, (coxeterSystem τ).parabolic_univ]
  congr 1
  ext w
  simp

end Sums

@[expose] def dualReflect (τ : Tag) (i : Fin τ.rank) (c : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  fun j => c j - c i * τ.cartan j i

theorem label_reflect_eq_dualReflect (i : Fin τ.rank) (x : Fin τ.rank → ℤ) :
    label τ (reflect τ i x) = dualReflect τ i (label τ x) :=
  funext fun j => label_reflect j i x

@[expose] def labelPairing (τ : Tag) (γ c : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, γ i * symDiag τ i * c i

theorem pairing_eq_labelPairing (γ x : Fin τ.rank → ℤ) :
    pairing τ γ x = labelPairing τ γ (label τ x) :=
  rfl

@[expose] def negCount (τ : Tag) (J : Finset (Fin τ.rank)) (c : Fin τ.rank → ℤ) : ℕ :=
  (rootList τ).countP fun γ =>
    decide (0 < height γ ∧ (∀ k, k ∉ J → γ k = 0) ∧ labelPairing τ γ c < 0)

theorem labelPairing_dualReflect (i : Fin τ.rank) (γ c : Fin τ.rank → ℤ) :
    labelPairing τ γ (dualReflect τ i c) = labelPairing τ (reflect τ i γ) c := by
  have h1 : ∑ j, γ j * symDiag τ j * τ.cartan j i = symDiag τ i * label τ γ i := by
    simp only [label, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, symDiag_mul_cartan]
    ring
  have e : ∀ j, γ j * symDiag τ j * (c j - c i * τ.cartan j i) =
      γ j * symDiag τ j * c j - c i * (γ j * symDiag τ j * τ.cartan j i) := fun j => by ring
  have e' : ∀ j, reflect τ i γ j * symDiag τ j * c j =
      γ j * symDiag τ j * c j - (if i = j then label τ γ i * symDiag τ i * c i else 0) :=
    fun j => by
      rw [reflect_eq_label]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases h : j = i
      · subst h
        simp only [ite_true]
        ring
      · simp only [h, ite_false, Ne.symm h]
        ring
  simp only [labelPairing, dualReflect]
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, ← Finset.mul_sum, h1,
    Finset.sum_congr rfl fun j _ => e' j, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

@[expose] def posRootsOn (τ : Tag) (J : Finset (Fin τ.rank)) : Finset (Fin τ.rank → ℤ) :=
  (rootList τ).toFinset.filter fun γ => 0 < height γ ∧ ∀ k, k ∉ J → γ k = 0

theorem mem_posRootsOn {J : Finset (Fin τ.rank)} {γ : Fin τ.rank → ℤ} :
    γ ∈ posRootsOn τ J ↔ IsRoot τ γ ∧ 0 < height γ ∧ ∀ k, k ∉ J → γ k = 0 := by
  rw [posRootsOn, Finset.mem_filter, List.mem_toFinset, mem_rootList]

theorem negCount_eq_card (J : Finset (Fin τ.rank)) (c : Fin τ.rank → ℤ) :
    negCount τ J c = ((posRootsOn τ J).filter fun γ => labelPairing τ γ c < 0).card := by
  classical
  rw [negCount, List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    (nodup_rootList.filter _)]
  congr 1
  ext γ
  simp [posRootsOn, and_assoc]

theorem negCount_dualReflect {J : Finset (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J)
    (c : Fin τ.rank → ℤ) :
    negCount τ J (dualReflect τ i c) + (if c i < 0 then 1 else 0) =
      negCount τ J c + (if 0 < c i then 1 else 0) := by
  classical
  rw [negCount_eq_card, negCount_eq_card]
  simp only [labelPairing_dualReflect]
  set P := posRootsOn τ J
  set Q := P.erase (Pi.single i 1)
  have hne : ∀ k ∉ J, k ≠ i := fun k hk (h : k = i) => hk (h ▸ hi)
  have hei : Pi.single i 1 ∈ P := by
    refine mem_posRootsOn.2 ⟨isRoot_single τ i, ?_, fun k hk => ?_⟩
    · rw [height_single]
      exact one_pos
    · rw [Pi.single_apply, ite_eq_right (hne k hk)]
  have hPQ : P = insert (Pi.single i 1) Q := (Finset.insert_erase hei).symm
  have heQ : Pi.single i 1 ∉ Q := Finset.notMem_erase _ _
  have hQ : ∀ γ ∈ Q, reflect τ i γ ∈ Q := fun γ hγ => by
    obtain ⟨hγne, hγP⟩ := Finset.mem_erase.1 hγ
    obtain ⟨hγ, hpos, hsupp⟩ := mem_posRootsOn.1 hγP
    refine Finset.mem_erase.2 ⟨reflect_ne_single hpos, mem_posRootsOn.2
      ⟨(isRoot_reflect_iff i).2 hγ, height_reflect_pos hγ hpos hγne, fun k hk => ?_⟩⟩
    rw [reflect_apply_of_ne i (hne k hk), hsupp k hk]
  have hcard : (Q.filter fun γ => labelPairing τ (reflect τ i γ) c < 0).card =
      (Q.filter fun γ => labelPairing τ γ c < 0).card := by
    refine Finset.card_nbij' (reflect τ i) (reflect τ i) ?_ ?_ ?_ ?_
    · intro γ hγ
      rw [Finset.mem_coe, Finset.mem_filter] at hγ ⊢
      exact ⟨hQ γ hγ.1, hγ.2⟩
    · intro γ hγ
      rw [Finset.mem_coe, Finset.mem_filter] at hγ ⊢
      refine ⟨hQ γ hγ.1, ?_⟩
      rw [reflect_reflect]
      exact hγ.2
    · intro γ _
      exact reflect_reflect τ i γ
    · intro γ _
      exact reflect_reflect τ i γ
  have hsi : labelPairing τ (Pi.single i 1) c = symDiag τ i * c i := by
    simp [labelPairing, Pi.single_apply]
  have hsi' : labelPairing τ (reflect τ i (Pi.single i 1)) c = -(symDiag τ i * c i) := by
    rw [reflect_single_self]
    simp [labelPairing, Pi.single_apply]
  have hd := symDiag_pos (τ := τ) i
  have hnot : ∀ p : (Fin τ.rank → ℤ) → Prop, ∀ [DecidablePred p],
      Pi.single i 1 ∉ Q.filter p := fun p _ h => heQ (Finset.mem_filter.1 h).1
  rw [hPQ, Finset.filter_insert, Finset.filter_insert, hsi, hsi']
  rcases lt_trichotomy (c i) 0 with h | h | h
  · have h1 : ¬ -(symDiag τ i * c i) < 0 := by nlinarith
    have h2 : symDiag τ i * c i < 0 := by nlinarith
    rw [ite_eq_right h1, ite_eq_left h2, Finset.card_insert_of_notMem (hnot _),
      ite_eq_left h, ite_eq_right (not_lt.2 h.le), hcard]
  · rw [h]
    simp [hcard]
  · have h1 : -(symDiag τ i * c i) < 0 := by nlinarith
    have h2 : ¬ symDiag τ i * c i < 0 := by nlinarith
    rw [ite_eq_left h1, ite_eq_right h2, Finset.card_insert_of_notMem (hnot _),
      ite_eq_right (not_lt.2 h.le), ite_eq_left h, hcard]

structure IsOrbitList (τ : Tag) (J J' : Finset (Fin τ.rank)) (lam : Fin τ.rank → ℤ)
    (L : List (Fin τ.rank → ℤ)) : Prop where
  subset : J' ⊆ J
  zero : ∀ i ∈ J', label τ lam i = 0
  pos : ∀ i ∈ J, i ∉ J' → 0 < label τ lam i
  nodup : L.Nodup
  mem : label τ lam ∈ L
  closed : ∀ c ∈ L, ∀ i ∈ J, dualReflect τ i c ∈ L
  reach : ∀ c ∈ L, ∃ w ∈ (coxeterSystem τ).parabolic (J : Set (Fin τ.rank)), label τ (w • lam) = c

namespace IsOrbitList

variable {J J' : Finset (Fin τ.rank)} {lam : Fin τ.rank → ℤ} {L : List (Fin τ.rank → ℤ)}
  (hL : IsOrbitList τ J J' lam L)
include hL

theorem label_nonneg : ∀ i ∈ (J : Set (Fin τ.rank)), 0 ≤ label τ lam i := fun i hi => by
  by_cases hi' : i ∈ J'
  · exact (hL.zero i hi').ge
  · exact (hL.pos i hi hi').le

theorem length_eq {u : WeylGroup τ} (hu : u ∈ (coxeterSystem τ).parabolic (J : Set (Fin τ.rank)))
    (hmin : (coxeterSystem τ).IsMinimalCosetRep (J' : Set (Fin τ.rank)) u) :
    (coxeterSystem τ).length u = negCount τ J (label τ (u • lam)) := by
  rw [length_eq_ncard (J := J) (J' := J') hL.zero hL.pos hu hmin, negCount,
    ← ncard_setOf_isRoot_and]
  rfl

theorem negCount_label_lam : negCount τ J (label τ lam) = 0 := by
  rw [negCount, List.countP_eq_zero]
  intro γ hγ
  simp only [decide_eq_true_eq, not_and, not_lt]
  intro hγpos hsupp
  exact pairing_nonneg (J := J) ((IsRoot.height_pos_iff (mem_rootList.1 hγ)).1 hγpos) hsupp
    hL.label_nonneg

theorem label_smul_mem {w : WeylGroup τ}
    (hw : w ∈ (coxeterSystem τ).parabolic (J : Set (Fin τ.rank))) : label τ (w • lam) ∈ L := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).mem_parabolic_iff_exists_wordProd_eq.1 hw
  clear hw
  induction ω with
  | nil => simpa using hL.mem
  | cons i ω ih =>
    rw [wordProd_cons, mul_smul]
    change label τ (simple τ i • _) ∈ L
    rw [simple_smul, label_reflect_eq_dualReflect]
    exact hL.closed _ (ih fun j hj => hω j (List.mem_cons_of_mem i hj)) i
      (hω i List.mem_cons_self)

theorem smul_lam_of_mem {v : WeylGroup τ}
    (hv : v ∈ (coxeterSystem τ).parabolic (J' : Set (Fin τ.rank))) : v • lam = lam :=
  smul_eq_self_of_mem_parabolic hv hL.zero

theorem exists_split {w : WeylGroup τ}
    (hw : w ∈ (coxeterSystem τ).parabolic (J : Set (Fin τ.rank))) :
    ∃ a b, a ∈ (coxeterSystem τ).parabolic (J : Set (Fin τ.rank)) ∧
      (coxeterSystem τ).IsMinimalCosetRep (J' : Set (Fin τ.rank)) a ∧
        b ∈ (coxeterSystem τ).parabolic (J' : Set (Fin τ.rank)) ∧ w = a * b := by
  obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, -⟩ := (coxeterSystem τ).existsUnique_isMinimalCosetRep_mul J' w
  refine ⟨a, b, ?_, ha, hb, hab⟩
  have := mul_mem hw (inv_mem ((coxeterSystem τ).parabolic_mono (Finset.coe_subset.2 hL.subset)
    hb))
  rwa [hab, mul_inv_cancel_right] at this

theorem eq_of_label_eq {u u' : WeylGroup τ}
    (hu : u ∈ (coxeterSystem τ).parabolic (J : Set (Fin τ.rank)))
    (hmin : (coxeterSystem τ).IsMinimalCosetRep (J' : Set (Fin τ.rank)) u)
    (hu' : u' ∈ (coxeterSystem τ).parabolic (J : Set (Fin τ.rank)))
    (hmin' : (coxeterSystem τ).IsMinimalCosetRep (J' : Set (Fin τ.rank)) u')
    (h : label τ (u • lam) = label τ (u' • lam)) : u = u' := by
  set cs := coxeterSystem τ
  set w := u⁻¹ * u' with hwdef
  have hw : w ∈ cs.parabolic (J : Set (Fin τ.rank)) := mul_mem (inv_mem hu) hu'
  have hwlam : label τ (w • lam) = label τ lam := by
    refine label_eq_of_forall_pairing fun δ => ?_
    rw [← pairing_smul u δ (w • lam), ← pairing_smul u δ lam, ← mul_smul,
      show u * w = u' by rw [hwdef, mul_inv_cancel_left], pairing_eq_labelPairing,
      pairing_eq_labelPairing, h]
  obtain ⟨a, b, haJ, ha, hb, hab⟩ := hL.exists_split hw
  have hla : label τ (a • lam) = label τ lam := by
    rw [← hwlam, hab, mul_smul, hL.smul_lam_of_mem hb]
  have ha1 : a = 1 := by
    rw [← cs.length_eq_zero_iff, hL.length_eq haJ ha, hla, hL.negCount_label_lam]
  have hwb : w = b := by rw [hab, ha1, one_mul]
  have hu'eq : u' = u * b := by rw [← hwb, hwdef, mul_inv_cancel_left]
  obtain ⟨_, -, huniq⟩ := cs.existsUnique_isMinimalCosetRep_mul J' u'
  exact congrArg Prod.fst ((huniq (u, b) ⟨hmin, hb, hu'eq⟩).trans
    (huniq (u', 1) ⟨hmin', one_mem _, (mul_one _).symm⟩).symm)

theorem exists_eq_label {c : Fin τ.rank → ℤ} (hc : c ∈ L) :
    ∃ u, u ∈ (coxeterSystem τ).parabolic (J : Set (Fin τ.rank)) ∧
      (coxeterSystem τ).IsMinimalCosetRep (J' : Set (Fin τ.rank)) u ∧ label τ (u • lam) = c := by
  obtain ⟨w, hw, rfl⟩ := hL.reach c hc
  obtain ⟨a, b, haJ, ha, hb, hab⟩ := hL.exists_split hw
  exact ⟨a, haJ, ha, by rw [hab, mul_smul, hL.smul_lam_of_mem hb]⟩

variable [Fintype (WeylGroup τ)]

theorem cosetSum_eq_sum (q : ℕ) :
    cosetSum τ J J' q = (L.map fun c => q ^ negCount τ J c).sum := by
  classical
  rw [cosetSum, ← List.sum_toFinset _ hL.nodup]
  refine Finset.sum_bij (fun u _ => label τ (u • lam)) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact List.mem_toFinset.2 (hL.label_smul_mem hu.1)
  · intro u hu u' hu' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
    exact hL.eq_of_label_eq hu.1 hu.2 hu'.1 hu'.2 h
  · intro c hc
    obtain ⟨u, hu, hmin, rfl⟩ := hL.exists_eq_label (List.mem_toFinset.1 hc)
    refine ⟨u, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hu, hmin⟩
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [hL.length_eq hu.1 hu.2]

end IsOrbitList

end CFSG.Timmesfeld.ExceptionalOrders
