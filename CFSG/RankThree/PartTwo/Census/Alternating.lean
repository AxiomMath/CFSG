module

public import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.LocalAnalysis.SectionRank.Alternating

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven Equiv Equiv.Perm

theorem excluded433_cyclic (p : ℕ) (hp : p.Prime) : Excluded433 (.cyclic p hp) :=
  fun _ _ _ hG e => hG.false_of_commute e fun a b => mul_comm a b

theorem excluded433_alternating_of_le_eight {n : ℕ} (hn : 5 ≤ n) (h8 : n ≤ 8) :
    Excluded433 (.alternating n hn) := by
  intro G _ _ hG e
  refine hG.false_of_localRank_three_le_two e (localRank_le_of_pRank_le Nat.prime_three ?_)
  exact CFSG.SectionRank.pRank_alternating_le_two h8 Nat.prime_three (by norm_num)

section Large

variable {n : ℕ}

abbrev HighLetter (n : ℕ) : Type := {j : Fin n // 4 ≤ j.val}

@[expose] def lowInvolutionPerm (n : ℕ) (hn : 4 ≤ n) : Perm (Fin n) :=
  swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩

theorem lowInvolutionPerm_mem (hn : 4 ≤ n) : lowInvolutionPerm n hn ∈ alternatingGroup (Fin n) := by
  rw [mem_alternatingGroup, lowInvolutionPerm, Perm.sign_mul,
    Perm.sign_swap (by simp [Fin.ext_iff]), Perm.sign_swap (by simp [Fin.ext_iff])]
  rfl

@[expose] def lowInvolution (n : ℕ) (hn : 4 ≤ n) : alternatingGroup (Fin n) :=
  ⟨lowInvolutionPerm n hn, lowInvolutionPerm_mem hn⟩

theorem lowInvolutionPerm_apply_of_four_le (hn : 4 ≤ n) {j : Fin n} (hj : 4 ≤ j.val) :
    lowInvolutionPerm n hn j = j := by
  have h0 : j ≠ ⟨0, by omega⟩ := fun h => by simp [h] at hj
  have h1 : j ≠ ⟨1, by omega⟩ := fun h => by simp [h] at hj
  have h2 : j ≠ ⟨2, by omega⟩ := fun h => by simp [h] at hj
  have h3 : j ≠ ⟨3, by omega⟩ := fun h => by simp [h] at hj
  rw [lowInvolutionPerm, Perm.mul_apply, swap_apply_of_ne_of_ne h2 h3,
    swap_apply_of_ne_of_ne h0 h1]

theorem lowInvolutionPerm_apply_ne_of_lt_four (hn : 4 ≤ n) {j : Fin n} (hj : j.val < 4) :
    lowInvolutionPerm n hn j ≠ j := by
  obtain ⟨j, hjn⟩ := j
  simp only at hj
  interval_cases j <;> simp [lowInvolutionPerm, Perm.mul_apply, swap_apply_def, Fin.ext_iff]

theorem lowInvolutionPerm_apply_lt_four (hn : 4 ≤ n) {j : Fin n} (hj : j.val < 4) :
    (lowInvolutionPerm n hn j).val < 4 := by
  obtain ⟨j, hjn⟩ := j
  simp only at hj
  interval_cases j <;> simp [lowInvolutionPerm, Perm.mul_apply, swap_apply_def, Fin.ext_iff]

theorem lowInvolutionPerm_mul_self (hn : 4 ≤ n) :
    lowInvolutionPerm n hn * lowInvolutionPerm n hn = 1 := by
  ext j
  by_cases hj : j.val < 4
  · obtain ⟨j, hjn⟩ := j
    simp only at hj
    interval_cases j <;> simp [lowInvolutionPerm, Perm.mul_apply, swap_apply_def, Fin.ext_iff]
  · have hj' : 4 ≤ j.val := by omega
    rw [Perm.mul_apply, lowInvolutionPerm_apply_of_four_le hn hj',
      lowInvolutionPerm_apply_of_four_le hn hj', Perm.one_apply]

theorem lowInvolution_ne_one (hn : 4 ≤ n) : lowInvolution n hn ≠ 1 := by
  intro h
  have h' := congrArg (fun σ : alternatingGroup (Fin n) => (σ : Perm (Fin n)) ⟨0, by omega⟩) h
  exact lowInvolutionPerm_apply_ne_of_lt_four hn (j := ⟨0, by omega⟩) (by simp) h'

theorem orderOf_lowInvolution (hn : 4 ≤ n) : orderOf (lowInvolution n hn) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    rw [pow_two]
    exact lowInvolutionPerm_mul_self hn
  · exact lowInvolution_ne_one hn

@[expose] def lowFix (n : ℕ) : Subgroup (alternatingGroup (Fin n)) where
  carrier := {σ | ∀ j : Fin n, j.val < 4 → (σ : Perm (Fin n)) j = j}
  mul_mem' {a b} ha hb j hj := by
    change (a : Perm (Fin n)) ((b : Perm (Fin n)) j) = j
    rw [hb j hj, ha j hj]
  one_mem' _ _ := rfl
  inv_mem' {a} ha j hj := by
    change (a : Perm (Fin n))⁻¹ j = j
    rw [Perm.inv_eq_iff_eq, ha j hj]

theorem mem_lowFix {σ : alternatingGroup (Fin n)} :
    σ ∈ lowFix n ↔ ∀ j : Fin n, j.val < 4 → (σ : Perm (Fin n)) j = j :=
  Iff.rfl

theorem lowFix_apply_high {σ : alternatingGroup (Fin n)} (hσ : σ ∈ lowFix n) (j : Fin n) :
    4 ≤ ((σ : Perm (Fin n)) j).val ↔ 4 ≤ j.val := by
  constructor
  · intro h
    by_contra hj
    have hfix := hσ j (by omega)
    rw [hfix] at h
    omega
  · intro hj
    by_contra h
    have hfix := hσ ((σ : Perm (Fin n)) j) (by omega)
    have := (σ : Perm (Fin n)).injective hfix
    rw [this] at h
    omega

theorem lowFix_commute (hn : 4 ≤ n) {σ : alternatingGroup (Fin n)} (hσ : σ ∈ lowFix n) :
    σ * lowInvolution n hn = lowInvolution n hn * σ := by
  apply Subtype.ext
  refine Equiv.ext fun j => ?_
  change (σ : Perm (Fin n)) (lowInvolutionPerm n hn j) =
    lowInvolutionPerm n hn ((σ : Perm (Fin n)) j)
  by_cases hj : j.val < 4
  · rw [hσ _ (lowInvolutionPerm_apply_lt_four hn hj), hσ j hj]
  · have hj' : 4 ≤ j.val := by omega
    rw [lowInvolutionPerm_apply_of_four_le hn hj',
      lowInvolutionPerm_apply_of_four_le hn ((lowFix_apply_high hσ j).mpr hj')]

theorem commute_of_mem_normalizer (hn : 4 ≤ n) {g : alternatingGroup (Fin n)}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers (lowInvolution n hn) : Set _)) :
    g * lowInvolution n hn = lowInvolution n hn * g := by
  set t := lowInvolution n hn
  have ht2 : t ^ 2 = 1 := by rw [← orderOf_lowInvolution hn]; exact pow_orderOf_eq_one t
  have hmem := (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hconj : g * t * g⁻¹ = t := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have h1 : t ^ (m + m) = 1 := by
        rw [← two_mul, zpow_mul]
        simp [ht2]
      rw [h1] at hk
      exfalso
      apply lowInvolution_ne_one hn
      have := hk.symm
      rwa [mul_inv_eq_one, mul_eq_left] at this
    · have h1 : t ^ (2 * m + 1) = t := by
        rw [zpow_add, zpow_mul]
        simp [ht2]
      rw [h1] at hk
      exact hk.symm
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [hconj]

theorem conj_mem_lowFix (hn : 4 ≤ n) {g σ : alternatingGroup (Fin n)}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers (lowInvolution n hn) : Set _))
    (hσ : σ ∈ lowFix n) : g * σ * g⁻¹ ∈ lowFix n := by
  have hcomm := commute_of_mem_normalizer hn hg
  intro j hj
  have hlow : (((g⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) j).val < 4 := by
    by_contra hhigh
    have hfix := lowInvolutionPerm_apply_of_four_le hn (j := ((g⁻¹ : alternatingGroup (Fin n)) :
      Perm (Fin n)) j) (by omega)
    have hcomm' : g⁻¹ * lowInvolution n hn = lowInvolution n hn * g⁻¹ := by
      calc g⁻¹ * lowInvolution n hn = g⁻¹ * (lowInvolution n hn * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * lowInvolution n hn) * g⁻¹ := by rw [hcomm]
        _ = lowInvolution n hn * g⁻¹ := by group
    have h1 := congrArg (fun τ : alternatingGroup (Fin n) => (τ : Perm (Fin n)) j) hcomm'
    change ((g⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) (lowInvolutionPerm n hn j) =
      lowInvolutionPerm n hn (((g⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) j) at h1
    rw [hfix] at h1
    exact lowInvolutionPerm_apply_ne_of_lt_four hn hj
      (((g⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)).injective h1)
  change (g : Perm (Fin n)) ((σ : Perm (Fin n))
    (((g⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) j)) = j
  rw [hσ _ hlow]
  change ((g * g⁻¹ : alternatingGroup (Fin n)) : Perm (Fin n)) j = j
  rw [mul_inv_cancel]
  rfl

@[expose] noncomputable def lowFixHom (n : ℕ) :
    alternatingGroup (HighLetter n) →* alternatingGroup (Fin n) :=
  ((ofSubtype : Perm (HighLetter n) →* Perm (Fin n)).comp
    (alternatingGroup (HighLetter n)).subtype).codRestrict (alternatingGroup (Fin n)) fun σ => by
      rw [mem_alternatingGroup, MonoidHom.comp_apply, sign_ofSubtype]
      exact σ.2

theorem lowFixHom_injective (n : ℕ) : Function.Injective (lowFixHom n) := by
  intro a b h
  apply Subtype.ext
  apply ofSubtype_injective
  exact congrArg Subtype.val h

theorem range_lowFixHom (n : ℕ) : (lowFixHom n).range = lowFix n := by
  ext σ
  constructor
  · rintro ⟨f, rfl⟩ j hj
    change ofSubtype (f : Perm (HighLetter n)) j = j
    exact ofSubtype_apply_of_not_mem _ (by show ¬ 4 ≤ j.val; omega)
  · intro hσ
    let f : Perm (HighLetter n) := (σ : Perm (Fin n)).subtypePerm fun j => lowFix_apply_high hσ j
    have hf : ofSubtype f = (σ : Perm (Fin n)) := by
      refine ofSubtype_subtypePerm _ fun j hj => ?_
      by_contra hlow
      exact hj (hσ j (by omega))
    have hfmem : f ∈ alternatingGroup (HighLetter n) := by
      rw [mem_alternatingGroup, ← sign_ofSubtype, hf]
      exact σ.2
    exact ⟨⟨f, hfmem⟩, Subtype.ext hf⟩

@[expose] noncomputable def lowFixEquiv (n : ℕ) : alternatingGroup (HighLetter n) ≃* lowFix n :=
  (MonoidHom.ofInjective (lowFixHom_injective n)).trans (MulEquiv.subgroupCongr (range_lowFixHom n))

theorem five_le_card_highLetter (hn : 9 ≤ n) : 5 ≤ Nat.card (HighLetter n) := by
  let f : Fin 5 → HighLetter n := fun k => ⟨⟨k.val + 4, by omega⟩, by simp⟩
  have hf : Function.Injective f := by
    intro a b h
    have := congrArg (fun x : HighLetter n => x.val.val) h
    simp only [f] at this
    exact Fin.ext (by omega)
  calc 5 = Nat.card (Fin 5) := by simp
    _ ≤ Nat.card (HighLetter n) := Nat.card_le_card_of_injective f hf

theorem isSimpleGroup_lowFix (hn : 9 ≤ n) : IsSimpleGroup (lowFix n) := by
  have : IsSimpleGroup (alternatingGroup (HighLetter n)) :=
    alternatingGroup.isSimpleGroup (five_le_card_highLetter hn)
  exact (lowFixEquiv n).symm.isSimpleGroup

@[expose] def highCyclePerm (n : ℕ) (hn : 9 ≤ n) : Perm (Fin n) :=
  swap ⟨4, by omega⟩ ⟨5, by omega⟩ * swap ⟨4, by omega⟩ ⟨6, by omega⟩

theorem highCyclePerm_isThreeCycle (hn : 9 ≤ n) : (highCyclePerm n hn).IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff])

theorem highCyclePerm_mem (hn : 9 ≤ n) : highCyclePerm n hn ∈ alternatingGroup (Fin n) :=
  (highCyclePerm_isThreeCycle hn).mem_alternatingGroup

@[expose] def highCycle (n : ℕ) (hn : 9 ≤ n) : alternatingGroup (Fin n) :=
  ⟨highCyclePerm n hn, highCyclePerm_mem hn⟩

theorem highCycle_mem_lowFix (hn : 9 ≤ n) : highCycle n hn ∈ lowFix n := by
  intro j hj
  change highCyclePerm n hn j = j
  have h4 : j ≠ ⟨4, by omega⟩ := fun h => by simp [h] at hj
  have h5 : j ≠ ⟨5, by omega⟩ := fun h => by simp [h] at hj
  have h6 : j ≠ ⟨6, by omega⟩ := fun h => by simp [h] at hj
  rw [highCyclePerm, Perm.mul_apply, swap_apply_of_ne_of_ne h4 h6, swap_apply_of_ne_of_ne h4 h5]

theorem orderOf_highCycle (hn : 9 ≤ n) : orderOf (highCycle n hn) = 3 := by
  rw [← Subgroup.orderOf_coe]
  exact (highCyclePerm_isThreeCycle hn).orderOf

theorem not_isPGroup_two_lowFix (hn : 9 ≤ n) : ¬ IsPGroup 2 (lowFix n) := by
  intro h
  obtain ⟨k, hk⟩ := h ⟨highCycle n hn, highCycle_mem_lowFix hn⟩
  have hk' : highCycle n hn ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd := orderOf_dvd_of_pow_eq_one hk'
  rw [orderOf_highCycle hn] at hdvd
  have h3 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem not_isCharTwoType_alternating (hn : 9 ≤ n) :
    ¬ IsCharTwoType (alternatingGroup (Fin n)) := by
  have hn4 : 4 ≤ n := by omega
  set t := lowInvolution n hn4
  set L := Subgroup.normalizer (Subgroup.zpowers t : Set (alternatingGroup (Fin n)))
  have hL : IsTwoLocal L := by
    refine ⟨Subgroup.zpowers t, ?_, ?_, rfl⟩
    · rw [Ne, Subgroup.zpowers_eq_bot]
      exact lowInvolution_ne_one hn4
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_lowInvolution hn4,
        pow_one])
  refine not_isCharTwoType_of_normal_subgroup (L := L) (K := lowFix n) hL ?_ ?_ ?_ ?_
  · intro σ hσ
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left (lowFix_commute hn4 hσ).symm k).eq
  · exact fun g hg σ hσ => conj_mem_lowFix hn4 hg hσ
  · intro N hNK hNn hN2
    have : IsSimpleGroup (lowFix n) := isSimpleGroup_lowFix hn
    have hnormal : (N.subgroupOf (lowFix n)).Normal :=
      ⟨fun a ha g => hNn g g.2 a ha⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (lowFix n)) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact (disjoint_of_le_iff_left_eq_bot hNK).mp h
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      exact not_isPGroup_two_lowFix hn (hN2.to_le h)
  · intro h
    have := highCycle_mem_lowFix hn
    rw [h, Subgroup.mem_bot] at this
    have h3 := orderOf_highCycle hn
    rw [this, orderOf_one] at h3
    omega

theorem excluded433_alternating_of_nine_le {n : ℕ} (hn : 5 ≤ n) (h9 : 9 ≤ n) :
    Excluded433 (.alternating n hn) :=
  fun _ _ _ hG e => hG.false_of_not_isCharTwoType e (not_isCharTwoType_alternating h9)

end Large

theorem excluded433_alternating (n : ℕ) (hn : 5 ≤ n) : Excluded433 (.alternating n hn) := by
  rcases le_or_gt n 8 with h8 | h9
  · exact excluded433_alternating_of_le_eight hn h8
  · exact excluded433_alternating_of_nine_le hn h9

end CFSG.RankThree.PartTwo.Census
