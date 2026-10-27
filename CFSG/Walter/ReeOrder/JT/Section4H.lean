module

public import CFSG.Walter.ReeOrder.JT.Section4G
public import CFSG.Walter.ReeOrder.JT.Section3

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

section Orbit

variable {N X : Type*} [Group N] [MulAction N X]

theorem ncard_orbit_le {Λ : Set X} (hΛf : Λ.Finite) {a : X} (ha : MulAction.orbit N a ⊆ Λ) :
    (MulAction.orbit N a).ncard ≤ Λ.ncard :=
  Set.ncard_le_ncard ha hΛf

theorem card_stabilizer_mul_ncard_orbit (a : X) :
    Nat.card (MulAction.stabilizer N a) * (MulAction.orbit N a).ncard = Nat.card N := by
  rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]

theorem ncard_orbit_eq_three {Λ : Set X} (hΛ : Λ.ncard ≤ 4) (hΛf : Λ.Finite) {a : X}
    (ha : MulAction.orbit N a ⊆ Λ) (h27 : 27 ∣ Nat.card N) (h8 : ¬ 8 ∣ Nat.card N)
    (hs : ¬ 27 ∣ Nat.card (MulAction.stabilizer N a)) {τ : N} (hτ : orderOf τ = 2)
    (hτa : τ • a = a) : (MulAction.orbit N a).ncard = 3 := by
  have hrel := card_stabilizer_mul_ncard_orbit (N := N) a
  set o := (MulAction.orbit N a).ncard with ho
  have hle : o ≤ 4 := (ncard_orbit_le hΛf ha).trans hΛ
  have hpos : 0 < o := (Set.ncard_pos (hΛf.subset ha)).mpr ⟨a, MulAction.mem_orbit_self a⟩
  have h2 : 2 ∣ Nat.card (MulAction.stabilizer N a) :=
    hτ ▸ Subgroup.orderOf_dvd_natCard _ (MulAction.mem_stabilizer_iff.mpr hτa)
  have h3 : 3 ∣ o := by
    by_contra h3
    have hcop : Nat.Coprime (3 ^ 3) o :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3)
    exact hs (hcop.dvd_of_dvd_mul_right (hrel ▸ h27))
  have h4 : ¬ 4 ∣ o := fun h4 => h8 (hrel ▸ (show 8 = 2 * 4 by norm_num) ▸ Nat.mul_dvd_mul h2 h4)
  interval_cases o <;> omega

theorem false_of_orbit_three {Λ : Set X} (hΛ : Λ.ncard ≤ 4) (hΛf : Λ.Finite) {a b : X}
    (ha : MulAction.orbit N a ⊆ Λ) (hb : MulAction.orbit N b ⊆ Λ) (hab : a ≠ b)
    (h27 : 27 ∣ Nat.card N) (h8 : ¬ 8 ∣ Nat.card N)
    (hsa : ¬ 27 ∣ Nat.card (MulAction.stabilizer N a))
    (hsb : ¬ 27 ∣ Nat.card (MulAction.stabilizer N b)) {τ : N} (hτ : orderOf τ = 2)
    (hτa : τ • a = a) (hτb : τ • b = b) (hfix : ∀ x ∈ Λ, τ • x = x → x = a ∨ x = b) : False := by
  have hoa := ncard_orbit_eq_three hΛ hΛf ha h27 h8 hsa hτ hτa
  have hob := ncard_orbit_eq_three hΛ hΛf hb h27 h8 hsb hτ hτb
  have hfa : (MulAction.orbit N a).Finite := hΛf.subset ha
  have hfb : (MulAction.orbit N b).Finite := hΛf.subset hb
  have hba : b ∈ MulAction.orbit N a := by
    by_contra hba
    have hdisj : Disjoint (MulAction.orbit N a) (MulAction.orbit N b) := by
      rw [Set.disjoint_left]
      intro x hxa hxb
      apply hba
      rw [← MulAction.orbit_eq_iff.mpr hxa, MulAction.orbit_eq_iff.mpr hxb]
      exact MulAction.mem_orbit_self b
    have := Set.ncard_union_eq hdisj hfa hfb
    have hsub : MulAction.orbit N a ∪ MulAction.orbit N b ⊆ Λ := Set.union_subset ha hb
    have := Set.ncard_le_ncard hsub hΛf
    omega
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c ∈ MulAction.orbit N a, c ≠ a ∧ c ≠ b := by
    by_contra hcon
    push Not at hcon
    have hsub : MulAction.orbit N a ⊆ {a, b} := fun x hx => by
      by_cases hxa : x = a
      · exact Or.inl hxa
      · exact Or.inr (hcon x hx hxa)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hab] at this
    omega
  have horb : MulAction.orbit N a = {a, b, c} := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_ hfa).symm
    · intro x hx
      rcases hx with rfl | rfl | rfl
      · exact MulAction.mem_orbit_self _
      · exact hba
      · exact hc
    · rw [hoa, Set.ncard_insert_of_notMem (by simp [hab, hca.symm]), Set.ncard_pair hcb.symm]
  have hτc : τ • c ∈ MulAction.orbit N a := by
    rw [← MulAction.orbit_eq_iff.mpr hc]
    exact MulAction.mem_orbit c τ
  rw [horb] at hτc
  have hτc' : τ • c = c := by
    rcases hτc with h1 | h1 | h1
    · exact absurd (by rw [← h1, inv_smul_smul] : c = τ⁻¹ • a) (by
        rw [inv_smul_eq_iff.mpr hτa.symm]; exact hca)
    · exact absurd (by rw [← h1, inv_smul_smul] : c = τ⁻¹ • b) (by
        rw [inv_smul_eq_iff.mpr hτb.symm]; exact hcb)
    · exact h1
  rcases hfix c (ha hc) hτc' with h1 | h1
  · exact hca h1
  · exact hcb h1

theorem false_of_orbit_two {Λ : Set X} (hΛ : Λ.ncard ≤ 4) (hΛf : Λ.Finite) {a b : X}
    (ha : MulAction.orbit N a ⊆ Λ) (hb : b ∈ MulAction.orbit N a) (hab : a ≠ b)
    (h27 : ¬ 27 ∣ Nat.card N) (h8 : ¬ 8 ∣ Nat.card N)
    (h9 : 9 ∣ Nat.card (MulAction.stabilizer N a))
    (h4 : 4 ∣ Nat.card (MulAction.stabilizer N a)) : False := by
  have hrel := card_stabilizer_mul_ncard_orbit (N := N) a
  set o := (MulAction.orbit N a).ncard with ho
  have hle : o ≤ 4 := (ncard_orbit_le hΛf ha).trans hΛ
  have hge : 2 ≤ o := by
    have hsub : ({a, b} : Set X) ⊆ MulAction.orbit N a := by
      intro x hx
      rcases hx with rfl | rfl
      · exact MulAction.mem_orbit_self _
      · exact hb
    have := Set.ncard_le_ncard hsub (hΛf.subset ha)
    rwa [Set.ncard_pair hab] at this
  have h3 : ¬ 3 ∣ o := fun h3 =>
    h27 (hrel ▸ (show 27 = 9 * 3 by norm_num) ▸ Nat.mul_dvd_mul h9 h3)
  have h2 : 2 ∣ o := by interval_cases o <;> omega
  exact h8 (hrel ▸ (show 8 = 4 * 2 by norm_num) ▸ Nat.mul_dvd_mul h4 h2)

end Orbit

section ThreeSq

variable {X : Type*} [Group X] [Finite X] {y μ : X}

theorem mem_zpowers_iff_of_orderOf_three {z x : X} (hz : orderOf z = 3) :
    x ∈ Subgroup.zpowers z ↔ x = 1 ∨ x = z ∨ x = z ^ 2 := by
  classical
  rw [(isOfFinOrder_of_finite z).mem_zpowers_iff_mem_range_orderOf, hz]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, pow_zero _⟩
    · exact ⟨1, by norm_num, pow_one _⟩
    · exact ⟨2, by norm_num, rfl⟩

omit [Finite X] in
theorem pow_three_eq_one_of_orderOf {z : X} (hz : orderOf z = 3) : z ^ 3 = 1 :=
  hz ▸ pow_orderOf_eq_one z

theorem disjoint_zpowers_of_not_mem (hμ : (orderOf μ).Prime) (hμy : μ ∉ Subgroup.zpowers y) :
    Disjoint (Subgroup.zpowers y) (Subgroup.zpowers μ) := by
  rw [Subgroup.disjoint_def]
  intro x hxy hxμ
  by_contra hx1
  have hord : orderOf x = orderOf μ := by
    rcases (Nat.dvd_prime hμ).mp (orderOf_dvd_of_mem_zpowers hxμ) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  have heq : Subgroup.zpowers x = Subgroup.zpowers μ :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hxμ)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  exact hμy ((Subgroup.zpowers_le).mpr hxy (heq ▸ Subgroup.mem_zpowers μ))

theorem pow_mul_pow_inj (hy : orderOf y = 3) (hμ : orderOf μ = 3)
    (hμy : μ ∉ Subgroup.zpowers y) {i j i' j' : ℕ} (hi : i < 3) (hj : j < 3) (hi' : i' < 3)
    (hj' : j' < 3) (h : y ^ i * μ ^ j = y ^ i' * μ ^ j') : i = i' ∧ j = j' := by
  have hdisj := disjoint_zpowers_of_not_mem (y := y) (hμ ▸ Nat.prime_three) hμy
  have h1 : μ ^ j * (μ ^ j')⁻¹ = (y ^ i)⁻¹ * y ^ i' := by
    calc μ ^ j * (μ ^ j')⁻¹ = (y ^ i)⁻¹ * (y ^ i * μ ^ j) * (μ ^ j')⁻¹ := by group
      _ = (y ^ i)⁻¹ * (y ^ i' * μ ^ j') * (μ ^ j')⁻¹ := by rw [h]
      _ = (y ^ i)⁻¹ * y ^ i' := by group
  have h2 : μ ^ j * (μ ^ j')⁻¹ = 1 := (Subgroup.disjoint_def.mp hdisj)
    (h1 ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers y i))
      (Subgroup.npow_mem_zpowers y i'))
    (Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers μ j)
      (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers μ j')))
  have hjj : μ ^ j = μ ^ j' := mul_inv_eq_one.mp h2
  have hii : y ^ i = y ^ i' := by
    rw [hjj] at h
    exact mul_right_cancel h
  rw [pow_eq_pow_iff_modEq] at hii hjj
  rw [hy] at hii
  rw [hμ] at hjj
  exact ⟨Nat.ModEq.eq_of_lt_of_lt hii hi hi', Nat.ModEq.eq_of_lt_of_lt hjj hj hj'⟩

theorem exists_pow_mul_pow_of_mem_sup (hy : orderOf y = 3) (hμ : orderOf μ = 3)
    (hc : y * μ = μ * y) {k : X} (hk : k ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers μ) :
    ∃ i < 3, ∃ j < 3, k = y ^ i * μ ^ j := by
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers μ : Set X) := by
    refine (Subgroup.zpowers_le).mpr (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_right hc n).eq).symm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hk
  obtain ⟨a, ha, b, hb, rfl⟩ := hk
  have hpow : ∀ {z x : X}, orderOf z = 3 → x ∈ Subgroup.zpowers z → ∃ i < 3, x = z ^ i := by
    intro z x hz hx
    rcases (mem_zpowers_iff_of_orderOf_three hz).mp hx with rfl | rfl | rfl
    · exact ⟨0, by norm_num, (pow_zero _).symm⟩
    · exact ⟨1, by norm_num, (pow_one _).symm⟩
    · exact ⟨2, by norm_num, rfl⟩
  obtain ⟨i, hi, rfl⟩ := hpow hy ha
  obtain ⟨j, hj, rfl⟩ := hpow hμ hb
  exact ⟨i, hi, j, hj, rfl⟩

theorem eq_zpowers_of_card_three {K : Subgroup X} (hK3 : Nat.card K = 3) {k z : X}
    (hKk : K = Subgroup.zpowers k) (hkz : k ∈ Subgroup.zpowers z) (hz3 : z ^ 3 = 1) :
    K = Subgroup.zpowers z := by
  refine Subgroup.eq_of_le_of_card_ge (hKk ▸ (Subgroup.zpowers_le).mpr hkz) ?_
  rw [Nat.card_zpowers, hK3]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz3)

theorem subgroup_eq_of_card_three (hy : orderOf y = 3) (hμ : orderOf μ = 3)
    (hc : y * μ = μ * y) {K : Subgroup X}
    (hK : K ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers μ) (hK3 : Nat.card K = 3) :
    K = Subgroup.zpowers y ∨ K = Subgroup.zpowers μ ∨ K = Subgroup.zpowers (y * μ) ∨
      K = Subgroup.zpowers (y ^ 2 * μ) := by
  have hy3 := pow_three_eq_one_of_orderOf hy
  have hμ3 := pow_three_eq_one_of_orderOf hμ
  have hK1 : K ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hK3
    omega
  obtain ⟨⟨k, hkK⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK1
  have hk1' : k ≠ 1 := fun h0 => hk1 (Subtype.ext h0)
  have hKk : K = Subgroup.zpowers k := by
    refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hkK) ?_).symm
    rw [Nat.card_zpowers, hK3]
    have h3 : orderOf k ∣ 3 := hK3 ▸ Subgroup.orderOf_dvd_natCard K hkK
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hk1'
    · rw [h1]
  have hcomm : Commute y μ := hc
  obtain ⟨i, hi, j, hj, hk⟩ := exists_pow_mul_pow_of_mem_sup hy hμ hc (hK hkK)
  have hyμ3 : (y * μ) ^ 3 = 1 := by rw [hcomm.mul_pow, hy3, hμ3, one_mul]
  have hy2μ3 : (y ^ 2 * μ) ^ 3 = 1 := by
    rw [(hcomm.pow_left 2).mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hy3,
      one_pow, hμ3, one_mul]
  interval_cases i <;> interval_cases j
  · simp at hk
    exact absurd hk hk1'
  · refine Or.inr (Or.inl (eq_zpowers_of_card_three hK3 hKk ?_ hμ3))
    simp only [pow_zero, one_mul] at hk
    exact hk ▸ Subgroup.npow_mem_zpowers μ 1
  · refine Or.inr (Or.inl (eq_zpowers_of_card_three hK3 hKk ?_ hμ3))
    simp only [pow_zero, one_mul] at hk
    exact hk ▸ Subgroup.npow_mem_zpowers μ 2
  · refine Or.inl (eq_zpowers_of_card_three hK3 hKk ?_ hy3)
    simp only [pow_zero, mul_one] at hk
    exact hk ▸ Subgroup.npow_mem_zpowers y 1
  · refine Or.inr (Or.inr (Or.inl (eq_zpowers_of_card_three hK3 hKk ?_ hyμ3)))
    simp only [pow_one] at hk
    exact hk ▸ Subgroup.mem_zpowers _
  · refine Or.inr (Or.inr (Or.inr (eq_zpowers_of_card_three hK3 hKk ?_ hy2μ3)))
    have : k = (y ^ 2 * μ) ^ 2 := by
      rw [hk, (hcomm.pow_left 2).mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add,
        hy3, one_mul, pow_one]
    exact this ▸ Subgroup.npow_mem_zpowers _ 2
  · refine Or.inl (eq_zpowers_of_card_three hK3 hKk ?_ hy3)
    simp only [pow_zero, mul_one] at hk
    exact hk ▸ Subgroup.npow_mem_zpowers y 2
  · refine Or.inr (Or.inr (Or.inr (eq_zpowers_of_card_three hK3 hKk ?_ hy2μ3)))
    simp only [pow_one] at hk
    exact hk ▸ Subgroup.mem_zpowers _
  · refine Or.inr (Or.inr (Or.inl (eq_zpowers_of_card_three hK3 hKk ?_ hyμ3)))
    have : k = (y * μ) ^ 2 := by rw [hk, hcomm.mul_pow]
    exact this ▸ Subgroup.npow_mem_zpowers _ 2

theorem ncard_subgroups_card_three_le (hy : orderOf y = 3) (hμ : orderOf μ = 3)
    (hc : y * μ = μ * y) :
    {K : Subgroup X | K ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers μ ∧ Nat.card K = 3}.ncard ≤ 4 ∧
      {K : Subgroup X | K ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers μ ∧ Nat.card K = 3}.Finite := by
  have hsub : {K : Subgroup X | K ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers μ ∧ Nat.card K = 3} ⊆
      {Subgroup.zpowers y, Subgroup.zpowers μ, Subgroup.zpowers (y * μ),
        Subgroup.zpowers (y ^ 2 * μ)} := fun K hK => by
    rcases subgroup_eq_of_card_three hy hμ hc hK.1 hK.2 with h1 | h1 | h1 | h1 <;> simp [h1]
  refine ⟨(Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_, (Set.toFinite _).subset hsub⟩
  refine (Set.ncard_insert_le _ _).trans ?_
  refine (Nat.succ_le_succ (Set.ncard_insert_le _ _)).trans ?_
  refine (Nat.succ_le_succ (Nat.succ_le_succ (Set.ncard_insert_le _ _))).trans ?_
  rw [Set.ncard_singleton]

theorem eq_of_conj_mem_of_card_three (hy : orderOf y = 3) (hμ : orderOf μ = 3)
    (hc : y * μ = μ * y) (hμy : μ ∉ Subgroup.zpowers y) {u : X} (huy : u * y * u⁻¹ = y⁻¹)
    (huμ : u * μ * u⁻¹ = μ) {K : Subgroup X}
    (hK : K ≤ Subgroup.zpowers y ⊔ Subgroup.zpowers μ) (hK3 : Nat.card K = 3)
    (huK : ∀ x ∈ K, u * x * u⁻¹ ∈ K) : K = Subgroup.zpowers y ∨ K = Subgroup.zpowers μ := by
  have hy3 := pow_three_eq_one_of_orderOf hy
  have hcomm : Commute y μ := hc
  have hyinv : y⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hy3])
  have key : ∀ i j i' j' : ℕ, i < 3 → j < 3 → i' < 3 → j' < 3 →
      y ^ i * μ ^ j = y ^ i' * μ ^ j' → i = i' ∧ j = j' :=
    fun _ _ _ _ hi hj hi' hj' h => pow_mul_pow_inj hy hμ hμy hi hj hi' hj' h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hμ3 := pow_three_eq_one_of_orderOf hμ
  have hyμ : orderOf (y * μ) = 3 := by
    refine orderOf_eq_prime (by rw [hcomm.mul_pow, hy3, hμ3, one_mul]) (fun h0 => hμy ?_)
    rw [eq_inv_of_mul_eq_one_right h0]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y)
  have hy2μ : orderOf (y ^ 2 * μ) = 3 := by
    refine orderOf_eq_prime (by
      rw [(hcomm.pow_left 2).mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hy3,
        one_pow, hμ3, one_mul]) (fun h0 => hμy ?_)
    rw [eq_inv_of_mul_eq_one_right h0]
    exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers y 2)
  rcases subgroup_eq_of_card_three hy hμ hc hK hK3 with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    have hmem := huK _ (h1 ▸ Subgroup.mem_zpowers (y * μ))
    have hconj : u * (y * μ) * u⁻¹ = y ^ 2 * μ ^ 1 := by
      rw [show u * (y * μ) * u⁻¹ = (u * y * u⁻¹) * (u * μ * u⁻¹) by group, huy, huμ, hyinv,
        pow_one]
    rw [hconj, h1, mem_zpowers_iff_of_orderOf_three hyμ] at hmem
    rcases hmem with h2 | h2 | h2
    · have := (key 2 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [h2]; simp)).1
      omega
    · have := (key 2 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [h2]; simp)).1
      omega
    · have := (key 2 1 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [h2, hcomm.mul_pow])).2
      omega
  · exfalso
    have hmem := huK _ (h1 ▸ Subgroup.mem_zpowers (y ^ 2 * μ))
    have hconj : u * (y ^ 2 * μ) * u⁻¹ = y ^ 1 * μ ^ 1 := by
      rw [show u * (y ^ 2 * μ) * u⁻¹ = (u * y ^ 2 * u⁻¹) * (u * μ * u⁻¹) by group, ← conj_pow,
        huy, huμ, hyinv, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hy3, one_mul]
      simp only [pow_one]
    rw [hconj, h1, mem_zpowers_iff_of_orderOf_three hy2μ] at hmem
    rcases hmem with h2 | h2 | h2
    · have := (key 1 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [h2]; simp)).1
      omega
    · have := (key 1 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [h2, pow_one])).1
      omega
    · have := (key 1 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by rw [h2, (hcomm.pow_left 2).mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num,
          pow_add, hy3, one_mul])).2
      omega

end ThreeSq

section Conj

variable {X : Type*} [Group X] [Finite X]

theorem mem_normalizer_sup_zpowers {A : Subgroup X} {μ g : X}
    (hA : ∀ x ∈ A, g * x * g⁻¹ ∈ A) (hμ : g * μ * g⁻¹ ∈ A ⊔ Subgroup.zpowers μ) :
    g ∈ Subgroup.normalizer ((A ⊔ Subgroup.zpowers μ : Subgroup X) : Set X) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : A ⊔ Subgroup.zpowers μ ≤
      (A ⊔ Subgroup.zpowers μ).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => Subgroup.mem_sup_left (hA a ha)) ((Subgroup.zpowers_le).mpr hμ)
  exact hle hx

omit [Finite X] in
theorem mem_normalizer_zpowers_of_commute {g x : X} (hgx : g * x = x * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set X) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact ((Commute.zpow_left hgx.symm n).eq)

theorem conj_smul_eq_iff {g : X} {K : Subgroup X} :
    MulAut.conj g • K = K ↔ g ∈ Subgroup.normalizer (K : Set X) := by
  constructor
  · intro hK
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    rw [← hK]
    exact ⟨x, hx, rfl⟩
  · intro hg
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    · change Nat.card K ≤ Nat.card (K.map (MulAut.conj g).toMonoidHom)
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem eq_of_le_of_isCyclic {W A B : Subgroup X} (hW : IsCyclic W) (hA : A ≤ W) (hB : B ≤ W)
    (hAB : Nat.card A = Nat.card B) : A = B := by
  have h1 : A.subgroupOf W = B.subgroupOf W := IsCyclic.subgroup_eq_iff_card_eq.mpr (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hAB])
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hA, inf_eq_left.mpr hB] at h1
  exact h1

end Conj

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp : h.p ≠ 2)
include hp

theorem isCyclic_of_le_centralizer
    (h3 : h.p ≠ 3) {u : G} (hu : orderOf u = 2)
    {W : Subgroup G} (hW : IsPGroup 3 W) (hWu : W ≤ Subgroup.centralizer ({u} : Set G)) :
    IsCyclic W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := h.exists_conj_eq_t hp hu
  set W' := W.map (MulAut.conj a).toMonoidHom
  have hW'C : W' ≤ Subgroup.centralizer ({h.t} : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← ha]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hWu hw)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc a * w * a⁻¹ * (a * u * a⁻¹) = a * (w * u) * a⁻¹ := by group
      _ = a * (u * w) * a⁻¹ := by rw [this]
      _ = a * u * a⁻¹ * (a * w * a⁻¹) := by group
  have hW'3 : IsPGroup 3 W' := hW.map _
  have hodd : Odd (Nat.card W') := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hW'3
    rw [hn]
    exact Odd.pow (by decide)
  have hcyc := (h.facts hp).cyclic 3 Nat.prime_three (by norm_num) (fun h0 => h3 h0.symm) W'
    (h.le_F_of_odd hW'C hodd) hW'3
  exact isCyclic_of_surjective
    (W.equivMapOfInjective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective).symm
    (MulEquiv.surjective _)

end JTHyp

namespace Setup

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (s : Setup h) (hp : h.p ≠ 2)
include hp

theorem pow_three_mem_centralizer_T
    {y : G} (hyT : y ∈ Subgroup.normalizer (s.T : Set G)) :
    y ^ 3 ∈ Subgroup.centralizer (s.T : Set G) := by
  have := centralizer_subgroupOf_normalizer_normal s.T
  have h2 := Subgroup.pow_index_mem ((Subgroup.centralizer (s.T : Set G)).subgroupOf
    (Subgroup.normalizer (s.T : Set G))) (⟨y, hyT⟩ : Subgroup.normalizer (s.T : Set G))
  rw [← Subgroup.relIndex, s.relIndex_centralizer_T_normalizer_T hp,
    Subgroup.mem_subgroupOf] at h2
  exact h2

theorem p_ne_three_of_dvd
    (h3 : 3 ∣ Nat.card s.Q) : h.p ≠ 3 := by
  intro hp3
  have h4 := s.four_mul_card_Q hp
  have hf : h.f ≠ 0 := by
    intro hf0
    have := h.five_lt
    rw [hf0, pow_zero] at this
    omega
  obtain ⟨m, hm⟩ : 3 ∣ h.q := by
    rw [JTHyp.q_eq, hp3]
    exact dvd_pow_self 3 hf
  obtain ⟨k, hk⟩ := h3
  have heps : h.eps = 1 ∨ h.eps = -1 := by
    unfold JTHyp.eps
    split_ifs <;> simp
  rw [hk, hm] at h4
  push_cast at h4
  omega

theorem factorization_card_normalizer_Q
    (hS : SuzukiFourGroupTheorem) :
    (Nat.card (Subgroup.normalizer (s.Q : Set G))).factorization 3 =
      (Nat.card s.Q).factorization 3 + 1 := by
  have hQ0 : Nat.card s.Q ≠ 0 := Nat.card_pos.ne'
  rcases s.card_normalizer_Q hp hS with h1 | h1 <;>
    rw [h1, Nat.factorization_mul (by norm_num) hQ0, Finsupp.add_apply]
  · rw [show (24 : ℕ) = 3 * 8 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    ring
  · rw [show (120 : ℕ) = 3 * 40 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    ring

theorem card_dvd_of_isPGroup_three
    (hS : SuzukiFourGroupTheorem) {H : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (s.Q : Set G)) (hH : IsPGroup 3 H) :
    Nat.card H ∣ 3 ^ ((Nat.card s.Q).factorization 3 + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  rw [hk]
  apply pow_dvd_pow
  have hdvd : 3 ^ k ∣ Nat.card (Subgroup.normalizer (s.Q : Set G)) :=
    hk ▸ Subgroup.card_dvd_of_le hHN
  rwa [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne',
    s.factorization_card_normalizer_Q hp hS] at hdvd

include s in
theorem not_eight_dvd_card_normalizer
    {W : Subgroup G} (hWodd : Odd (Nat.card W))
    (hWcyc : ¬ IsCyclic W) : ¬ 8 ∣ Nat.card (Subgroup.normalizer (W : Set G)) := by
  intro h8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := Subgroup.normalizer (W : Set G)) 2 (n := 3) (by norm_num; exact h8)
  set H₁ := H.map (Subgroup.normalizer (W : Set G)).subtype
  have hH₁ : Nat.card H₁ = 8 := by
    rw [Subgroup.card_map_of_injective (Subgroup.normalizer (W : Set G)).subtype_injective, hH]
    norm_num
  have hfac : (Nat.card G).factorization 2 = 3 := by
    have h1 := h.card_sylow hp s.S s.t_mem_S
    rw [Sylow.card_eq_multiplicity, show (8 : ℕ) = 2 ^ 3 by norm_num] at h1
    exact Nat.pow_right_injective le_rfl h1
  let S' : Sylow 2 G := Sylow.ofCard H₁ (by rw [hH₁, hfac]; norm_num)
  obtain ⟨g, hg⟩ := s.lemma_4_2_b hp ⟨hWodd, S', Subgroup.map_subtype_le H⟩
  have : IsCyclic s.Q := s.isCyclic_Q hp
  have hcyc : IsCyclic (W.map (MulAut.conj g).toMonoidHom) := Subgroup.isCyclic_of_le hg
  exact hWcyc (isCyclic_of_surjective
    (W.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
    (MulEquiv.surjective _))

end Setup

namespace Config

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (c : Config h)

theorem μ_not_mem_centralizer_T : c.μ ∉ Subgroup.centralizer (c.T : Set G) := by
  intro hμ
  have hfix : ∀ x ∈ c.T, x = 1 := fun x hx => c.μ_fpf x hx (by
    rw [← (Subgroup.mem_centralizer_iff.mp hμ) x hx, mul_inv_cancel_right])
  have h4 := c.four.card_four
  have : c.T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hfix
  rw [this, Subgroup.card_bot] at h4
  omega

theorem μ_not_mem_Q : c.μ ∉ c.Q := fun hμQ =>
  c.μ_not_mem_centralizer_T (Subgroup.mem_centralizer_iff.mpr fun _ hx =>
    ((Subgroup.mem_centralizer_iff.mp (c.toSetup.T_le_centralizer_Q hx)) c.μ hμQ).symm)

variable (hp : h.p ≠ 2)
include hp

theorem μ_mem_normalizer_Q :
    c.μ ∈ Subgroup.normalizer (c.Q : Set G) :=
  c.toSetup.normalizer_T_le_normalizer_Q hp c.μ_mem_NT

theorem t₁_mem_normalizer_Q :
    c.t₁ ∈ Subgroup.normalizer (c.Q : Set G) :=
  c.toSetup.normalizer_T_le_normalizer_Q hp
    (c.toSetup.centralizer_T_le_normalizer_T (c.toSetup.S_le_centralizer_T c.t₁_mem))

theorem false_of_factorization_eq_one
    (hS : SuzukiFourGroupTheorem) {y : G} (hyQ : y ∈ c.Q)
    (hy : orderOf y = 3) (hm : (Nat.card c.Q).factorization 3 = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3Q : 3 ∣ Nat.card c.Q := hy ▸ Subgroup.orderOf_dvd_natCard _ hyQ
  have hp3 := c.toSetup.p_ne_three_of_dvd hp h3Q
  have hQcyc : IsCyclic c.Q := c.toSetup.isCyclic_Q hp
  set Y := Subgroup.zpowers y with hYdef
  set M := Subgroup.zpowers c.μ with hMdef
  have hYQ : Y ≤ c.Q := (Subgroup.zpowers_le).mpr hyQ
  have hy1 : y ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hy; omega
  have hY1 : Y ≠ ⊥ := by rw [Ne, Subgroup.zpowers_eq_bot]; exact hy1
  have hYcard : Nat.card Y = 3 := by rw [Nat.card_zpowers, hy]
  have hMcard : Nat.card M = 3 := by rw [Nat.card_zpowers, c.orderOf_μ]
  have hNY : Subgroup.normalizer (Y : Set G) = Subgroup.normalizer (c.Q : Set G) :=
    c.toSetup.lemma_4_3 hp hS hYQ hY1
  have hNQY : Subgroup.normalizer (c.Q : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    normalizer_le_normalizer_of_le_isCyclic hQcyc hYQ
  have hμN := c.μ_mem_normalizer_Q hp
  have hμQ := c.μ_not_mem_Q
  have hμY : c.μ ∉ Y := fun h0 => hμQ (hYQ h0)
  have hYM : Y ≠ M := fun h0 => hμY (h0 ▸ Subgroup.mem_zpowers c.μ)
  set W := Y ⊔ M with hWdef
  have hMY : M ≤ Subgroup.normalizer (Y : Set G) := (Subgroup.zpowers_le).mpr (hNQY hμN)
  have hW9 : Nat.card W = 9 := by
    rw [hWdef, sup_comm, card_sup_eq_mul_of_disjoint hMY
      (disjoint_zpowers_of_not_mem (by rw [c.orderOf_μ]; exact Nat.prime_three) hμY).symm,
      hYcard, hMcard]
  have hW3 : IsPGroup 3 W := IsPGroup.of_card (n := 2) (by rw [hW9]; norm_num)
  have hWab : IsMulCommutative W :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hW9]; norm_num)
  have hyW : y ∈ W := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hμW : c.μ ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers c.μ)
  have hc : y * c.μ = c.μ * y :=
    congrArg Subtype.val (hWab.is_comm.comm ⟨y, hyW⟩ ⟨c.μ, hμW⟩)
  have hWcyc : ¬ IsCyclic W := fun hcyc =>
    hYM (eq_of_le_of_isCyclic hcyc le_sup_left le_sup_right (by rw [hYcard, hMcard]))
  have hWN : W ≤ Subgroup.normalizer (c.Q : Set G) :=
    sup_le (hYQ.trans Subgroup.le_normalizer) ((Subgroup.zpowers_le).mpr hμN)
  have ht₁N := c.t₁_mem_normalizer_Q hp
  have ht₁y : c.t₁ * y * c.t₁⁻¹ = y⁻¹ :=
    c.toSetup.conj_eq_inv_of_mem_S hp c.t₁_mem c.t₁_not_mem_T hyQ
  have ht₁μ : c.t₁ * c.μ * c.t₁⁻¹ = c.μ := by rw [← c.comm, mul_inv_cancel_right]
  have ht₁NY : c.t₁ ∈ Subgroup.normalizer (Y : Set G) := hNQY ht₁N
  have ht₁NM : c.t₁ ∈ Subgroup.normalizer (M : Set G) :=
    mem_normalizer_zpowers_of_commute (by rw [c.comm])
  have ht₁NW : c.t₁ ∈ Subgroup.normalizer (W : Set G) :=
    mem_normalizer_sup_zpowers (fun x hx => (Subgroup.mem_normalizer_iff.mp ht₁NY x).mp hx)
      (by rw [ht₁μ]; exact hμW)
  have h8 : ¬ 8 ∣ Nat.card (Subgroup.normalizer (W : Set G)) :=
    c.toSetup.not_eight_dvd_card_normalizer hp (by rw [hW9]; decide) hWcyc
  have hyt : y * h.t = h.t * y :=
    (Subgroup.mem_centralizer_iff.mp (c.toSetup.T_le_centralizer_Q c.t_mem_T)) y hyQ
  obtain ⟨g, hg⟩ := h.exists_conj_zpowers_of_orderOf_three hp hp3 hy c.orderOf_μ h.orderOf_t
    c.orderOf_t₁ hyt c.comm
  have hbY : ∀ H : Subgroup G, H ≤ Subgroup.normalizer (Y : Set G) → IsPGroup 3 H →
      Nat.card H ∣ 9 := fun H hH h3 => by
    have := c.toSetup.card_dvd_of_isPGroup_three hp hS (hNY ▸ hH) h3
    rwa [hm] at this
  have hbM : ∀ H : Subgroup G, H ≤ Subgroup.normalizer (M : Set G) → IsPGroup 3 H →
      Nat.card H ∣ 9 := fun H hH h3 => by
    have hle : H.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Y : Set G) := by
      rw [hYdef, ← hg, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hH
    have := hbY _ hle (h3.map _)
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at this
  set NW := Subgroup.normalizer (W : Set G) with hNWdef
  let _ : MulAction NW (Subgroup G) :=
    MulAction.compHom _ ((MulAut.conj : G →* MulAut G).comp NW.subtype)
  have hsmul : ∀ (n : NW) (K : Subgroup G), n • K = MulAut.conj (n : G) • K := fun _ _ => rfl
  have hstab : ∀ (K : Subgroup G) (n : NW),
      n ∈ MulAction.stabilizer NW K ↔ (n : G) ∈ Subgroup.normalizer (K : Set G) := fun K n => by
    rw [MulAction.mem_stabilizer_iff, hsmul, conj_smul_eq_iff]
  have hstab27 : ∀ K : Subgroup G, (∀ H : Subgroup G, H ≤ Subgroup.normalizer (K : Set G) →
      IsPGroup 3 H → Nat.card H ∣ 9) → ¬ 27 ∣ Nat.card (MulAction.stabilizer NW K) := by
    intro K hK h27
    obtain ⟨H', hH'⟩ := Sylow.exists_subgroup_card_pow_prime
      (G := MulAction.stabilizer NW K) 3 (n := 3) (by norm_num; exact h27)
    set H₁ := (H'.map (MulAction.stabilizer NW K).subtype).map NW.subtype
    have hH₁ : Nat.card H₁ = 27 := by
      rw [Subgroup.card_map_of_injective NW.subtype_injective,
        Subgroup.card_map_of_injective (MulAction.stabilizer NW K).subtype_injective, hH']
      norm_num
    have hle : H₁ ≤ Subgroup.normalizer (K : Set G) := by
      rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      exact (hstab K _).mp x.2
    have := hK H₁ hle (IsPGroup.of_card (n := 3) (by rw [hH₁]; norm_num))
    rw [hH₁] at this
    norm_num at this
  set Λ := {K : Subgroup G | K ≤ Y ⊔ M ∧ Nat.card K = 3} with hΛdef
  obtain ⟨hΛ, hΛf⟩ := ncard_subgroups_card_three_le (X := G) hy c.orderOf_μ hc
  have horb : ∀ K ∈ Λ, MulAction.orbit NW K ⊆ Λ := by
    rintro K ⟨hKW, hK3⟩ _ ⟨n, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp n.2 x).mp (hKW hx)
    · change Nat.card (K.map (MulAut.conj (n : G)).toMonoidHom) = 3
      rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hK3]
  have hYΛ : Y ∈ Λ := ⟨le_sup_left, hYcard⟩
  have hMΛ : M ∈ Λ := ⟨le_sup_right, hMcard⟩
  have hG27 : ¬ 27 ∣ Nat.card G := by
    intro h27
    have h27N : 27 ∣ Nat.card NW := by
      have := Sylow.prime_pow_dvd_card_normalizer (p := 3) (n := 2) (by norm_num; exact h27)
        (H := W) (by rw [hW9]; norm_num)
      norm_num at this
      exact this
    refine false_of_orbit_three hΛ hΛf (horb Y hYΛ) (horb M hMΛ) hYM h27N h8 (hstab27 Y hbY)
      (hstab27 M hbM) (τ := ⟨c.t₁, ht₁NW⟩) (by rw [Subgroup.orderOf_mk, c.orderOf_t₁])
      (by rw [hsmul, conj_smul_eq_iff]; exact ht₁NY) (by rw [hsmul, conj_smul_eq_iff]; exact ht₁NM)
      ?_
    intro K hK hτK
    rw [hsmul, conj_smul_eq_iff] at hτK
    exact eq_of_conj_mem_of_card_three hy c.orderOf_μ hc hμY ht₁y ht₁μ hK.1 hK.2
      (fun x hx => (Subgroup.mem_normalizer_iff.mp hτK x).mp hx)
  have hfacG : (Nat.card G).factorization 3 = 2 := by
    have h9 : 3 ^ 2 ∣ Nat.card G := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hW9]
      exact Subgroup.card_subgroup_dvd_card W
    have h27' : ¬ 3 ^ 3 ∣ Nat.card G := by norm_num; exact hG27
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne'] at h9 h27'
    omega
  let P : Sylow 3 G := Sylow.ofCard W (by rw [hW9, hfacG]; norm_num)
  have hPab : IsMulCommutative (P : Subgroup G) := hWab
  have hgμ : g * c.μ * g⁻¹ ∈ Y := by
    rw [hYdef, ← hg]
    exact ⟨c.μ, Subgroup.mem_zpowers _, rfl⟩
  obtain ⟨n, hnN, hn⟩ := Sylow.conj_eq_normalizer_conj_of_mem P c.μ g⁻¹ hμW
    (by rw [inv_inv]; exact Subgroup.mem_sup_left hgμ)
  rw [inv_inv] at hn
  have hn'N : n⁻¹ ∈ NW := Subgroup.inv_mem _ hnN
  set z := n⁻¹ * c.μ * n⁻¹⁻¹ with hz
  have hzY : z ∈ Y := by rw [hz, inv_inv, ← hn]; exact hgμ
  have hzo : orderOf z = 3 := by
    rw [hz, ← MulAut.conj_apply, MulEquiv.orderOf_eq, c.orderOf_μ]
  have hzY' : Subgroup.zpowers z = Y :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hzY)
      (by rw [hYcard, Nat.card_zpowers, hzo])
  rcases c.toSetup.lemma_4_4 hp hS with h44 | ⟨L, D, ⟨eL⟩, hQD, -, hD, hLD⟩
  ·
    set u := n⁻¹ * c.t₁ * n⁻¹⁻¹ with hu
    have hu2 : orderOf u = 2 := by
      rw [hu, ← MulAut.conj_apply, MulEquiv.orderOf_eq, c.orderOf_t₁]
    have huu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
    have huz : u * z = z * u := by
      rw [hu, hz]
      calc n⁻¹ * c.t₁ * n⁻¹⁻¹ * (n⁻¹ * c.μ * n⁻¹⁻¹) = n⁻¹ * (c.t₁ * c.μ) * n⁻¹⁻¹ := by group
        _ = n⁻¹ * (c.μ * c.t₁) * n⁻¹⁻¹ := by rw [c.comm]
        _ = n⁻¹ * c.μ * n⁻¹⁻¹ * (n⁻¹ * c.t₁ * n⁻¹⁻¹) := by group
    have huY : ∀ w ∈ Y, u * w = w * u := by
      intro w hw
      rw [← hzY'] at hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_right huz k).eq
    have huNW : u ∈ NW := NW.mul_mem (NW.mul_mem hn'N ht₁NW) (NW.inv_mem hn'N)
    have huT : u ∈ Subgroup.centralizer (c.T : Set G) := by
      have huNY : u ∈ Subgroup.normalizer (Y : Set G) :=
        mem_normalizer_zpowers_of_commute (huY y (Subgroup.mem_zpowers y))
      have huNT : u ∈ Subgroup.normalizer (c.T : Set G) := h44 ▸ hNY ▸ huNY
      have h3 := c.toSetup.pow_three_mem_centralizer_T hp huNT
      rwa [pow_succ, pow_two, huu, one_mul] at h3
    set k := u * c.μ * u⁻¹ * c.μ⁻¹ with hk
    have hkW : k ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp huNW c.μ).mp hμW) (W.inv_mem hμW)
    have hkT : k ∈ Subgroup.centralizer (c.T : Set G) := by
      rw [hk, show u * c.μ * u⁻¹ * c.μ⁻¹ = u * (c.μ * u⁻¹ * c.μ⁻¹) by group]
      refine Subgroup.mul_mem _ huT ?_
      have := c.toSetup.conj_mem_centralizer_T c.μ_mem_NT (Subgroup.inv_mem _ huT)
      exact this
    have hkY : k ∈ Y := by
      rw [hWdef, sup_comm, ← SetLike.mem_coe,
        Subgroup.coe_mul_of_left_le_normalizer_right _ _ hMY] at hkW
      obtain ⟨a, ha, b, hb, hab⟩ := hkW
      have hbT : b ∈ Subgroup.centralizer (c.T : Set G) := c.toSetup.Q_le_centralizer_T (hYQ hb)
      have haT : a ∈ Subgroup.centralizer (c.T : Set G) := by
        have : a = k * b⁻¹ := by rw [← hab]; group
        rw [this]
        exact Subgroup.mul_mem _ hkT (Subgroup.inv_mem _ hbT)
      have ha1 : a = 1 := by
        by_contra ha1
        have hao : orderOf a = 3 := by
          rcases (Nat.dvd_prime Nat.prime_three).mp
            (c.orderOf_μ ▸ orderOf_dvd_of_mem_zpowers ha) with h1 | h1
          · exact absurd (orderOf_eq_one_iff.mp h1) ha1
          · exact h1
        have haM : Subgroup.zpowers a = M :=
          Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr ha)
            (by rw [hMcard, Nat.card_zpowers, hao])
        exact c.μ_not_mem_centralizer_T ((Subgroup.zpowers_le).mpr haT
          (haM ▸ Subgroup.mem_zpowers c.μ))
      rw [← hab, ha1]
      simpa using hb
    have huk : u * k = k * u := huY k hkY
    have h1 : u * c.μ * u⁻¹ = k * c.μ := by rw [hk]; group
    have hkk : k * k = 1 := by
      have h2 : c.μ = k * k * c.μ := by
        calc c.μ = (u * u) * c.μ * (u * u)⁻¹ := by rw [huu, one_mul, inv_one, mul_one]
          _ = u * (u * c.μ * u⁻¹) * u⁻¹ := by group
          _ = u * (k * c.μ) * u⁻¹ := by rw [h1]
          _ = (u * k) * c.μ * u⁻¹ := by group
          _ = k * (u * c.μ * u⁻¹) := by rw [huk]; group
          _ = k * k * c.μ := by rw [h1]; group
      have := congrArg (· * c.μ⁻¹) h2
      simp only [mul_inv_cancel, mul_inv_cancel_right] at this
      exact this.symm
    have hk1 : k = 1 := by
      have h2 : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hkk)
      have h3 : orderOf k ∣ 3 := hYcard ▸ Subgroup.orderOf_dvd_natCard Y hkY
      have := Nat.dvd_gcd h2 h3
      rw [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one] at this
      exact orderOf_eq_one_iff.mp this
    have huμ : u * c.μ = c.μ * u := by
      have : u * c.μ * u⁻¹ = c.μ := by rw [h1, hk1, one_mul]
      calc u * c.μ = u * c.μ * u⁻¹ * u := by group
        _ = c.μ * u := by rw [this]
    have hWu : W ≤ Subgroup.centralizer ({u} : Set G) :=
      sup_le ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          (huY y (Subgroup.mem_zpowers y)).symm))
        ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr huμ.symm))
    exact hWcyc (h.isCyclic_of_le_centralizer hp hp3 hu2 hW3 hWu)
  ·
    obtain ⟨l₀, hl₀, d₀, hd₀, hμld⟩ := hLD.exists_mul hμN
    have hcld : Commute l₀ d₀ := hLD.commute hl₀ hd₀
    have hμ3 := pow_three_eq_one_of_orderOf c.orderOf_μ
    have h3 : l₀ ^ 3 * d₀ ^ 3 = 1 := by rw [← hcld.mul_pow, hμld, hμ3]
    have hl₀3 : l₀ ^ 3 = 1 := by
      have hinv : l₀ ^ 3 = (d₀ ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
      exact (Subgroup.disjoint_def.mp hLD.2.1) (L.pow_mem hl₀ 3)
        (hinv ▸ D.inv_mem (D.pow_mem hd₀ 3))
    have hd₀3 : d₀ ^ 3 = 1 := by rw [hl₀3, one_mul] at h3; exact h3
    have hd₀Q : d₀ ∈ c.Q := c.toSetup.mem_Q_of_mem_D hp hQD hD hd₀
      (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hd₀3))
    have hd₀Y : d₀ ∈ Y := by
      by_cases hd₀1 : d₀ = 1
      · rw [hd₀1]
        exact Y.one_mem
      · have hd₀o : orderOf d₀ = 3 := orderOf_eq_prime hd₀3 hd₀1
        have : Subgroup.zpowers d₀ = Y := eq_of_le_of_isCyclic hQcyc
          ((Subgroup.zpowers_le).mpr hd₀Q) hYQ (by rw [Nat.card_zpowers, hd₀o, hYcard])
        exact this ▸ Subgroup.mem_zpowers d₀
    have hl₀1 : l₀ ≠ 1 := fun h0 => hμQ (by rw [← hμld, h0, one_mul]; exact hd₀Q)
    have hl₀o : orderOf l₀ = 3 := orderOf_eq_prime hl₀3 hl₀1
    obtain ⟨a', ha'2, ha'l⟩ := exists_inv_of_orderOf_three_of_psl24 eL (x := ⟨l₀, hl₀⟩)
      (by rw [Subgroup.orderOf_mk, hl₀o])
    set a : G := (a' : G) with ha
    have haL : a ∈ L := a'.2
    have ha2 : orderOf a = 2 := by rw [ha, Subgroup.orderOf_coe, ha'2]
    have hal : a * l₀ * a⁻¹ = l₀⁻¹ := congrArg Subtype.val ha'l
    have hD2 : 2 ∣ Nat.card D := by
      have h4 := c.toSetup.four_mul_card_Q hp
      have : (Nat.card D : ℤ) = 2 * Nat.card c.Q := by linarith
      exact ⟨Nat.card c.Q, by exact_mod_cast this⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨d', hd'⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hD2
    set d : G := (d' : G) with hd
    have hdD : d ∈ D := d'.2
    have hd2 : orderOf d = 2 := by rw [hd, Subgroup.orderOf_coe, hd']
    have haC : ∀ x ∈ D, a * x * a⁻¹ = x := fun x hx => by
      rw [hLD.commute haL hx, mul_inv_cancel_right]
    have haNY : a ∈ Subgroup.normalizer (Y : Set G) := mem_normalizer_of_conj_mem fun x hx => by
      rw [haC x (hQD (hYQ hx))]
      exact hx
    have hd₀W : d₀ ∈ W := Subgroup.mem_sup_left hd₀Y
    have haNW : a ∈ NW := by
      refine mem_normalizer_sup_zpowers (fun x hx => by rw [haC x (hQD (hYQ hx))]; exact hx) ?_
      rw [← hμld, show a * (l₀ * d₀) * a⁻¹ = (a * l₀ * a⁻¹) * (a * d₀ * a⁻¹) by group, hal,
        haC d₀ hd₀, show l₀⁻¹ = d₀ * (l₀ * d₀)⁻¹ by group, hμld]
      exact W.mul_mem (W.mul_mem hd₀W (W.inv_mem hμW)) hd₀W
    have hdNY : d ∈ Subgroup.normalizer (Y : Set G) := hNQY (hLD.right_le hdD)
    have hdNW : d ∈ NW := by
      refine mem_normalizer_sup_zpowers
        (fun x hx => (Subgroup.mem_normalizer_iff.mp hdNY x).mp hx) ?_
      have h1 : d * c.μ * d⁻¹ = c.μ * d₀⁻¹ * (d * d₀ * d⁻¹) := by
        rw [← hμld, show d * (l₀ * d₀) * d⁻¹ = (d * l₀) * d₀ * d⁻¹ by group,
          ← hLD.commute hl₀ hdD]
        group
      rw [h1]
      exact W.mul_mem (W.mul_mem hμW (W.inv_mem hd₀W))
        (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hdNY d₀).mp hd₀Y))
    have hadc : Commute a d := hLD.commute haL hdD
    have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
    have hdd : d * d = 1 := by rw [← pow_two, ← hd2, pow_orderOf_eq_one]
    have ha1 : a ≠ 1 := fun h0 => by rw [h0, orderOf_one] at ha2; omega
    have hd1 : d ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hd2; omega
    have had : a ≠ d := fun h0 => ha1 ((Subgroup.disjoint_def.mp hLD.2.1) haL (h0 ▸ hdD))
    set V := GorensteinWalter.kleinFourOfCommutingInvolutions a d haa hdd hadc
    have hV4 : Nat.card V = 4 := (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
      a d haa hdd ha1 hd1 had hadc).card_four
    have hVle : ∀ x ∈ V, x ∈ NW ∧ x ∈ Subgroup.normalizer (Y : Set G) := by
      intro x hx
      change x ∈ ({a * d, a, d, 1} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨NW.mul_mem haNW hdNW, Subgroup.mul_mem _ haNY hdNY⟩
      · exact ⟨haNW, haNY⟩
      · exact ⟨hdNW, hdNY⟩
      · exact ⟨NW.one_mem, Subgroup.one_mem _⟩
    have h4 : 4 ∣ Nat.card (MulAction.stabilizer NW Y) := by
      have hle : V.subgroupOf NW ≤ MulAction.stabilizer NW Y := fun x hx =>
        (hstab Y x).mpr (hVle _ (Subgroup.mem_subgroupOf.mp hx)).2
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun x hx => (hVle x hx).1)).toEquiv,
        hV4] at this
    have h9 : 9 ∣ Nat.card (MulAction.stabilizer NW Y) := by
      have hle : W.subgroupOf NW ≤ MulAction.stabilizer NW Y := fun x hx =>
        (hstab Y x).mpr (hNQY (hWN (Subgroup.mem_subgroupOf.mp hx)))
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv,
        hW9] at this
    have hMorb : M ∈ MulAction.orbit NW Y := by
      rw [MulAction.mem_orbit_symm]
      refine ⟨⟨n⁻¹, hn'N⟩, ?_⟩
      change M.map (MulAut.conj n⁻¹).toMonoidHom = Y
      rw [hMdef, MonoidHom.map_zpowers]
      exact hzY'
    have h27N : ¬ 27 ∣ Nat.card NW := fun h27 =>
      hG27 (h27.trans (Subgroup.card_subgroup_dvd_card NW))
    exact false_of_orbit_two hΛ hΛf (horb Y hYΛ) hMorb hYM h27N h8 h9 h4

theorem false_of_two_le_factorization
    (hS : SuzukiFourGroupTheorem)
    (hH : HuppertMetacyclicTheorem) (h3Q : 3 ∣ Nat.card c.Q)
    (hm : 2 ≤ (Nat.card c.Q).factorization 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 := c.toSetup.p_ne_three_of_dvd hp h3Q
  have hQcyc : IsCyclic c.Q := c.toSetup.isCyclic_Q hp
  set m := (Nat.card c.Q).factorization 3 with hmdef
  obtain ⟨P₃⟩ : Nonempty (Sylow 3 c.Q) := inferInstance
  obtain ⟨⟨⟨x, hxQ⟩, hxP⟩, hxo⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := (P₃ : Subgroup c.Q))
  have hx : orderOf x = 3 ^ m := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Sylow.card_eq_multiplicity] at hxo
    exact hxo
  set Q₃ := Subgroup.zpowers x with hQ₃def
  set M := Subgroup.zpowers c.μ with hMdef
  have hQ₃Q : Q₃ ≤ c.Q := (Subgroup.zpowers_le).mpr hxQ
  have hQ₃card : Nat.card Q₃ = 3 ^ m := by rw [Nat.card_zpowers, hx]
  have hμN := c.μ_mem_normalizer_Q hp
  have hμQ := c.μ_not_mem_Q
  have hμQ₃ : c.μ ∉ Q₃ := fun h0 => hμQ (hQ₃Q h0)
  have hNQQ₃ : Subgroup.normalizer (c.Q : Set G) ≤ Subgroup.normalizer (Q₃ : Set G) :=
    normalizer_le_normalizer_of_le_isCyclic hQcyc hQ₃Q
  have hMQ₃ : M ≤ Subgroup.normalizer (Q₃ : Set G) := (Subgroup.zpowers_le).mpr (hNQQ₃ hμN)
  set W := Q₃ ⊔ M with hWdef
  have hWcard : Nat.card W = 3 ^ (m + 1) := by
    rw [hWdef, sup_comm, card_sup_eq_mul_of_disjoint hMQ₃
      (disjoint_zpowers_of_not_mem (by rw [c.orderOf_μ]; exact Nat.prime_three) hμQ₃).symm,
      Nat.card_zpowers, c.orderOf_μ, hQ₃card, pow_succ, mul_comm]
  have hμW : c.μ ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers c.μ)
  have hxW : x ∈ W := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hWN : W ≤ Subgroup.normalizer (c.Q : Set G) :=
    sup_le (hQ₃Q.trans Subgroup.le_normalizer) ((Subgroup.zpowers_le).mpr hμN)
  have hQ₃W : Q₃ ≤ W := le_sup_left
  have hWQ₃ : W ≤ Subgroup.normalizer (Q₃ : Set G) := sup_le Subgroup.le_normalizer hMQ₃
  have hnorm : (Q₃.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₃W).mpr hWQ₃
  have hidx : (Q₃.subgroupOf W).index = 3 := by
    have h1 := Subgroup.card_mul_index (Q₃.subgroupOf W)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₃W).toEquiv, hQ₃card, hWcard,
      pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  set C := Subgroup.closure ((fun w => w ^ 3) '' (W : Set G)) with hCdef
  have hCQ₃ : C ≤ Q₃ := by
    rw [hCdef, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    have := Subgroup.pow_index_mem (Q₃.subgroupOf W) (⟨w, hw⟩ : W)
    rw [hidx, Subgroup.mem_subgroupOf] at this
    exact this
  have hC1 : C ≠ ⊥ := by
    intro h0
    have hx3 : x ^ 3 ∈ C := Subgroup.subset_closure ⟨x, hxW, rfl⟩
    rw [h0, Subgroup.mem_bot] at hx3
    have h1 := orderOf_dvd_of_pow_eq_one hx3
    rw [hx] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 : 3 ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hNWC : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    have hle : C ≤ C.comap (MulAut.conj g).toMonoidHom := by
      rw [hCdef, Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      change g * w ^ 3 * g⁻¹ ∈ C
      rw [← conj_pow]
      exact Subgroup.subset_closure ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg w).mp hw, rfl⟩
    exact hle hz
  have hNWQ : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (c.Q : Set G) :=
    hNWC.trans (c.toSetup.lemma_4_3 hp hS (hCQ₃.trans hQ₃Q) hC1).le
  have hfacG : (Nat.card G).factorization 3 = m + 1 := by
    have h1 : 3 ^ (m + 1) ∣ Nat.card G := hWcard ▸ Subgroup.card_subgroup_dvd_card W
    have h2 : ¬ 3 ^ (m + 1 + 1) ∣ Nat.card G := by
      intro h2
      have h3 := (Sylow.prime_pow_dvd_card_normalizer h2 hWcard).trans
        (Subgroup.card_dvd_of_le hNWQ)
      rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne',
        c.toSetup.factorization_card_normalizer_Q hp hS] at h3
      omega
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne'] at h1 h2
    omega
  let P : Sylow 3 G := Sylow.ofCard W (by rw [hWcard, hfacG])
  set y := x ^ 3 ^ (m - 1) with hydef
  have hy : orderOf y = 3 := by
    rw [hydef, orderOf_pow_of_dvd (by positivity) (by rw [hx]; exact pow_dvd_pow 3 (by omega)),
      hx, Nat.pow_div (by omega) (by norm_num), show m - (m - 1) = 1 by omega, pow_one]
  have hyQ : y ∈ c.Q := c.Q.pow_mem hxQ _
  by_cases hab : IsMulCommutative W
  ·
    have hPab : IsMulCommutative (P : Subgroup G) := hab
    have hyt : y * h.t = h.t * y :=
      (Subgroup.mem_centralizer_iff.mp (c.toSetup.T_le_centralizer_Q c.t_mem_T)) y hyQ
    obtain ⟨g, hg⟩ := h.exists_conj_zpowers_of_orderOf_three hp hp3 hy c.orderOf_μ h.orderOf_t
      c.orderOf_t₁ hyt c.comm
    have hgμ : g * c.μ * g⁻¹ ∈ Subgroup.zpowers y := by
      rw [← hg]
      exact ⟨c.μ, Subgroup.mem_zpowers _, rfl⟩
    have hyW : Subgroup.zpowers y ≤ W :=
      (Subgroup.zpowers_le).mpr (W.pow_mem hxW _)
    obtain ⟨n, hnN, hn⟩ := Sylow.conj_eq_normalizer_conj_of_mem P c.μ g⁻¹ hμW
      (by rw [inv_inv]; exact hyW hgμ)
    rw [inv_inv] at hn
    have hny : n ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
      normalizer_le_normalizer_of_le_isCyclic hQcyc ((Subgroup.zpowers_le).mpr hyQ) (hNWQ hnN)
    have h1 : n⁻¹ * c.μ * n ∈ Subgroup.zpowers y := by rw [← hn]; exact hgμ
    have h2 := (Subgroup.mem_normalizer_iff.mp hny (n⁻¹ * c.μ * n)).mp h1
    rw [show n * (n⁻¹ * c.μ * n) * n⁻¹ = c.μ by group] at h2
    exact hμQ ((Subgroup.zpowers_le).mpr hyQ h2)
  ·
    have hmeta : IsMetacyclic W := by
      have := hnorm
      refine ⟨Q₃.subgroupOf W, hnorm, ?_, ?_⟩
      · exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQ₃W).symm
          (MulEquiv.surjective _)
      · exact isCyclic_of_prime_card (p := 3) hidx
    obtain ⟨N₀, hN₀, hN₀ne, hN₀3⟩ := hH G 3 (by norm_num) P hab hmeta
    have hodd : Odd N₀.index := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN₀3
      rw [Subgroup.index, hk]
      exact Odd.pow (by decide)
    exact hN₀ne (h.eq_top_of_normal_of_odd_index hp hN₀ hodd)

end Config

namespace Setup

variable {G : Type} [Group G] [Finite G] {h : JTHyp G}

theorem lemma_4_5
    (s : Setup h) (hp : h.p ≠ 2) (hS : SuzukiFourGroupTheorem)
    (hH : HuppertMetacyclicTheorem) : ¬ 3 ∣ Nat.card s.Q := by
  intro h3
  obtain ⟨c, rfl⟩ := s.exists_config hp
  by_cases hm : 2 ≤ (Nat.card c.Q).factorization 3
  · exact c.false_of_two_le_factorization hp hS hH h3 hm
  · have hm1 : (Nat.card c.Q).factorization 3 = 1 := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization (k := 1) Nat.prime_three
        Nat.card_pos.ne').mp (by rw [pow_one]; exact h3)
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := c.Q) 3 h3
    exact c.false_of_factorization_eq_one hp hS y.2 (by rw [Subgroup.orderOf_coe, hy]) hm1

end Setup

end CFSG.Walter.JT
