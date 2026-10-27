module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148OneRepair

variable {M : Type*} [Group M]

theorem mem_zpowers_pow_three148 {u v : M} (hu3 : u ^ 3 = 1) (hv : v ∈ Subgroup.zpowers u) :
    v = 1 ∨ v = u ∨ v = u ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have h3 : u ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hu3
  rw [zpow_eq_zpow_emod k h3]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h | h | h <;> rw [h]
  · left; exact zpow_zero u
  · right; left; exact zpow_one u
  · right; right; exact zpow_ofNat u 2

theorem zpow_pow_three148 {x : M} (hx : x ^ 3 = 1) (k : ℤ) : (x ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem mem_zpowers_of_mem_zpowers148 {u v : M} (hu3 : u ^ 3 = 1) (hv : v ∈ Subgroup.zpowers u)
    (hv1 : v ≠ 1) : u ∈ Subgroup.zpowers v := by
  rcases mem_zpowers_pow_three148 hu3 hv with rfl | rfl | rfl
  · exact absurd rfl hv1
  · exact Subgroup.mem_zpowers _
  · have h : u = (u ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc u = u ^ 3 * u := by rw [hu3, one_mul]
        _ = u ^ (2 * 2) := by rw [← pow_succ]
    have h2 : (u ^ 2) ^ 2 ∈ Subgroup.zpowers (u ^ 2) :=
      Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
    rwa [← h] at h2

theorem isPGroup_zpowers148 {x : M} (hx : x ^ 3 = 1) : IsPGroup 3 (Subgroup.zpowers x) := by
  rintro ⟨g, hg⟩
  refine ⟨1, ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  apply Subtype.ext
  change (x ^ k) ^ 3 ^ 1 = 1
  rw [pow_one]
  exact zpow_pow_three148 hx k

theorem exists_commute_pow_three_not_mem148 [Finite M] {s t : M} (hs : s ≠ 1)
    (hs3 : s ^ 3 = 1) (ht3 : t ^ 3 = 1) (hst : s * t = t * s) (ht : t ∉ Subgroup.zpowers s)
    (u : M) (hu3 : u ^ 3 = 1) :
    ∃ v : M, u * v = v * u ∧ v ^ 3 = 1 ∧ v ∉ Subgroup.zpowers u := by
  by_contra hcon
  have hcon' : ∀ v : M, u * v = v * u → v ^ 3 = 1 → v ∈ Subgroup.zpowers u := by
    intro v h1 h2
    by_contra h3
    exact hcon ⟨v, h1, h2, h3⟩
  by_cases hu1 : u = 1
  · subst hu1
    have h := hcon' t (by rw [one_mul, mul_one]) ht3
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h
    exact ht (h ▸ Subgroup.one_mem _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := (isPGroup_zpowers148 hu3).exists_le_sylow
  have huT : u ∈ (T : Subgroup M) := hT (Subgroup.mem_zpowers u)
  have hcomm : ∀ w ∈ (T : Subgroup M), u * w = w * u := by
    have hTp : IsPGroup 3 (T : Subgroup M) := T.isPGroup'
    have : Nontrivial (T : Subgroup M) :=
      ⟨⟨⟨u, huT⟩, 1, fun h => hu1 (congrArg Subtype.val h)⟩⟩
    have hZ := hTp.center_nontrivial
    have hZp : IsPGroup 3 (Subgroup.center (T : Subgroup M)) := hTp.to_subgroup _
    have h3 : 3 ∣ Nat.card (Subgroup.center (T : Subgroup M)) := by
      rcases hZp.card_eq_or_dvd with h | h
      · exfalso
        rw [Nat.card_eq_one_iff_unique] at h
        obtain ⟨hsub, -⟩ := h
        exact not_subsingleton _ hsub
      · exact h
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
    set y' : M := ((y : (T : Subgroup M)) : M) with hy'
    have hy3 : y' ^ 3 = 1 := by
      have h1 : y ^ 3 = 1 := by
        have h0 := pow_orderOf_eq_one y
        rwa [hy] at h0
      have h2 := congrArg (fun w => ((w : (T : Subgroup M)) : M)) (congrArg Subtype.val h1)
      simpa using h2
    have hy1 : y' ≠ 1 := by
      intro h1
      have h2 : y = 1 := Subtype.ext (Subtype.ext h1)
      rw [h2, orderOf_one] at hy
      omega
    have hyw : ∀ w ∈ (T : Subgroup M), y' * w = w * y' := by
      intro w hw
      have h1 := Subgroup.mem_center_iff.mp y.2 ⟨w, hw⟩
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul] at h2
      exact h2.symm
    have hyu : y' ∈ Subgroup.zpowers u := hcon' y' (hyw u huT).symm hy3
    have huy : u ∈ Subgroup.zpowers y' := mem_zpowers_of_mem_zpowers148 hu3 hyu hy1
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp huy
    exact ((Commute.zpow_left (hyw w hw : Commute y' w)) k).eq
  have hE : IsPGroup 3 (Subgroup.zpowers s ⊔ Subgroup.zpowers t : Subgroup M) := by
    refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers148 hs3) (isPGroup_zpowers148 ht3) ?_
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have : s * t ^ k * s⁻¹ = t ^ k := by
        rw [((Commute.zpow_right (hst : Commute s t)) k).eq, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hc : s * t ^ k = t ^ k * s := ((Commute.zpow_right (hst : Commute s t)) k).eq
      have : x = t ^ k := by
        calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
          _ = s⁻¹ * t ^ k * s := by rw [hk]
          _ = s⁻¹ * (t ^ k * s) := by group
          _ = s⁻¹ * (s * t ^ k) := by rw [hc]
          _ = t ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k
  obtain ⟨T', hT'⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M T T'
  have hmem : ∀ x ∈ (T' : Subgroup M), g⁻¹ * x * g ∈ (T : Subgroup M) := by
    intro x hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have h1 : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
    rwa [h1] at hx
  have hconj3 : ∀ x : M, x ^ 3 = 1 → (g⁻¹ * x * g) ^ 3 = 1 := by
    intro x hx
    have h1 : (g⁻¹ * x * g⁻¹⁻¹) ^ 3 = g⁻¹ * x ^ 3 * g⁻¹⁻¹ := conj_pow
    rw [inv_inv] at h1
    rw [h1, hx, mul_one, inv_mul_cancel]
  have hs' := hmem s (hT' (Subgroup.mem_sup_left (Subgroup.mem_zpowers s)))
  have ht' := hmem t (hT' (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
  have hs'u : g⁻¹ * s * g ∈ Subgroup.zpowers u := hcon' _ (hcomm _ hs') (hconj3 s hs3)
  have ht'u : g⁻¹ * t * g ∈ Subgroup.zpowers u := hcon' _ (hcomm _ ht') (hconj3 t ht3)
  have hs'1 : g⁻¹ * s * g ≠ 1 := by
    intro h1
    apply hs
    calc s = g * (g⁻¹ * s * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hus' : u ∈ Subgroup.zpowers (g⁻¹ * s * g) := mem_zpowers_of_mem_zpowers148 hu3 hs'u hs'1
  have ht's' : g⁻¹ * t * g ∈ Subgroup.zpowers (g⁻¹ * s * g) :=
    (Subgroup.zpowers_le.mpr hus') ht'u
  apply ht
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht's'
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have h1 : (g⁻¹ * s * g⁻¹⁻¹) ^ k = g⁻¹ * s ^ k * g⁻¹⁻¹ := conj_zpow
  rw [inv_inv] at h1
  rw [h1] at hk
  calc s ^ k = g * (g⁻¹ * s ^ k * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [hk]
    _ = t := by group

end CFSG.RankThree.PartTwo.Sec14.Item148OneRepair
