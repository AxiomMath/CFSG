module

public import CFSG.Quasithin.Background.F7TwoInvDefs

public section

namespace CFSG.Quasithin.F7Two

variable {Γ : Type*} [Group Γ] {L : Subgroup Γ} {a : Γ}

theorem isPGroup_two_zpowers_iff {y : Γ} :
    IsPGroup 2 ↥(Subgroup.zpowers y) ↔ ∃ n : ℕ, y ^ 2 ^ n = 1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h ⟨y, Subgroup.mem_zpowers y⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  · rintro ⟨n, hn⟩ ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨n, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]

theorem mem_invXi_iff {x : Γ} :
    x ∈ invXi L a ↔ x ∈ L ∧ ∀ n : ℕ, (a * x * a⁻¹ * x⁻¹) ^ 2 ^ n ≠ 1 := by
  show (x ∈ L ∧ ¬ IsPGroup 2 ↥(Subgroup.zpowers (a * x * a⁻¹ * x⁻¹))) ↔ _
  rw [isPGroup_two_zpowers_iff, not_exists]

theorem invXi_subset : invXi L a ⊆ L := fun _ hx => hx.1

theorem closure_invXi_le : Subgroup.closure (invXi L a) ≤ L :=
  (Subgroup.closure_le L).2 invXi_subset

theorem not_mem_invXi_of_commute {x : Γ} (h : a * x = x * a) : x ∉ invXi L a := by
  rw [mem_invXi_iff]
  intro hx
  refine hx.2 0 ?_
  rw [pow_zero, pow_one]
  group
  rw [h]
  group

theorem comm_mem_of_mem (haL : ∀ x ∈ L, a * x * a⁻¹ ∈ L) {x : Γ} (hx : x ∈ L) :
    a * x * a⁻¹ * x⁻¹ ∈ L :=
  L.mul_mem (haL x hx) (L.inv_mem hx)

theorem mul_mem_invXi_of_commute {c x : Γ} (hc : c ∈ L) (hca : a * c = c * a)
    (hx : x ∈ invXi L a) : c * x ∈ invXi L a := by
  rw [mem_invXi_iff] at hx ⊢
  refine ⟨L.mul_mem hc hx.1, fun n hn => hx.2 n ?_⟩
  have e : a * (c * x) * a⁻¹ * (c * x)⁻¹ = c * (a * x * a⁻¹ * x⁻¹) * c⁻¹ := by
    calc a * (c * x) * a⁻¹ * (c * x)⁻¹ = (a * c) * x * a⁻¹ * x⁻¹ * c⁻¹ := by group
      _ = (c * a) * x * a⁻¹ * x⁻¹ * c⁻¹ := by rw [hca]
      _ = c * (a * x * a⁻¹ * x⁻¹) * c⁻¹ := by group
  rw [e, conj_pow, mul_inv_eq_one, mul_eq_left] at hn
  exact hn

theorem inv_mem_invXi {x : Γ} (hx : x ∈ invXi L a) : x⁻¹ ∈ invXi L a := by
  rw [mem_invXi_iff] at hx ⊢
  refine ⟨L.inv_mem hx.1, fun n hn => hx.2 n ?_⟩
  have e : a * x⁻¹ * a⁻¹ * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
  rwa [e, conj_pow, conj_eq_one_iff, inv_pow, inv_eq_one] at hn

theorem centralizer_le_closure_invXi (hne : (invXi L a).Nonempty) :
    L ⊓ Subgroup.centralizer {a} ≤ Subgroup.closure (invXi L a) := by
  obtain ⟨x, hx⟩ := hne
  intro c hc
  have hca : a * c = c * a := (Subgroup.mem_centralizer_singleton_iff.mp hc.2).symm
  have h := Subgroup.mul_mem _ (Subgroup.subset_closure (mul_mem_invXi_of_commute hc.1 hca hx))
    (Subgroup.subset_closure (inv_mem_invXi hx))
  simpa using h

theorem mem_closure_invXi_of_inverted {y : Γ} (hy : y ∈ L) (hodd : Odd (orderOf y))
    (hinv : a * y * a⁻¹ = y⁻¹) : y ∈ Subgroup.closure (invXi L a) := by
  by_cases hy1 : y = 1
  · rw [hy1]
    exact Subgroup.one_mem _
  have hmem : y⁻¹ ∈ invXi L a := by
    rw [mem_invXi_iff]
    refine ⟨L.inv_mem hy, fun n hn => hy1 ?_⟩
    have e : a * y⁻¹ * a⁻¹ * y⁻¹⁻¹ = y ^ 2 := by
      calc a * y⁻¹ * a⁻¹ * y⁻¹⁻¹ = (a * y * a⁻¹)⁻¹ * y := by group
        _ = y ^ 2 := by rw [hinv, inv_inv, sq]
    rw [e, ← pow_mul] at hn
    have hd : orderOf y ∣ 2 ^ (n + 1) := by
      rw [pow_succ']
      exact orderOf_dvd_of_pow_eq_one hn
    exact orderOf_eq_one_iff.mp ((hodd.coprime_two_right.pow_right (n + 1)).eq_one_of_dvd hd)
  simpa using Subgroup.inv_mem _ (Subgroup.subset_closure hmem)

theorem conj_mem_closure_of_forall {S : Set Γ} {c : Γ}
    (h : ∀ x ∈ S, c * x * c⁻¹ ∈ Subgroup.closure S) {x : Γ} (hx : x ∈ Subgroup.closure S) :
    c * x * c⁻¹ ∈ Subgroup.closure S := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

end CFSG.Quasithin.F7Two
