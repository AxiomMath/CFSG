module

public import CFSG.Quasithin.EmptyFaithful.S14612DA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace SBc13

theorem rot_pow {p : ℕ} [NeZero p] (i : ZMod p) (n : ℕ) :
    (DihedralGroup.r i : DihedralGroup p) ^ n = DihedralGroup.r ((n : ZMod p) * i) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, DihedralGroup.r_zero]
  | succ n ih =>
    rw [pow_succ, ih, DihedralGroup.r_mul_r]
    congr 1
    push_cast
    ring

variable {G : Type} [Group G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem _root_.CFSG.Quasithin.IsDecP.exists_phiP (h : IsDecP T M H p H₀ H₁ H₂ t) :
    ∃ φ : ↥H₁ →* DihedralGroup p, Function.Surjective φ ∧
      ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H := by
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  let φ : ↥H₁ →* DihedralGroup p :=
    e.toMonoidHom.comp (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf H₁))
  refine ⟨φ, e.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  show e (QuotientGroup.mk x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem _root_.CFSG.Quasithin.IsDecP.mem_rotation {φ : ↥H₁ →* DihedralGroup p} {y : G}
    (hy : y ∈ oTwoUpper H₁) :
    ∃ hyH : y ∈ H₁, ∃ i : ZMod p, φ ⟨y, hyH⟩ = DihedralGroup.r i := by
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨hyH, hyodd⟩ := hy
    refine ⟨hyH, ?_⟩
    cases hφ : φ ⟨y, hyH⟩ with
    | r i => exact ⟨i, rfl⟩
    | sr i =>
      exfalso
      have hdvd : orderOf (φ ⟨y, hyH⟩) ∣ orderOf y := by
        have := orderOf_map_dvd φ (⟨y, hyH⟩ : ↥H₁)
        rwa [← Subgroup.orderOf_coe] at this
      rw [hφ, DihedralGroup.orderOf_sr] at hdvd
      have := hyodd.of_dvd_nat hdvd
      exact absurd this (by decide)
  | one =>
    refine ⟨H₁.one_mem, 0, ?_⟩
    have : (⟨1, H₁.one_mem⟩ : ↥H₁) = 1 := rfl
    rw [this, map_one]
    exact DihedralGroup.r_zero.symm
  | mul y z _ _ ihy ihz =>
    obtain ⟨hyH, i, hi⟩ := ihy
    obtain ⟨hzH, j, hj⟩ := ihz
    refine ⟨H₁.mul_mem hyH hzH, i + j, ?_⟩
    have : (⟨y * z, H₁.mul_mem hyH hzH⟩ : ↥H₁) = ⟨y, hyH⟩ * ⟨z, hzH⟩ := rfl
    rw [this, map_mul, hi, hj, DihedralGroup.r_mul_r]
  | inv y _ ih =>
    obtain ⟨hyH, i, hi⟩ := ih
    refine ⟨H₁.inv_mem hyH, -i, ?_⟩
    have : (⟨y⁻¹, H₁.inv_mem hyH⟩ : ↥H₁) = (⟨y, hyH⟩ : ↥H₁)⁻¹ := rfl
    rw [this, map_inv, hi]
    exact DihedralGroup.inv_r i

theorem _root_.CFSG.Quasithin.IsDecP.exists_pow_of_notin (hp : p.Prime)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {k y : G} (hk : k ∈ oTwoUpper H₁) (hkQ : k ∉ pCoreOf 2 H)
    (hy : y ∈ oTwoUpper H₁) : ∃ n : ℕ, y * (k ^ n)⁻¹ ∈ pCoreOf 2 H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, -, hker⟩ := h.exists_phiP
  obtain ⟨hkH, i, hi⟩ := IsDecP.mem_rotation (φ := φ) hk
  obtain ⟨hyH, j, hj⟩ := IsDecP.mem_rotation (φ := φ) hy
  have hi0 : i ≠ 0 := by
    intro h0
    apply hkQ
    apply (hker ⟨k, hkH⟩).mp
    rw [hi, h0, DihedralGroup.r_zero]
  refine ⟨(j * i⁻¹).val, ?_⟩
  have h1 : φ (⟨y, hyH⟩ * (⟨k, hkH⟩ ^ (j * i⁻¹).val)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, hj, hi, rot_pow, ZMod.natCast_zmod_val, mul_assoc,
      inv_mul_cancel₀ hi0, mul_one, DihedralGroup.inv_r]
    rw [DihedralGroup.r_mul_r]
    simp
  have := (hker _).mp h1
  simpa using this

end SBc13

end CFSG.Quasithin
