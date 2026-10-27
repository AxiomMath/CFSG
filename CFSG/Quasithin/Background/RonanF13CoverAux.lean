module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.RonanF13

theorem eq_one_of_odd_orderOf_of_pow' {K : Type*} [Group K] {w : K}
    (ho : Odd (orderOf w)) {k : ℕ} (hw : w ^ 2 ^ k = 1) : w = 1 := by
  have h1 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hw
  have h2 : Nat.Coprime (orderOf w) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 ho)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem mem_normalizer_of_central_cover {K K' : Type*} [Group K] [Group K'] (π : K →* K')
    (hZ : π.ker ≤ Subgroup.center K) (hodd : ∀ z ∈ π.ker, Odd (orderOf z))
    {T : Subgroup K} (hT : IsPGroup 2 T) {x : K}
    (hx : π x ∈ Subgroup.normalizer ((T.map π : Subgroup K') : Set K')) :
    x ∈ Subgroup.normalizer (T : Set K) := by
  have hTexp : ∀ t ∈ T, ∃ k : ℕ, t ^ 2 ^ k = 1 := fun t ht => by
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hclaim : ∀ y : K, π y ∈ Subgroup.normalizer ((T.map π : Subgroup K') : Set K') →
      ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
    intro y hy t ht
    have hu : π (y * t * y⁻¹) ∈ T.map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy (π t)).mp (Subgroup.mem_map_of_mem π ht)
    obtain ⟨t0, ht0, ht0eq⟩ := Subgroup.mem_map.mp hu
    obtain ⟨z, hzdef⟩ : ∃ z, z = t0⁻¹ * (y * t * y⁻¹) := ⟨_, rfl⟩
    have hz : z ∈ π.ker := by
      rw [hzdef, MonoidHom.mem_ker, map_mul, map_inv, ht0eq, inv_mul_cancel]
    have hu_eq : y * t * y⁻¹ = t0 * z := by rw [hzdef]; group
    have hcomm : Commute t0 z := Subgroup.mem_center_iff.mp (hZ hz) t0
    obtain ⟨k1, hk1⟩ := hTexp t ht
    obtain ⟨k2, hk2⟩ := hTexp t0 ht0
    have hpt : (y * t * y⁻¹) ^ 2 ^ (k1 + k2) = 1 := by
      rw [conj_pow, pow_add, pow_mul, hk1, one_pow]
      simp
    have hpt0 : t0 ^ 2 ^ (k1 + k2) = 1 := by
      rw [add_comm, pow_add, pow_mul, hk2, one_pow]
    have hzp : z ^ 2 ^ (k1 + k2) = 1 := by
      rw [hu_eq, hcomm.mul_pow, hpt0, one_mul] at hpt
      exact hpt
    have hz1 : z = 1 := eq_one_of_odd_orderOf_of_pow' (hodd z hz) hzp
    rw [hu_eq, hz1, mul_one]
    exact ht0
  have hx' : π x⁻¹ ∈ Subgroup.normalizer ((T.map π : Subgroup K') : Set K') := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => hclaim x hx g hg, fun hg => ?_⟩
  simpa [mul_assoc] using hclaim x⁻¹ hx' _ hg

theorem exists_induced_aut {K K' : Type*} [Group K] [Group K'] (π : K →* K')
    (hπ : Function.Surjective π) (α : MulAut K) (hα : ∀ x, α x ∈ π.ker ↔ x ∈ π.ker) :
    ∃ α' : MulAut K', ∀ x, α' (π x) = π (α x) := by
  have he : π.ker.map α = π.ker := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hα x).mpr hx
    · intro hy
      refine ⟨α.symm y, (hα (α.symm y)).mp ?_, α.apply_symm_apply y⟩
      rw [α.apply_symm_apply]
      exact hy
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.congr π.ker π.ker α he).trans (QuotientGroup.quotientKerEquivOfSurjective π hπ)),
    fun x => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π x) =
      (QuotientGroup.mk x : K ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, QuotientGroup.congr_mk]
  rfl

theorem induced_aut_pow {K K' : Type*} [Group K] [Group K'] (π : K →* K')
    (hπ : Function.Surjective π) (α : MulAut K) (α' : MulAut K')
    (h : ∀ x, α' (π x) = π (α x)) (m : ℕ) (hm : α ^ m = 1) : α' ^ m = 1 := by
  have key : ∀ j : ℕ, ∀ x : K, (α' ^ j) (π x) = π ((α ^ j) x) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, h, ih]
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  rw [key m x, hm]
  simp

theorem odd_orderOf_induced {K K' : Type*} [Group K] [Group K'] (π : K →* K')
    (hπ : Function.Surjective π) (α : MulAut K) (α' : MulAut K')
    (h : ∀ x, α' (π x) = π (α x)) (hodd : Odd (orderOf α)) : Odd (orderOf α') :=
  Odd.of_dvd_nat hodd
    (orderOf_dvd_of_pow_eq_one (induced_aut_pow π hπ α α' h (orderOf α) (pow_orderOf_eq_one α)))

end CFSG.Quasithin.RonanF13
