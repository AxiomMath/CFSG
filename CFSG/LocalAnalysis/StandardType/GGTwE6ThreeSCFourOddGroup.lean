module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.StandardType.SCFourOdd

theorem aut_eq_one_of_central {M : Type} [Group M] (hM : commutator M = ⊤) {Z₀ : Subgroup M}
    (hZ : Z₀ ≤ Subgroup.center M) (α : MulAut M) (h : ∀ m : M, m⁻¹ * α m ∈ Z₀) : α = 1 := by
  have hcen : ∀ y ∈ Z₀, ∀ g : M, g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZ hy) g
  letI : CommGroup Z₀ :=
    { (inferInstance : Group Z₀) with mul_comm := fun x y => Subtype.ext (hcen y y.2 x) }
  let f : M →* Z₀ :=
    { toFun := fun m => ⟨m⁻¹ * α m, h m⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun l m => Subtype.ext (by
        show (l * m)⁻¹ * α (l * m) = l⁻¹ * α l * (m⁻¹ * α m)
        have hc := hcen _ (h l) m⁻¹
        calc (l * m)⁻¹ * α (l * m) = m⁻¹ * (l⁻¹ * α l) * α m := by rw [map_mul]; group
          _ = (l⁻¹ * α l) * m⁻¹ * α m := by rw [hc]
          _ = l⁻¹ * α l * (m⁻¹ * α m) := by group) }
  have hf : ∀ l, f l = 1 := fun l =>
    Abelianization.commutator_subset_ker f (by rw [hM]; exact Subgroup.mem_top l)
  ext l
  have h1 : l⁻¹ * α l = 1 := congrArg Subtype.val (hf l)
  exact (inv_mul_eq_one.mp h1).symm

theorem existsUnique_cube_lift {M : Type} [Group M] {K₂ : Subgroup M} [K₂.Normal]
    (hK : K₂ ≤ Subgroup.center M) (hp : IsPGroup 2 K₂) {n₀ : M ⧸ K₂} (h : n₀ ^ 3 = 1) :
    ∃! n : M, (n : M ⧸ K₂) = n₀ ∧ n ^ 3 = 1 := by
  obtain ⟨m₀, rfl⟩ := QuotientGroup.mk_surjective n₀
  have hz : m₀ ^ 3 ∈ K₂ :=
    (QuotientGroup.eq_one_iff (m₀ ^ 3)).mp (by rw [QuotientGroup.mk_pow]; exact h)
  have hc : Commute m₀ (m₀ ^ 3) := (Subgroup.mem_center_iff.mp (hK hz)) m₀
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hp) ⟨m₀ ^ 3, hz⟩
  have hk' : (m₀ ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by decide)
  have hgcd : Nat.gcd 3 (2 ^ k) = 1 := hcop.gcd_eq_one
  let s : ℤ := Nat.gcdA 3 (2 ^ k)
  have hmod : (3 : ℤ) * s ≡ 1 [ZMOD ((2 ^ k : ℕ) : ℤ)] := by
    simpa [s, hgcd] using Int.gcd_a_modEq 3 (2 ^ k)
  have hdvd : ((2 ^ k : ℕ) : ℤ) ∣ 1 - 3 * s := Int.modEq_iff_dvd.mp hmod
  let n : M := m₀ * (m₀ ^ 3) ^ (-s)
  have hn3 : n ^ 3 = 1 := by
    have hcomm : Commute m₀ ((m₀ ^ 3) ^ (-s)) := hc.zpow_right (-s)
    have hstep : ((m₀ ^ 3) ^ (-s)) ^ 3 = (m₀ ^ 3) ^ (-(3 * s)) := by
      calc ((m₀ ^ 3) ^ (-s)) ^ 3
          = ((m₀ ^ 3) ^ (-s)) ^ (3 : ℤ) :=
            (zpow_natCast ((m₀ ^ 3) ^ (-s)) 3).symm
        _ = (m₀ ^ 3) ^ ((-s) * 3) := (zpow_mul (m₀ ^ 3) (-s) 3).symm
        _ = (m₀ ^ 3) ^ (-(3 * s)) := by congr 1; ring
    calc n ^ 3 = m₀ ^ 3 * ((m₀ ^ 3) ^ (-s)) ^ 3 := hcomm.mul_pow 3
      _ = (m₀ ^ 3) * (m₀ ^ 3) ^ (-(3 * s)) := by rw [hstep]
      _ = (m₀ ^ 3) ^ (1 + -(3 * s)) := by rw [zpow_add, zpow_one]
      _ = (m₀ ^ 3) ^ (1 - 3 * s) := by
            rw [show 1 + -(3 * s) = 1 - 3 * s by ring]
      _ = 1 := by
            obtain ⟨t, ht⟩ := hdvd
            rw [ht, zpow_mul, zpow_natCast, hk', one_zpow]
  have hnq : (n : M ⧸ K₂) = (m₀ : M ⧸ K₂) := by
    show (((m₀ * (m₀ ^ 3) ^ (-s) : M)) : M ⧸ K₂) = (m₀ : M ⧸ K₂)
    have hAq : (((m₀ ^ 3) ^ (-s) : M) : M ⧸ K₂) = 1 := by
      rw [QuotientGroup.mk_zpow, (QuotientGroup.eq_one_iff (m₀ ^ 3)).mpr hz, one_zpow]
    rw [QuotientGroup.mk_mul, hAq, mul_one]
  refine ⟨n, ⟨hnq, hn3⟩, ?_⟩
  rintro n' ⟨hn'q, hn'3⟩
  have hwmem : n⁻¹ * n' ∈ K₂ := by
    rw [← QuotientGroup.eq]
    exact hnq.trans hn'q.symm
  let w : M := n⁻¹ * n'
  have hwcen : Commute n w := (Subgroup.mem_center_iff.mp (hK hwmem)) n
  have hn'_eq : n' = n * w := by
    rw [show w = n⁻¹ * n' from rfl, mul_inv_cancel_left]
  have hw3 : w ^ 3 = 1 := by
    have hh := hn'3
    rw [hn'_eq, hwcen.mul_pow, hn3, one_mul] at hh
    exact hh
  obtain ⟨j, hj⟩ := (isPGroup_iff_pow_pow_eq_one.mp hp) ⟨w, hwmem⟩
  have hj' : w ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hord : orderOf w = 1 :=
    Nat.eq_one_of_dvd_coprimes (a := 3) (b := 2 ^ j) (k := orderOf w)
      (Nat.Coprime.pow_right j (by decide))
      (orderOf_dvd_of_pow_eq_one hw3) (orderOf_dvd_of_pow_eq_one hj')
  rw [hn'_eq, orderOf_eq_one_iff.mp hord, mul_one]

end CFSG.StandardType.SCFourOdd
