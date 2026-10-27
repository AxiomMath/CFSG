module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.H13.N1246.SL27

theorem mem_of_transfer {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    {H K : Subgroup G} (hKH : K ≤ H) (hKn : (K.subgroupOf H).Normal) (hodd : ¬ 2 ∣ H.index)
    (h2 : ∀ x ∈ H, ∃ j : ℕ, x ^ 2 ^ j ∈ K)
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ K)
    {d : G} (hd : ∀ g : G, g * d = d * g) (hdH : d ∈ H) : d ∈ K := by
  letI : CommGroup (H ⧸ K.subgroupOf H) :=
    { (inferInstance : Group (H ⧸ K.subgroupOf H)) with
      mul_comm := fun a b => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have hxy := hcomm (y : G)⁻¹ (H.inv_mem y.2) (x : G)⁻¹ (H.inv_mem x.2)
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]
          using hxy }
  obtain ⟨ϕ, hϕ⟩ : ∃ ϕ : H →* H ⧸ K.subgroupOf H, ∀ x : H, ϕ x = (x : H ⧸ K.subgroupOf H) :=
    ⟨QuotientGroup.mk' (K.subgroupOf H), fun _ => rfl⟩
  have htriv : ∀ g : G, MonoidHom.transfer ϕ g = 1 := by
    intro g
    haveI : Group.IsPerfect (MonoidHom.transfer ϕ).range := Group.IsPerfect.range _
    have hmem : MonoidHom.transfer ϕ g ∈ (MonoidHom.transfer ϕ).range :=
      MonoidHom.mem_range.mpr ⟨g, rfl⟩
    exact congrArg Subtype.val (Subsingleton.elim (⟨_, hmem⟩ : (MonoidHom.transfer ϕ).range) 1)
  have hkey : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * d ^ k * g₀ ∈ H → g₀⁻¹ * d ^ k * g₀ = d ^ k := by
    intro k g₀ _
    have hc : Commute (d ^ k) g₀ :=
      Commute.pow_left (show Commute d g₀ from (hd g₀).symm) k
    rw [mul_assoc, hc.eq, inv_mul_cancel_left]
  have h1 : ϕ ⟨d, hdH⟩ ^ H.index = 1 := by
    have hz := htriv d
    rw [MonoidHom.transfer_eq_pow ϕ d hkey] at hz
    rw [← map_pow]
    exact hz
  obtain ⟨j, hj⟩ := h2 d hdH
  have h3 : ϕ ⟨d, hdH⟩ ^ 2 ^ j = 1 := by
    rw [← map_pow, hϕ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hj
  have hcop : Nat.Coprime H.index (2 ^ j) :=
    Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
  have hg : ϕ ⟨d, hdH⟩ ^ H.index.gcd (2 ^ j) = 1 := pow_gcd_eq_one.mpr ⟨h1, h3⟩
  have hg1 : H.index.gcd (2 ^ j) = 1 := hcop
  rw [hg1, pow_one] at hg
  rw [hϕ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg
  exact hg

end CFSG.Quasithin.H13.N1246.SL27
end
