module

public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.Quasithin.H13.CTK

theorem exists_elemAbelian_of_odd_ker {H Q : Type*} [Group H] [Group Q] [Finite H]
    (ψ : H →* Q) (hψ : Function.Surjective ψ) (hker : Odd (Nat.card ψ.ker))
    {V : Subgroup Q} (hV : ∀ x ∈ V, x ^ 2 = 1) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) :
    ∃ P : Subgroup H, (∀ x ∈ P, x ^ 2 = 1) ∧ (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) ∧
      Nat.card P = Nat.card V := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Vt : Subgroup H := V.comap ψ
  let ρ : ↥Vt →* ↥V := ψ.subgroupComap V
  have hρ : Function.Surjective ρ := ψ.subgroupComap_surjective V hψ
  have hVfin : Finite V := Finite.of_surjective ρ hρ
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV x x.2)⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hindex : ρ.ker.index = Nat.card V := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective ρ hρ, Subgroup.card_top]
  have hodd : ¬ 2 ∣ Nat.card ρ.ker := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ρ.ker) 2 hd
    have hxk : ((x : Vt) : H) ∈ ψ.ker := by
      have := x.2
      rw [MonoidHom.mem_ker] at this ⊢
      exact congrArg Subtype.val this
    have h1 : orderOf (((x : Vt) : H)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have h3 : orderOf (⟨((x : Vt) : H), hxk⟩ : ψ.ker) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact h1
    have h4 := orderOf_dvd_natCard (⟨((x : Vt) : H), hxk⟩ : ψ.ker)
    rw [h3] at h4
    have h5 := Nat.odd_iff.1 hker
    have h6 := Nat.mod_eq_zero_of_dvd h4
    omega
  have hcop : Nat.Coprime (Nat.card ρ.ker) ρ.ker.index := by
    rw [hindex, hn]
    exact Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
  obtain ⟨P₀, hP₀⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hP0card : Nat.card P₀ = Nat.card V := by
    rw [← hindex]
    exact hP₀.symm.index_eq_card.symm
  have hdisj : ∀ y ∈ P₀, y ∈ ρ.ker → y = 1 := fun y hy hyk =>
    Subgroup.disjoint_def.1 hP₀.disjoint hyk hy
  refine ⟨P₀.map Vt.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : y ^ 2 = 1 := by
      apply hdisj (y ^ 2) (P₀.pow_mem hy 2)
      rw [MonoidHom.mem_ker, map_pow]
      exact Subtype.ext (hV _ (ρ y).2)
    simpa using congrArg Subtype.val h1
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have h1 : y * z = z * y := by
      have : y * z * (z * y)⁻¹ = 1 := by
        apply hdisj _ (P₀.mul_mem (P₀.mul_mem hy hz) (P₀.inv_mem (P₀.mul_mem hz hy)))
        have hc : ρ y * ρ z = ρ z * ρ y := Subtype.ext (hVc _ (ρ y).2 _ (ρ z).2)
        rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
      exact mul_inv_eq_one.1 this
    exact congrArg Subtype.val h1
  · rw [Subgroup.card_map_of_injective Vt.subtype_injective, hP0card]

end CFSG.Quasithin.H13.CTK
