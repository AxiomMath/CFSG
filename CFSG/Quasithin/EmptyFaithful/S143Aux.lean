module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.Quasithin.S143

variable {G : Type*} [Group G]

theorem exists_fixed_mem_diff_of_relIndex_two [Finite G] {R N : Subgroup G} (hRN : R ≤ N)
    (h2 : R.relIndex N = 2) {x : G} (hx3 : x ^ 3 = 1)
    (hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hR3 : ¬ 3 ∣ Nat.card R) : ∃ c ∈ N, c ∉ R ∧ x * c * x⁻¹ = c := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxx : x⁻¹ = x * x := by
    have : x * (x * x) = 1 := by simpa [pow_succ, mul_assoc] using hx3
    exact inv_eq_of_mul_eq_one_right this
  have hconj : ∀ y : G, x⁻¹ * y * x = x * (x * y * x⁻¹) * x⁻¹ := by
    intro y
    calc x⁻¹ * y * x = (x * x) * y * (x * x)⁻¹ := by rw [← hxx, inv_inv]
      _ = x * (x * y * x⁻¹) * x⁻¹ := by group
  have hxR' : ∀ r ∈ R, x⁻¹ * r * x ∈ R := fun r hr => by
    rw [hconj]; exact hxR _ (hxR r hr)
  have hxN' : ∀ n ∈ N, x⁻¹ * n * x ∈ N := fun n hn => by
    rw [hconj]; exact hxN _ (hxN n hn)
  let α : Type _ := {y : G // y ∈ N ∧ y ∉ R}
  let σ : Equiv.Perm α :=
    { toFun := fun y => ⟨x * y * x⁻¹, hxN _ y.2.1, fun h => y.2.2 (by
        have := hxR' _ h
        simpa [mul_assoc] using this)⟩
      invFun := fun y => ⟨x⁻¹ * y * x, hxN' _ y.2.1, fun h => y.2.2 (by
        have := hxR _ h
        simpa [mul_assoc] using this)⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  have hf : ∀ (k : ℕ) (y : α), ((σ ^ k : Equiv.Perm α) y : G) = x ^ k * y * (x ^ k)⁻¹ := by
    intro k y
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      show x * ((σ ^ k : Equiv.Perm α) y : G) * x⁻¹ = _
      rw [ih, pow_succ']
      group
  have hσ : σ ^ 3 ^ 1 = 1 := by
    refine Equiv.ext fun y => Subtype.ext ?_
    rw [show (3 : ℕ) ^ 1 = 3 from rfl, hf 3 y, hx3]
    simp
  have hcard : Nat.card α = Nat.card R := by
    set R' : Subgroup N := R.subgroupOf N with hR'
    have hR'card : Nat.card R' = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv
    have hidx : R'.index = 2 := h2
    have hN : Nat.card N = Nat.card R' * 2 := by
      rw [← hidx]; exact (Subgroup.card_mul_index R').symm
    have hsum : Nat.card N = Nat.card {y : N // y ∈ R'} + Nat.card {y : N // y ∉ R'} := by
      rw [← Nat.card_sum]
      exact Nat.card_congr (Equiv.sumCompl (fun y : N => y ∈ R')).symm
    have h1 : Nat.card {y : N // y ∈ R'} = Nat.card R' := rfl
    have h2' : Nat.card α = Nat.card {y : N // y ∉ R'} :=
      Nat.card_congr
        { toFun := fun y => ⟨⟨y.1, y.2.1⟩, fun h => y.2.2 h⟩
          invFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
          left_inv := fun y => rfl
          right_inv := fun y => rfl }
    omega
  have hfix : ∃ y : α, σ y = y := by
    have : Fintype α := Fintype.ofFinite α
    refine Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) ?_ hσ
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hR3
  obtain ⟨y, hy⟩ := hfix
  exact ⟨y.1, y.2.1, y.2.2, congrArg Subtype.val hy⟩

theorem card_sup_mul_card_inf_of_le_normalizer {R U : Subgroup G}
    (hU : U ≤ Subgroup.normalizer (R : Set G)) :
    Nat.card ↥(R ⊔ U) * Nat.card ↥(R ⊓ U) = Nat.card R * Nat.card U := by
  set S : Subgroup G := R ⊔ U with hS
  have hRS : R ≤ S := le_sup_left
  have hUS : U ≤ S := le_sup_right
  have hSN : S ≤ Subgroup.normalizer (R : Set G) := sup_le Subgroup.le_normalizer hU
  set R' : Subgroup S := R.subgroupOf S with hR'
  set U' : Subgroup S := U.subgroupOf S with hU'
  have : R'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRS).2 hSN
  have hrel := Subgroup.relIndex_sup_right U' R'
  have htop : U' ⊔ R' = ⊤ := by
    have h1 : (U ⊔ R).subgroupOf S = U' ⊔ R' := by
      rw [hU', hR']
      exact Subgroup.subgroupOf_sup hUS hRS
    rw [← h1, sup_comm]
    exact Subgroup.subgroupOf_self S
  rw [htop] at hrel
  have hR'card : Nat.card R' = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS).toEquiv
  have hU'card : Nat.card U' = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv
  have hinfcard : Nat.card ↥(R' ⊓ U') = Nat.card ↥(R ⊓ U) := by
    have : R' ⊓ U' = (R ⊓ U).subgroupOf S := by
      ext x
      simp [hR', hU', Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hRS)).toEquiv
  have e1 := Subgroup.relIndex_mul_card R' (⊤ : Subgroup S)
  have e2 := Subgroup.relIndex_mul_card R' U'
  rw [inf_top_eq, Subgroup.card_top] at e1
  rw [hrel] at e1
  rw [hU'card] at e2
  rw [hR'card] at e1
  rw [← e1, ← hinfcard, ← e2]
  ring

theorem exists_involution_mem_diff_sup [Finite G] {R N U : Subgroup G} {x : G} (hRN : R ≤ N)
    (hidx : R.relIndex N = 2) (hx3 : x ^ 3 = 1)
    (hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hfpf : ∀ r ∈ R, x * r * x⁻¹ = r → r = 1) (hR3 : ¬ 3 ∣ Nat.card R)
    (hUR : U ≤ Subgroup.normalizer (R : Set G)) (hNU : N ⊓ U ≤ R) :
    ∃ c ∈ N, c ∉ R ⊔ U ∧ orderOf c = 2 := by
  obtain ⟨c, hcN, hcR, hcx⟩ := exists_fixed_mem_diff_of_relIndex_two hRN hidx hx3 hxR hxN hR3
  have hN2 : (R.subgroupOf N).index = 2 := hidx
  have hc2R : c * c ∈ R := by
    have := Subgroup.sq_mem_of_index_two hN2 ⟨c, hcN⟩
    simpa [pow_two, Subgroup.mem_subgroupOf] using this
  have hc2x : x * (c * c) * x⁻¹ = c * c := by
    calc x * (c * c) * x⁻¹ = (x * c * x⁻¹) * (x * c * x⁻¹) := by group
      _ = c * c := by rw [hcx]
  have hc2 : c * c = 1 := hfpf _ hc2R hc2x
  have hc1 : c ≠ 1 := fun h => hcR (h ▸ R.one_mem)
  refine ⟨c, hcN, fun hc => ?_, orderOf_eq_prime_iff.mpr ⟨by rw [pow_two]; exact hc2, hc1⟩⟩
  have hc' : c ∈ ((U ⊔ R : Subgroup G) : Set G) := by rw [sup_comm]; exact hc
  rw [Subgroup.coe_mul_of_left_le_normalizer_right U R hUR] at hc'
  obtain ⟨u, hu, r, hr, rfl⟩ := hc'
  have huN : u ∈ N := by
    have : u = (u * r) * r⁻¹ := by group
    rw [this]
    exact N.mul_mem hcN (N.inv_mem (hRN hr))
  exact hcR (R.mul_mem (hNU ⟨huN, hu⟩) hr)

end CFSG.Quasithin.S143
