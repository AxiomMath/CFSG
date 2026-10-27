module

public import CFSG.Quasithin.EmptyFaithful.S153F19

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

theorem szN3_exists_mul_inv_apply_eq {W : Type*} [CommGroup W] [Finite W] {U : Subgroup W}
    {x : MulAut W} (hst : ∀ u ∈ U, x u ∈ U) (hfix : ∀ u ∈ U, x u = u → u = 1) :
    ∀ u₀ ∈ U, ∃ u ∈ U, u * (x u)⁻¹ = u₀ := by
  classical
  let f : U → U := fun u => ⟨(u : W) * (x u)⁻¹, U.mul_mem u.2 (U.inv_mem (hst u u.2))⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : (a : W) * (x a)⁻¹ = (b : W) * (x b)⁻¹ := congrArg Subtype.val hab
    have h1' : (a : W) / x a = (b : W) / x b := by simpa [div_eq_mul_inv] using h1
    have h2 : (a : W) * x b = (b : W) * x a := div_eq_div_iff_mul_eq_mul.mp h1'
    have h3 : x (a : W) / x (b : W) = (a : W) / (b : W) := by
      rw [div_eq_div_iff_mul_eq_mul]
      calc x (a : W) * (b : W) = (b : W) * x (a : W) := mul_comm _ _
        _ = (a : W) * x (b : W) := h2.symm
    have h4 : x ((a : W) / (b : W)) = (a : W) / (b : W) := by rw [map_div]; exact h3
    have h5 : (a : W) / (b : W) = 1 := hfix _ (U.div_mem a.2 b.2) h4
    exact Subtype.ext (div_eq_one.mp h5)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro u₀ hu₀
  obtain ⟨u, hu⟩ := hsurj ⟨u₀, hu₀⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

theorem v2CommutatorYp_holds (h113 : StageLemma14113) : V2CommutatorYp := by
  intro G _ _ T Mc M V₁ V₂ Yp t hh
  have hhyp : Hyp153 G T Mc M := hh.hyp
  have hYpY : Yp ≤ Y153 Mc M := by
    rcases hh.cases with hY | ⟨-, hY⟩
    · exact hY.le
    · rw [hY]
      exact (oTwoUpper_le _).trans inf_le_left
  obtain ⟨-, hY₂⟩ := hhyp.Y153_le_normalizer_V h113 hh.decomp
  apply le_antisymm
  ·
    rw [Subgroup.commutator_le]
    intro v hv y hy
    have hyN : y ∈ Subgroup.normalizer (V₂ : Set G) := hY₂ (hYpY hy)
    have h1 : y * v⁻¹ * y⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hyN _).mp (inv_mem hv)
    have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V₂.mul_mem hv h1
  ·
    obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -, -⟩ := hh.decomp.model
    obtain ⟨x, hxL, hx3, hx1⟩ := exists_orderThree hS.nat₂
    have hxord : orderOf x = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hx3 hx1
    have hxM : x ∈ autI hV M := hS.L₂_le hxL
    have hxO : x ∈ oTwoUpper (autI hV M) :=
      mem_oTwoUpper_of_odd hxM (by rw [hxord]; decide)
    have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := hhyp.autOn_Y153 h113
    have hxY : x ∈ autI hV (Y153 Mc M) := by rw [e]; exact hxO
    obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hxY
    have hgC : (g : G) ∈ Subgroup.centralizer
        (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := by
      refine (mem_centralizer_map_inclMod_iff hV g.2 (commV L₁)).2 fun u hu => ?_
      have hgx : convI hV ⟨(g : G), g.2⟩ = x := hg
      rw [hgx]
      exact hS.L₂_fix₁ hxL hu
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (g : G) ^ 2 ^ k ∈ Yp := by
      rcases hh.cases with hY | ⟨-, hY⟩
      · exact ⟨0, by simpa [hY] using hgY⟩
      · rw [hY]
        exact exists_pow_mem_oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer
          (((commV L₁).map (inclMod hV) : Subgroup G) : Set G)) ⟨hgY, hgC⟩
    have hx'L : x ^ 2 ^ k ∈ L₂ := L₂.pow_mem hxL _
    have hx'3 : (x ^ 2 ^ k) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
    have hx'1 : x ^ 2 ^ k ≠ 1 := by
      intro h1
      have hdvd : 3 ∣ 2 ^ k := hxord ▸ orderOf_dvd_of_pow_eq_one h1
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      omega
    have hx'ord : orderOf (x ^ 2 ^ k) = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hx'3 hx'1
    have hst : ∀ l ∈ L₂, ∀ u ∈ commV L₂, l u ∈ commV L₂ :=
      fun l hl u hu => commV_stable L₂ hl hu
    have hfix : ∀ u ∈ commV L₂, (x ^ 2 ^ k) u = u → u = 1 := by
      intro u hu hxu
      by_contra hu1
      exact hx'1 (eq_one_of_odd_of_fixed hS.nat₂ hst hx'L (by rw [hx'ord]; decide) hu hu1 hxu)
    have hconv : convI hV (g ^ 2 ^ k) = x ^ 2 ^ k := by rw [map_pow, hg]
    intro v hv
    obtain ⟨u₀, hu₀, rfl⟩ := hv
    obtain ⟨u, hu, hu0⟩ := szN3_exists_mul_inv_apply_eq (hst _ hx'L) hfix u₀ hu₀
    have h2 : ((x ^ 2 ^ k) u).val = (g : G) ^ 2 ^ k * u.val * ((g : G) ^ 2 ^ k)⁻¹ := by
      rw [← hconv, convI_apply_val]
      simp
    have hcomm : ⁅u.val, (g : G) ^ 2 ^ k⁆ = inclMod hV u₀ := by
      rw [← hu0, map_mul, map_inv, inclMod_apply, inclMod_apply, h2, commutatorElement_def]
      group
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator ⟨u, hu, rfl⟩ hk

end CFSG.Quasithin
