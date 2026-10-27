module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModRefl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut2
public import CFSG.Quasithin.EmptyFaithful.S151bW3Five

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

theorem dih5_commute_r :
    ∀ d : DihedralGroup 5, d * DihedralGroup.r 1 = DihedralGroup.r 1 * d →
      ∃ k : ZMod 5, d = DihedralGroup.r k := by
  decide

omit [Finite W] in
theorem mem_A₂_of_mem_sup_of_fix {y : MulAut W} (hy : y ∈ S.A₁ ⊔ S.A₂)
    (hfix : ∀ w ∈ S.W₁, y w = w) : y ∈ S.A₂ := by
  rw [← S.range_ι] at hy
  obtain ⟨w, rfl⟩ := hy
  rw [ι_apply] at hfix ⊢
  have hP : S.ι₁ w.1 = 1 := by
    apply S.eq_one_of_fix_W₁_W₂
    · intro u hu
      have h := hfix u hu
      rwa [MulAut.mul_apply, S.fix_W₁_of_mem_A₂ (S.ι₂_mem w.2) hu] at h
    · intro u hu
      exact (six_module151b S.comm S.winf).2.2.1 _ (S.ι₁_mem w.1) u hu
  rw [hP, one_mul]
  exact S.ι₂_mem w.2

omit [Finite W] in
theorem exists_pow_a₂_of_commute {d : MulAut W} (hd : d ∈ S.A₂) (hc : d * S.a₂ = S.a₂ * d) :
    ∃ k : ℕ, d = S.a₂ ^ k := by
  obtain ⟨u, rfl⟩ := S.exists_ι₂ hd
  have h : u * DihedralGroup.r 1 = DihedralGroup.r 1 * u := by
    apply S.ι₂_injective
    rw [map_mul, map_mul, ← S.a₂_eq_ι₂]
    exact hc
  obtain ⟨k, rfl⟩ := dih5_commute_r u h
  exact ⟨k.val, S.ι₂_r (Or.inr rfl) k⟩

omit [Finite W] in
theorem commute_of_conj_mem_A₂ {ε x : MulAut W} (hε3 : orderOf ε = 3) (hεa : ε * S.a₂ = S.a₂ * ε)
    (hx : x ∈ S.A₂) (hx2 : orderOf x = 2) (hy : ε * x * ε⁻¹ ∈ S.A₂) : ε * x = x * ε := by
  set y : MulAut W := ε * x * ε⁻¹ with hy_def
  have hxsq : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2] at this
  have hy1 : y ≠ 1 := by
    intro h
    have hx1 : x = 1 := by
      calc x = ε⁻¹ * y * ε := by rw [hy_def]; group
        _ = 1 := by rw [h]; group
    rw [hx1, orderOf_one] at hx2
    omega
  have hysq : y ^ 2 = 1 := by rw [hy_def, conj_pow, hxsq]; group
  have hy2 : orderOf y = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hysq hy1
  have hxinv := S.reflection_inv_a₂ hx hx2
  have hyinv := S.reflection_inv_a₂ hy hy2
  have hxinv' : x⁻¹ * S.a₂ * x = S.a₂⁻¹ := by
    have h1 : x⁻¹ * S.a₂⁻¹ * x = S.a₂ := by
      calc x⁻¹ * S.a₂⁻¹ * x = x⁻¹ * (x * S.a₂ * x⁻¹) * x := by rw [hxinv]
        _ = S.a₂ := by group
    calc x⁻¹ * S.a₂ * x = (x⁻¹ * S.a₂⁻¹ * x)⁻¹ := by group
      _ = S.a₂⁻¹ := by rw [h1]
  have hdA : y * x⁻¹ ∈ S.A₂ := S.A₂.mul_mem hy (S.A₂.inv_mem hx)
  have hdc : (y * x⁻¹) * S.a₂ = S.a₂ * (y * x⁻¹) := by
    have h : y * x⁻¹ * S.a₂ * (y * x⁻¹)⁻¹ = S.a₂ := by
      calc y * x⁻¹ * S.a₂ * (y * x⁻¹)⁻¹ = y * (x⁻¹ * S.a₂ * x) * y⁻¹ := by group
        _ = y * S.a₂⁻¹ * y⁻¹ := by rw [hxinv']
        _ = (y * S.a₂ * y⁻¹)⁻¹ := by group
        _ = S.a₂ := by rw [hyinv, inv_inv]
    exact mul_inv_eq_iff_eq_mul.mp h
  obtain ⟨k, hk⟩ := S.exists_pow_a₂_of_commute hdA hdc
  have hyk : y = S.a₂ ^ k * x := by
    calc y = (y * x⁻¹) * x := by group
      _ = S.a₂ ^ k * x := by rw [hk]
  have hεa' : ε * S.a₂ * ε⁻¹ = S.a₂ := by rw [hεa]; group
  have hconj : ε * S.a₂ ^ k * ε⁻¹ = S.a₂ ^ k := by rw [← conj_pow, hεa']
  have h1 : ε * y * ε⁻¹ = S.a₂ ^ k * y := by
    calc ε * y * ε⁻¹ = ε * (S.a₂ ^ k * x) * ε⁻¹ := by rw [← hyk]
      _ = (ε * S.a₂ ^ k * ε⁻¹) * (ε * x * ε⁻¹) := by group
      _ = S.a₂ ^ k * y := by rw [hconj]
  have hε3' : ε * (ε * ε) = 1 := by
    have := pow_orderOf_eq_one ε
    rwa [hε3, pow_three] at this
  have h3 : x = S.a₂ ^ k * (S.a₂ ^ k * (S.a₂ ^ k * x)) := by
    calc x = (ε * (ε * ε)) * x * (ε * (ε * ε))⁻¹ := by rw [hε3']; group
      _ = ε * (ε * y * ε⁻¹) * ε⁻¹ := by rw [hy_def]; group
      _ = ε * (S.a₂ ^ k * y) * ε⁻¹ := by rw [h1]
      _ = (ε * S.a₂ ^ k * ε⁻¹) * (ε * y * ε⁻¹) := by group
      _ = S.a₂ ^ k * (S.a₂ ^ k * y) := by rw [hconj, h1]
      _ = S.a₂ ^ k * (S.a₂ ^ k * (S.a₂ ^ k * x)) := by rw [hyk]
  have h4 : S.a₂ ^ (3 * k) = 1 := by
    have h5 : S.a₂ ^ (3 * k) * x = 1 * x := by
      calc S.a₂ ^ (3 * k) * x = S.a₂ ^ k * (S.a₂ ^ k * (S.a₂ ^ k * x)) := by
            rw [mul_comm 3 k, pow_mul, pow_three]; simp only [mul_assoc]
        _ = 1 * x := by rw [one_mul]; exact h3.symm
    exact mul_right_cancel h5
  have h6 : 5 ∣ 3 * k := by
    have := orderOf_dvd_of_pow_eq_one h4
    rwa [S.orderOf_a₂_five] at this
  have h7 : 5 ∣ k := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h6)
  have h8 : S.a₂ ^ k = 1 := by
    obtain ⟨m, hm⟩ := h7
    rw [hm, pow_mul, show S.a₂ ^ 5 = 1 from S.a₂_pow (Or.inr rfl), one_pow]
  have hy_eq : y = x := by rw [hyk, h8, one_mul]
  have : ε * x * ε⁻¹ = x := hy_eq
  exact mul_inv_eq_iff_eq_mul.mp this

set_option linter.unusedSectionVars false in
theorem reflection_commute_eps (_hW : ∀ w : W, w ^ 2 = 1) (_hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (_hτ : S.τ ∈ Mb)
    (_hA : S.A₁ ⊔ S.A₂ ≤ Mb) {ε x : MulAut W} (hε : ε ∈ Mb) (hε3 : orderOf ε = 3)
    (hε₁ : ∀ w ∈ S.W₁, ε w = w) (hεa : ε * S.a₂ = S.a₂ * ε)
    (_hεf : ∀ w ∈ S.W₂, w ≠ 1 → ε w ≠ w)
    (hx : x ∈ S.A₂) (hx2 : orderOf x = 2) : ε * x = x * ε := by
  refine S.commute_of_conj_mem_A₂ hε3 hεa hx hx2 ?_
  refine S.mem_A₂_of_mem_sup_of_fix (hnorm ε hε x (Subgroup.mem_sup_right hx)) ?_
  intro w hw
  have h1 : ε⁻¹ w = w := by
    calc ε⁻¹ w = ε⁻¹ (ε w) := by rw [hε₁ w hw]
      _ = w := MulAut.inv_apply_self W ε w
  show ε (x (ε⁻¹ w)) = w
  rw [h1, S.fix_W₁_of_mem_A₂ hx hw, hε₁ w hw]

theorem reflection_commute_eps₁ (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (hτ : S.τ ∈ Mb)
    (hA : S.A₁ ⊔ S.A₂ ≤ Mb) {ε x : MulAut W} (hε : ε ∈ Mb) (hε3 : orderOf ε = 3)
    (hε₂ : ∀ w ∈ S.W₂, ε w = w) (hεa : ε * S.a₁ = S.a₁ * ε)
    (hεf : ∀ w ∈ S.W₁, w ≠ 1 → ε w ≠ w)
    (hx : x ∈ S.A₁) (hx2 : orderOf x = 2) : ε * x = x * ε := by
  have hnorm' : ∀ g ∈ Mb, ∀ z ∈ S.swap.A₁ ⊔ S.swap.A₂,
      g * z * g⁻¹ ∈ S.swap.A₁ ⊔ S.swap.A₂ := by
    intro g hg z hz
    have hz' : z ∈ S.A₁ ⊔ S.A₂ := by
      rwa [show S.swap.A₁ ⊔ S.swap.A₂ = S.A₂ ⊔ S.A₁ from rfl, sup_comm] at hz
    have := hnorm g hg z hz'
    rwa [show S.swap.A₁ ⊔ S.swap.A₂ = S.A₂ ⊔ S.A₁ from rfl, sup_comm]
  have hA' : S.swap.A₁ ⊔ S.swap.A₂ ≤ Mb := by
    rw [show S.swap.A₁ ⊔ S.swap.A₂ = S.A₂ ⊔ S.A₁ from rfl, sup_comm]
    exact hA
  exact S.swap.reflection_commute_eps hW hcard hnorm' hτ hA' hε hε3 hε₂
    (by rw [swap_a₂]; exact hεa) hεf hx hx2

end CFSG.Quasithin.SixData151b
