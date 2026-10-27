module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.GH74.GLS.IVK.Statements.Sec1

public section

namespace CFSG.Quasithin.Ch3E213M.OS

open CFSG.Open CFSG.GH74.GLS.IVK CFSG.GH74.GLS CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem card_fixed_of_fieldAut (h14a : IVK_1_4a) (hF : L2Field F) (e : K ≃* L2 F) {p : ℕ}
    (hq : Nat.card F = p ^ 2) {f₀ : MulAut K} (hf₀ : f₀ ∈ fieldAutSub e) (hf₀2 : orderOf f₀ = 2) :
    Nat.card (fixedSubgroup K f₀) = p * (Nat.card F - 1) := by
  obtain ⟨σ, rfl⟩ := hf₀
  have hσ : orderOf σ = 2 := by
    rw [← hf₀2]
    exact (orderOf_injective _ (fieldAutHom_injective e) σ).symm
  obtain ⟨F₀, _, _, hF₀, ⟨φ⟩⟩ := (h14a F hF K e σ).2.2 (by rw [hσ]; exact even_two)
  rw [hσ, hq] at hF₀
  have hp : Nat.card F₀ = p := Nat.pow_left_injective (by norm_num) hF₀
  rw [Nat.card_congr φ.toEquiv, pgl2_card_formula, hp, hq]

omit [Finite K] in
theorem eq_of_le_fixed {z₀ : K} (hcoat : IsCoatom (Subgroup.centralizer ({z₀} : Set K)))
    {u : MulAut K} (hu : u ≠ 1) (hle : Subgroup.centralizer ({z₀} : Set K) ≤ fixedSubgroup K u) :
    fixedSubgroup K u = Subgroup.centralizer ({z₀} : Set K) := by
  rcases hcoat.le_iff.mp hle with h | h
  · exfalso
    apply hu
    ext x
    have : x ∈ fixedSubgroup K u := h ▸ Subgroup.mem_top x
    exact this
  · exact h

omit [Finite K] in
theorem le_fixed {C S : Subgroup K} {u : MulAut K} {b m : ℕ} {c : K} (hSC : S ≤ C)
    (hSodd : Odd S.index) (hcC : c ∈ C) (hcm : orderOf c = m) (hC : Nat.card C = 2 ^ b * m)
    (hm : 0 < m) (hS : ∀ x ∈ S, u x = x) (hc : u c = c) : C ≤ fixedSubgroup K u := by
  have hfin : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; positivity)
  set Y := C ⊓ fixedSubgroup K u with hY
  have hSY : S ≤ Y := fun x hx => ⟨hSC hx, hS x hx⟩
  have hcY : Subgroup.zpowers c ≤ Y := (Subgroup.zpowers_le).mpr ⟨hcC, hc⟩
  have h1 : Y.relIndex C ∣ S.index :=
    (Subgroup.relIndex_dvd_of_le_left C hSY).trans (Subgroup.relIndex_dvd_index_of_le hSC)
  have hzC : Subgroup.zpowers c ≤ C := (Subgroup.zpowers_le).mpr hcC
  have h2 : (Subgroup.zpowers c).relIndex C = 2 ^ b := by
    have h := Subgroup.card_mul_index ((Subgroup.zpowers c).subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzC).toEquiv, Nat.card_zpowers, hcm, hC,
      mul_comm (2 ^ b)] at h
    exact Nat.eq_of_mul_eq_mul_left hm h
  have h3 : Y.relIndex C ∣ 2 ^ b := h2 ▸ Subgroup.relIndex_dvd_of_le_left C hcY
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  have hj0 : j = 0 := by
    by_contra hj0
    have hodd := Odd.of_dvd_nat hSodd h1
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hj0⟩)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact hj.trans inf_le_right

end CFSG.Quasithin.Ch3E213M.OS
