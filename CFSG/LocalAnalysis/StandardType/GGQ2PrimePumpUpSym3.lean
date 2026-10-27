module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimePumpUpAut
import CFSG.LieType.SeitzGeneration.QuasiHighLift

public section

namespace CFSG.GGQ2Prime

open Subgroup
open CFSG.LieType.SeitzGeneration.QuasiHigh (apply_commutatorElement_of_fixed quotAut_mk)
open scoped commutatorElement

theorem PumpUpAut.false_of_sym3_lift {K : Type} [Group K] {W Wk : Subgroup K}
    {ζ ξ : MulAut K} {Q A : Subgroup (MulAut K)} (h : PumpUpAut W Wk ζ ξ Q A)
    {β : MulAut (K ⧸ center K)}
    (hβ : ∀ k, QuotientGroup.mk' (center K) (ζ k) = β (QuotientGroup.mk' (center K) k))
    {t m : K ⧸ center K} (ht : β t = t) (hm : β m = m)
    (hmW : ∀ w ∈ W, Commute m (QuotientGroup.mk' (center K) w))
    (hm3 : m ^ 3 = 1) (hm1 : m ≠ 1) (htm : t * m * t⁻¹ = m⁻¹) : False := by
  classical
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (center K) t
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (center K) m
  have hgζ : ζ ⁅a, b⁆ = ⁅a, b⁆ :=
    apply_commutatorElement_of_fixed (by rw [quotAut_mk]; exact (hβ a).trans ht)
      (by rw [quotAut_mk]; exact (hβ b).trans hm)
  set π : K →* K ⧸ center K := QuotientGroup.mk' (center K) with hπ
  have hker : π.ker ≤ center K := by rw [hπ, QuotientGroup.ker_mk']
  have hWp : ⁅W, W⁆ = W := by
    rw [← Subgroup.map_subtype_commutator, h.W_comp.2.2.1, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  set g := ⁅a, b⁆ with hg
  have hπg : π g = π b := by
    rw [hg, map_commutatorElement, commutatorElement_def, htm]
    calc (π b)⁻¹ * (π b)⁻¹ = (π b)⁻¹ * (π b)⁻¹ * π b ^ 3 := by rw [hm3, mul_one]
      _ = π b := by group
  have hgW : ∀ w ∈ W, Commute g w :=
    CFSG.ClassicalInvolution.RouteD.TwinSmall.commute_of_perfect_of_map_commute π hker hWp
      fun w hw => by rw [hπg]; exact hmW w hw
  have hg3 : g ^ 3 = 1 := by
    obtain ⟨z, hz, hzab⟩ : ∃ z ∈ center K, a * b * a⁻¹ = b⁻¹ * z := by
      refine ⟨b * (a * b * a⁻¹), hker ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, htm, mul_inv_cancel]
    have hb3 : b ^ 3 ∈ center K := hker (by rw [MonoidHom.mem_ker, map_pow]; exact hm3)
    have hzb : Commute z b := (Subgroup.mem_center_iff.1 hz b).symm
    have e1 : (b⁻¹ * z) ^ 3 = b ^ 3 := by
      rw [← hzab, conj_pow, Subgroup.mem_center_iff.1 hb3 a, mul_inv_cancel_right]
    rw [hzb.symm.inv_left.mul_pow] at e1
    have hz3 : z ^ 3 = b ^ 3 * b ^ 3 := by
      calc z ^ 3 = (b⁻¹ ^ 3)⁻¹ * (b⁻¹ ^ 3 * z ^ 3) := by group
        _ = b ^ 3 * b ^ 3 := by rw [e1]; group
    have hgz : g = z * b⁻¹ ^ 2 := by
      rw [hg, commutatorElement_def, hzab, hzb.symm.inv_left.eq]
      group
    rw [hgz, (hzb.inv_right.pow_right 2).mul_pow, hz3]
    group
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 (fun h1 => hm1 (by rw [← hπg, h1, map_one]))
  have hζfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, h.ζ_cube⟩
  have hpow : ∀ (n : ℕ) (x : K), ζ x = x → (ζ ^ n) x = x := by
    intro n x hx
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hx, ih]
  have hfix : ∀ α ∈ A, α g = g := by
    intro α hα
    obtain ⟨w, hw, γ, hγ, rfl⟩ := h.A_gen α hα
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hζfin.mem_powers_iff_mem_zpowers.2 hγ)
    rw [MulAut.mul_apply, hpow n g hgζ, MulAut.conj_apply, ← (hgW w hw).eq, mul_inv_cancel_right]
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 (hζfin.mem_powers_iff_mem_zpowers.2
    (h.A_fixW _ (h.selfcent g hord hfix) fun w hw => by
      rw [MulAut.conj_apply, (hgW w hw).eq, mul_inv_cancel_right]))
  have hpowπ : ∀ (n : ℕ) (x : K), β (π x) = π x → π ((ζ ^ n) x) = π x := by
    intro n
    induction n with
    | zero => intro x _; rfl
    | succ n ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, ih (ζ x) (by rw [hβ x, hx, hx]), hβ x, hx]
  have hc : π b * π a * (π b)⁻¹ = π a := by
    have := hpowπ n a ht
    rwa [hn, MulAut.conj_apply, map_mul, map_mul, map_inv, hπg] at this
  have e1 : π b * π a = π a * π b := by
    calc π b * π a = π b * π a * (π b)⁻¹ * π b := by group
      _ = π a * π b := by rw [hc]
  have e2 : π a * π b = (π b)⁻¹ * π a := by
    calc π a * π b = π a * π b * (π a)⁻¹ * π a := by group
      _ = (π b)⁻¹ * π a := by rw [htm]
  have e3 : π b = (π b)⁻¹ := mul_right_cancel (e1.trans e2)
  have h2 : π b * π b = 1 := by
    calc π b * π b = π b * (π b)⁻¹ := by rw [← e3]
      _ = 1 := mul_inv_cancel _
  apply hm1
  calc π b = π b ^ 3 * (π b * π b)⁻¹ := by group
    _ = 1 := by rw [hm3, h2]; group

end CFSG.GGQ2Prime
