module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Centralizer
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Iso
import CFSG.LocalAnalysis.StandardType.GGOrthRk1Theta
import CFSG.LocalAnalysis.StandardType.GGOrthFrameModel
import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockGTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

open Module Multiplicative

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open SpCoord

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem TBJOmData.card_rankOne_of_card_two {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ}
    (Δ : TBJOmData Q p A r) (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (hK : Nat.card K = 2) {i j : Fin r} (hij : i ≠ j) :
    Nat.card ↥(Δ.rankOne i j) = 6 := by
  classical
  obtain ⟨φ, hφinj, hφrange, hφQ, hφτ⟩ := Δ.exists_rk1_isometry hp2 hAΩ i j hij
  obtain ⟨θ, -, -, hθinj, -, -, hθuniq⟩ :=
    Δ.exists_rk1_theta hfix i j hij φ hφinj hφrange hφQ hφτ
  have hle : Δ.rankOne i j ≤ θ.range :=
    Δ.rankOne_le_range hp2 hfix i j φ hφinj hφrange hφQ hφτ θ hθuniq
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 6 := by
    have : Fintype K := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 := by rwa [Nat.card_eq_fintype_card] at hK
    rw [Matrix.card_SL_field (𝔽 := K) 2, hK', Fin.prod_univ_two]
    norm_num
  have hrange : Nat.card ↥θ.range = 6 :=
    (Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv).symm.trans hSL
  have hdvd : Nat.card ↥(Δ.rankOne i j) ∣ 6 := hrange ▸ Subgroup.card_dvd_of_le hle
  have hC : ∀ x : V ≃ₗ[K] V,
      (∀ f, x * Δ.τ f * x⁻¹ = Δ.τ (permAut (Equiv.swap i j) f)) →
      x ∈ Subgroup.centralizer (Δ.reflFixed i j : Set (V ≃ₗ[K] V)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact ((Δ.mem_reflFixed_iff hx t).mp ht).2.symm
  have hmem : ∀ (x : V ≃ₗ[K] V) (e : ℕ), x ∈ orthDerived Q → x ^ (2 ^ e) = 1 →
      (∀ f, x * Δ.τ f * x⁻¹ = Δ.τ (permAut (Equiv.swap i j) f)) → x ∈ Δ.rankOne i j := by
    intro x e hxΩ hx2 hx
    rw [TBJOmData.rankOne, ggOTwoPrime]
    exact Subgroup.subset_closure ⟨⟨hC x hx, hxΩ⟩, e, hx2⟩
  let f₀ : Fin r → Multiplicative (ZMod p) := Pi.mulSingle i (ofAdd (1 : ZMod p))
  have hf₀ : permAut (Equiv.swap i j) f₀ ≠ f₀ := by
    intro h
    have h' := congrFun h i
    rw [permAut_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_left] at h'
    have hj : f₀ j = 1 := Pi.mulSingle_eq_of_ne hij.symm _
    have hi : f₀ i = ofAdd (1 : ZMod p) := Pi.mulSingle_eq_same _ _
    rw [hj, hi] at h'
    exact one_ne_zero (ofAdd_eq_one.mp h'.symm)
  have hτne : ∀ x : V ≃ₗ[K] V,
      (∀ f, x * Δ.τ f * x⁻¹ = Δ.τ (permAut (Equiv.swap i j) f)) →
      x * Δ.τ f₀ ≠ Δ.τ f₀ * x := by
    intro x hx hcomm
    apply hf₀
    apply Δ.τ_inj
    rw [← hx f₀, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) DFunLike.coe_injective
  obtain ⟨w, hwΩ, -, hw⟩ := Δ.swapMove i j hij
  obtain ⟨N, hN, e, he⟩ := exists_odd_pow_pow_two_eq_one w
  have hw₂ : ∀ f, w ^ N * Δ.τ f * (w ^ N)⁻¹ = Δ.τ (permAut (Equiv.swap i j) f) :=
    pow_odd_conj_eq Δ.τ hw (permAut_swap_swap i j) hN
  have hw₂R : w ^ N ∈ Δ.rankOne i j := hmem _ e ((orthDerived Q).pow_mem hwΩ N) he hw₂
  have hw₂1 : w ^ N ≠ 1 := fun h => hτne _ hw₂ (by rw [h, one_mul, mul_one])
  have hτcomm : ∀ f g, Δ.τ f * Δ.τ g = Δ.τ g * Δ.τ f := fun f g => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hτA : Δ.τ f₀ ∈ A := Δ.τ_range.le ⟨f₀, rfl⟩
  set w₃ := Δ.τ f₀ * w ^ N * (Δ.τ f₀)⁻¹ with hw₃def
  have hw₃ : ∀ f, w₃ * Δ.τ f * w₃⁻¹ = Δ.τ (permAut (Equiv.swap i j) f) := by
    intro f
    have h1 : (Δ.τ f₀)⁻¹ * Δ.τ f * Δ.τ f₀ = Δ.τ f := by
      rw [mul_assoc, hτcomm f f₀, ← mul_assoc, inv_mul_cancel, one_mul]
    calc w₃ * Δ.τ f * w₃⁻¹
        = Δ.τ f₀ * (w ^ N * ((Δ.τ f₀)⁻¹ * Δ.τ f * Δ.τ f₀) * (w ^ N)⁻¹) * (Δ.τ f₀)⁻¹ := by
          rw [hw₃def]; group
      _ = Δ.τ f₀ * Δ.τ (permAut (Equiv.swap i j) f) * (Δ.τ f₀)⁻¹ := by rw [h1, hw₂ f]
      _ = Δ.τ (permAut (Equiv.swap i j) f) := by
          rw [hτcomm f₀, mul_assoc, mul_inv_cancel, mul_one]
  have hw₃Ω : w₃ ∈ orthDerived Q :=
    (orthDerived Q).mul_mem ((orthDerived Q).mul_mem (hAΩ hτA)
      ((orthDerived Q).pow_mem hwΩ N)) ((orthDerived Q).inv_mem (hAΩ hτA))
  have hw₃2 : w₃ ^ (2 ^ e) = 1 := by
    rw [hw₃def, conj_pow, he, mul_one, mul_inv_cancel]
  have hw₃R : w₃ ∈ Δ.rankOne i j := hmem _ e hw₃Ω hw₃2 hw₃
  have hw₃1 : w₃ ≠ 1 := fun h => hτne _ hw₃ (by rw [h, one_mul, mul_one])
  have hw₃₂ : w₃ ≠ w ^ N := fun h =>
    hτne _ hw₂ (mul_inv_eq_iff_eq_mul.mp (hw₃def ▸ h)).symm
  have hne2 : Nat.card ↥(Δ.rankOne i j) ≠ 2 := by
    intro h2
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(Δ.rankOne i j))).mp h2
    have h2' : (⟨w ^ N, hw₂R⟩ : ↥(Δ.rankOne i j)) = y :=
      huniq _ fun h => hw₂1 (congrArg Subtype.val h)
    have h3' : (⟨w₃, hw₃R⟩ : ↥(Δ.rankOne i j)) = y :=
      huniq _ fun h => hw₃1 (congrArg Subtype.val h)
    exact hw₃₂ (congrArg Subtype.val (h3'.trans h2'.symm))
  have heven : 2 ∣ Nat.card ↥(Δ.rankOne i j) := by
    have hord : orderOf (⟨w ^ N, hw₂R⟩ : ↥(Δ.rankOne i j)) ∣ 2 ^ e := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using he)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hm
      exact hw₂1 (congrArg Subtype.val hm)
    calc 2 ∣ 2 ^ m := dvd_pow_self 2 hm0
      _ = orderOf (⟨w ^ N, hw₂R⟩ : ↥(Δ.rankOne i j)) := hm.symm
      _ ∣ Nat.card ↥(Δ.rankOne i j) := orderOf_dvd_natCard _
  have hle6 : Nat.card ↥(Δ.rankOne i j) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨n, hn⟩ : ∃ n, Nat.card ↥(Δ.rankOne i j) = n := ⟨_, rfl⟩
  rw [hn] at hdvd heven hne2 hle6 ⊢
  interval_cases n <;> omega

end OrthTorus

end CFSG.StandardType

end
