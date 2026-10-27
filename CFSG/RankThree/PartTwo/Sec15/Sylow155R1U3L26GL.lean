module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem not_sq_thirteen_dvd_card_GL {d : ℕ} (hd : d ≤ 7) :
    ¬ 13 ^ 2 ∣ Nat.card (GL (Fin d) (ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h := Matrix.card_GL_field (𝔽 := ZMod 5) d
  rw [ZMod.card] at h
  rw [h]
  interval_cases d <;> decide

private theorem card_units_end_eq_card_GL (V : Type*) [AddCommGroup V] [Module (ZMod 5) V]
    [Module.Finite (ZMod 5) V] :
    Nat.card (Module.End (ZMod 5) V)ˣ =
      Nat.card (GL (Fin (Module.finrank (ZMod 5) V)) (ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact Nat.card_congr
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis (ZMod 5) V)).toMulEquiv).toEquiv

theorem not_sq_thirteen_dvd_card_quotient_ker {X : Type*} [Group X] [Finite X] {V : Type*}
    [AddCommGroup V] [Module (ZMod 5) V] [Module.Finite (ZMod 5) V]
    (hdim : Module.finrank (ZMod 5) V ≤ 7) (σ : X →* (V →ₗ[ZMod 5] V)) :
    ¬ 13 ^ 2 ∣ Nat.card (X ⧸ σ.ker) := by
  intro h
  have hker : σ.toHomUnits.ker = σ.ker := by
    ext y
    simp [MonoidHom.mem_ker]
  have hdvd : Nat.card (X ⧸ σ.ker) ∣ Nat.card (Module.End (ZMod 5) V)ˣ := by
    rw [← hker, ← Subgroup.index_eq_card, Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  rw [card_units_end_eq_card_GL] at hdvd
  exact not_sq_thirteen_dvd_card_GL hdim (h.trans hdvd)

private theorem exists_conj_mem_zpowers_of_orderOf_eq_prime {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [hp : Fact p.Prime] (hQ : ¬ p ^ 2 ∣ Nat.card Q) {a b : Q} (ha : orderOf a = p)
    (hb : orderOf b = p) : ∃ n : Q, n * b * n⁻¹ ∈ Subgroup.zpowers a := by
  have hne : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card Q).factorization p = 1 := by
    have h1 : 1 ≤ (Nat.card Q).factorization p := by
      rw [← hp.out.pow_dvd_iff_le_factorization hne, pow_one, ← ha]
      exact orderOf_dvd_natCard a
    have h2 : ¬ 2 ≤ (Nat.card Q).factorization p := by
      rw [← hp.out.pow_dvd_iff_le_factorization hne]
      exact hQ
    omega
  have hA : Nat.card (Subgroup.zpowers a) = p ^ (Nat.card Q).factorization p := by
    rw [Nat.card_zpowers, ha, hfac, pow_one]
  have hB : Nat.card (Subgroup.zpowers b) = p ^ (Nat.card Q).factorization p := by
    rw [Nat.card_zpowers, hb, hfac, pow_one]
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq Q (Sylow.ofCard (Subgroup.zpowers b) hB)
    (Sylow.ofCard (Subgroup.zpowers a) hA)
  refine ⟨n, ?_⟩
  have h1 : MulAut.conj n • b ∈
      ((n • Sylow.ofCard (Subgroup.zpowers b) hB : Sylow p Q) : Subgroup Q) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul b (MulAut.conj n) _ (Subgroup.mem_zpowers b)
  rw [hn] at h1
  exact h1

theorem exists_orderOf_thirteen_conj_cube_of_surjective {H U : Type*} [Group H] [Finite H]
    [Group U] (φ : H →* U) (hφ : Function.Surjective φ) (h169 : ¬ 13 ^ 2 ∣ Nat.card H)
    {g x : U} (hg : orderOf g = 13) (hxg : x * g * x⁻¹ = g ^ 3) :
    ∃ g' y : H, orderOf g' = 13 ∧ y * g' * y⁻¹ = g' ^ 3 := by
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨g₀, hg₀⟩ := hφ g
  obtain ⟨y₀, hy₀⟩ := hφ x
  have h13 : 13 ∣ orderOf g₀ := by
    have h := orderOf_map_dvd φ g₀
    rwa [hg₀, hg] at h
  obtain ⟨m, hm⟩ := h13
  have hm13 : ¬ 13 ∣ m := by
    rintro ⟨k, rfl⟩
    refine h169 ((?_ : 13 ^ 2 ∣ orderOf g₀).trans (orderOf_dvd_natCard g₀))
    exact ⟨k, by rw [hm]; ring⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (orderOf_pos g₀).ne' (by simpa using hm)
  have hg₁ : orderOf (g₀ ^ m) = 13 := by
    rw [orderOf_pow_of_dvd hm0 ⟨13, by rw [hm]; ring⟩, hm]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have hĝ : φ (g₀ ^ m) = g ^ m := by rw [map_pow, hg₀]
  have hĝo : orderOf (g ^ m) = 13 := by
    rw [Nat.Coprime.orderOf_pow, hg]
    rw [hg]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm13
  have hx : x * g ^ m * x⁻¹ = (g ^ m) ^ 3 := by
    rw [← conj_pow, hxg, ← pow_mul, ← pow_mul, mul_comm]
  have hφ₂ : φ (y₀ * g₀ ^ m * y₀⁻¹) = (g ^ m) ^ 3 := by
    rw [map_mul, map_mul, map_inv, hy₀, hĝ, hx]
  have hg₂ : orderOf (y₀ * g₀ ^ m * y₀⁻¹) = 13 := by
    have h := orderOf_injective (MulAut.conj y₀).toMonoidHom (MulAut.conj y₀).injective
      (g₀ ^ m)
    rw [← hg₁]
    exact h
  let Q : Subgroup H := (Subgroup.zpowers (g ^ m)).comap φ
  have hg₁Q : g₀ ^ m ∈ Q := by
    rw [Subgroup.mem_comap, hĝ]
    exact Subgroup.mem_zpowers _
  have hg₂Q : y₀ * g₀ ^ m * y₀⁻¹ ∈ Q := by
    rw [Subgroup.mem_comap, hφ₂]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3
  have hQ : ¬ 13 ^ 2 ∣ Nat.card Q := fun h => h169 (h.trans (Subgroup.card_subgroup_dvd_card Q))
  obtain ⟨n, hn⟩ := exists_conj_mem_zpowers_of_orderOf_eq_prime hQ
    (a := (⟨g₀ ^ m, hg₁Q⟩ : Q)) (b := (⟨y₀ * g₀ ^ m * y₀⁻¹, hg₂Q⟩ : Q))
    (by rw [Subgroup.orderOf_mk, hg₁]) (by rw [Subgroup.orderOf_mk, hg₂])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
  have hk' : (n : H) * (y₀ * g₀ ^ m * y₀⁻¹) * (n : H)⁻¹ = (g₀ ^ m) ^ k := by
    have h := congrArg Subtype.val hk
    simpa using h.symm
  refine ⟨g₀ ^ m, (n : H) * y₀, hg₁, ?_⟩
  have h3 : ((n : H) * y₀) * g₀ ^ m * ((n : H) * y₀)⁻¹ = (g₀ ^ m) ^ k := by
    rw [← hk']
    group
  have hcomm : Commute (φ n) (g ^ m) := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 n.2)
    rw [← hj]
    exact (Commute.refl (g ^ m)).zpow_left j
  have h4 : (g ^ m) ^ k = (g ^ m) ^ 3 := by
    have h5 := congrArg φ h3
    rw [map_zpow, hĝ] at h5
    rw [← h5]
    calc φ ((n : H) * y₀ * g₀ ^ m * ((n : H) * y₀)⁻¹)
        = φ n * (x * g ^ m * x⁻¹) * (φ n)⁻¹ := by
          simp only [map_mul, map_inv, hy₀, hĝ]
          group
      _ = (g ^ m) ^ 3 := by
          rw [hx, (hcomm.pow_right 3).eq, mul_inv_cancel_right]
  have h5 : (k : ℤ) ≡ 3 [ZMOD 13] := by
    have h := zpow_eq_zpow_iff_modEq.1 (by simpa using h4 : (g ^ m) ^ k = (g ^ m) ^ (3 : ℤ))
    rw [hĝo] at h
    exact_mod_cast h
  have h6 : (g₀ ^ m) ^ k = (g₀ ^ m) ^ (3 : ℤ) :=
    zpow_eq_zpow_iff_modEq.2 (by rw [hg₁]; exact_mod_cast h5)
  rw [h3, h6]
  exact zpow_ofNat _ 3

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
