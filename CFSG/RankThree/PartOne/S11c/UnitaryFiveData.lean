module

public import CFSG.LocalAnalysis.SectionRank.OddCover.UnitaryThree
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.RankThree.PartOne.HNRed

open Matrix CFSG.LieType.Universal.Unitary CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits
open scoped commutatorElement

section Torus

variable {K : Type} [Field K] {σ : K ≃+* K}

noncomputable def torusSU (t1 t2 t3 : K) (h1 : t1 ≠ 0) (h2 : t2 ≠ 0) (h3 : t3 ≠ 0)
    (hdet : t1 * t2 * t3 = 1) (hiso1 : σ t1 * t3 = 1) (hiso2 : σ t2 * t2 = 1)
    (hiso3 : σ t3 * t1 = 1) : SU σ 3 :=
  ⟨⟨diagonal ![t1, t2, t3], diagonal ![t1⁻¹, t2⁻¹, t3⁻¹],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [h1, h2, h3],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [h1, h2, h3]⟩,
    by simpa [Fin.prod_univ_three, det_diagonal] using hdet,
    by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_three, diagonal, Fin.rev, hiso1,
          hiso2, hiso3]⟩

end Torus

section Data

variable {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 5)] [CharP K 5]

omit [Finite K] [Fact (Nat.Prime 5)] [CharP K 5] in
theorem torusSU_conj_heisSU_zero {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c) {t1 t2 t3 : K}
    (h1 : t1 ≠ 0) (h2 : t2 ≠ 0) (h3 : t3 ≠ 0) (hdet : t1 * t2 * t3 = 1)
    (hiso1 : σ t1 * t3 = 1) (hiso2 : σ t2 * t2 = 1) (hiso3 : σ t3 * t1 = 1) (β : K)
    (hβ : β + σ β + σ 0 * 0 = 0)
    (hβ' : t1 * t3⁻¹ * β + σ (t1 * t3⁻¹ * β) + σ 0 * 0 = 0) :
    torusSU t1 t2 t3 h1 h2 h3 hdet hiso1 hiso2 hiso3 * heisSU hσ 0 β hβ *
      (torusSU t1 t2 t3 h1 h2 h3 hdet hiso1 hiso2 hiso3)⁻¹ = heisSU hσ 0 (t1 * t3⁻¹ * β) hβ' := by
  apply SU_ext
  have hinv : ((((torusSU t1 t2 t3 h1 h2 h3 hdet hiso1 hiso2 hiso3)⁻¹ : SU σ 3) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![t1⁻¹, t2⁻¹, t3⁻¹] := rfl
  have hfwd : ((((torusSU t1 t2 t3 h1 h2 h3 hdet hiso1 hiso2 hiso3) : SU σ 3) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![t1, t2, t3] := rfl
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hinv, hfwd, coe_heisSU, coe_heisSU, CFSG.LieType.Steinberg.heisenbergMatrix_three,
    CFSG.LieType.Steinberg.heisenbergMatrix_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, diagonal, h1, h2, h3]
  field_simp

end Data

section Data2

variable {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 5)] [CharP K 5]

omit [Finite K] [Fact (Nat.Prime 5)] in
theorem heisSU_pow_five {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c) (a b : K)
    (hab : b + σ b + σ a * a = 0) : (heisSU hσ a b hab) ^ 5 = 1 := by
  apply SU_ext
  have h5 : ((5 : ℕ) : K) = 0 := CharP.cast_eq_zero K 5
  have h10 : ((Nat.choose 5 2 : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K 5 _).2 (by decide)
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_heisSU, heis_pow, h5, h10, zero_mul,
    zero_mul, zero_mul, sub_zero, CFSG.LieType.Universal.Unitary.heisenbergMatrix_zero]
  rfl

omit [Finite K] [Fact (Nat.Prime 5)] in
theorem eq_natCast_of_pow_four {u : K} (hu : u ^ 4 = 1) :
    u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have hfac : (u - 1) * (u - 2) * (u - 3) * (u - 4) = 0 := by
    linear_combination hu + (-2 * u ^ 3 + 7 * u ^ 2 - 10 * u + 5) * h5
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
  · exact Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h)))

end Data2

section SUData

variable {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 5)] [CharP K 5]

theorem exists_heisenberg_data_SU (hK : Nat.card K = (5 ^ 1) ^ 2) :
    ∃ (x y h : SU (unitaryInvolution K 5 1) 3) (m : ℕ), (m % 5 = 2 ∨ m % 5 = 3) ∧ x ^ 5 = 1 ∧
      y ^ 5 = 1 ∧ Commute ⁅y, x⁆ x ∧ Commute ⁅y, x⁆ y ∧ ⁅y, x⁆ ^ 5 = 1 ∧ ⁅y, x⁆ ≠ 1 ∧
      h * ⁅y, x⁆ * h⁻¹ = ⁅y, x⁆ ^ m := by
  set σ := unitaryInvolution K 5 1 with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 5]; norm_num)
  have h22 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  obtain ⟨ζ, hζ0, hζ'⟩ := exists_unitaryInvolution_eq_neg hK
  have hζ : σ ζ = -ζ := hζ'
  have hσ2 : σ (2⁻¹ : K) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  have hb1 : σ (-2⁻¹ : K) = -2⁻¹ := by rw [map_neg, hσ2]
  have hx : (-2⁻¹ : K) + σ (-2⁻¹) + σ 1 * 1 = 0 := by
    rw [hb1, map_one]; linear_combination -h22
  have hb2 : σ (ζ ^ 2 * 2⁻¹) = ζ ^ 2 * 2⁻¹ := by rw [map_mul, map_pow, hσ2, hζ, neg_sq]
  have hy : ζ ^ 2 * 2⁻¹ + σ (ζ ^ 2 * 2⁻¹) + σ ζ * ζ = 0 := by
    rw [hb2, hζ]; linear_combination ζ ^ 2 * h22
  have hβ : 1 * σ ζ - ζ * σ 1 + σ (1 * σ ζ - ζ * σ 1) + σ 0 * 0 = 0 := by
    simp only [map_sub, map_mul, map_one, map_zero, hζ, map_neg]
    ring
  set x := heisSU hσ 1 (-2⁻¹) hx with hxdef
  set y := heisSU hσ ζ (ζ ^ 2 * 2⁻¹) hy with hydef
  have hyx : ⁅y, x⁆ = heisSU hσ 0 (1 * σ ζ - ζ * σ 1) hβ :=
    commutator_heisSU hσ ζ _ 1 _ hy hx hβ
  set β : K := 1 * σ ζ - ζ * σ 1 with hβdef
  have hβval : β = -(2 * ζ) := by rw [hβdef, map_one, hζ]; ring
  have hσβ : σ β = -β := by
    rw [hβval, map_neg, map_mul, map_ofNat, hζ]
    ring
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [hβval] at h0
    have : 2 * ζ = 0 := by linear_combination -h0
    exact hζ0 ((mul_eq_zero.1 this).resolve_left h2)
  have hz1 : ⁅y, x⁆ ≠ 1 := by
    intro h1
    rw [hyx] at h1
    have h02 := congrArg (fun g : SU σ 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2) h1
    simp [coe_heisSU, CFSG.LieType.Steinberg.heisenbergMatrix_three] at h02
    rw [hζ] at h02
    exact hβ0 (by rw [hβval]; linear_combination h02)
  obtain ⟨ξ, hξ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf ξ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hξ
  have hcard : Nat.card Kˣ = 24 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    norm_num
  rw [hcard] at hord
  set u : K := (ξ : K) with hu
  have hu0 : u ≠ 0 := ξ.ne_zero
  have hu24 : u ^ 24 = 1 := by
    have h1 : ξ ^ 24 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ξ
    have h2 := congrArg (fun g : Kˣ => (g : K)) h1
    simpa using h2
  have hu6 : u ^ 6 ≠ 1 := by
    intro h6
    have : ξ ^ 6 = 1 := Units.ext (by simpa using h6)
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num) this
  have hu12 : u ^ 12 ≠ 1 := by
    intro h12
    have : ξ ^ 12 = 1 := Units.ext (by simpa using h12)
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num) this
  obtain ⟨m, hm5, hum⟩ : ∃ m : ℕ, (m % 5 = 2 ∨ m % 5 = 3) ∧ u ^ 6 = (m : K) := by
    have h4 : (u ^ 6) ^ 4 = 1 := by rw [← pow_mul]; exact hu24
    rcases eq_natCast_of_pow_four h4 with h | h | h | h
    · exact absurd h hu6
    · exact ⟨2, Or.inl rfl, by simpa using h⟩
    · exact ⟨3, Or.inr rfl, by simpa using h⟩
    · exfalso
      apply hu12
      have h44 : (4 : K) * 4 = 1 := by
        have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
        linear_combination 3 * h5
      rw [show u ^ 12 = (u ^ 6) ^ 2 by ring, h, sq, h44]
  have hu5 : u ^ 5 ≠ 0 := pow_ne_zero 5 hu0
  have hσu : σ u = u ^ 5 := by rw [hσdef, unitaryInvolution_apply, pow_one]
  have hu25 : u ^ 25 = u := by
    rw [show 25 = 24 + 1 by norm_num, pow_add, hu24, one_mul, pow_one]
  have hdet : u * u ^ 4 * (u ^ 5)⁻¹ = 1 := by
    rw [show u * u ^ 4 = u ^ 5 by ring]
    exact mul_inv_cancel₀ hu5
  have hiso1 : σ u * (u ^ 5)⁻¹ = 1 := by rw [hσu]; exact mul_inv_cancel₀ hu5
  have hiso2 : σ (u ^ 4) * u ^ 4 = 1 := by
    rw [map_pow, hσu]
    calc (u ^ 5) ^ 4 * u ^ 4 = u ^ 24 := by ring
      _ = 1 := hu24
  have hiso3 : σ ((u ^ 5)⁻¹) * u = 1 := by
    rw [map_inv₀, map_pow, hσu, ← pow_mul, show 5 * 5 = 25 by norm_num, hu25]
    exact inv_mul_cancel₀ hu0
  have hmul : u * ((u ^ 5)⁻¹)⁻¹ = (m : K) := by
    rw [inv_inv, ← hum]
    ring
  have hβ' : u * ((u ^ 5)⁻¹)⁻¹ * β + σ (u * ((u ^ 5)⁻¹)⁻¹ * β) + σ 0 * 0 = 0 := by
    rw [hmul, map_mul, map_natCast, hσβ]
    simp
  have hconj := torusSU_conj_heisSU_zero hσ hu0 (pow_ne_zero 4 hu0) (inv_ne_zero hu5) hdet hiso1
    hiso2 hiso3 β hβ hβ'
  refine ⟨x, y, torusSU u (u ^ 4) ((u ^ 5)⁻¹) hu0 (pow_ne_zero 4 hu0) (inv_ne_zero hu5) hdet
    hiso1 hiso2 hiso3, m, hm5, heisSU_pow_five hσ _ _ hx, heisSU_pow_five hσ _ _ hy, ?_, ?_, ?_,
    hz1, ?_⟩
  · rw [hyx]
    exact commute_heisSU_zero hσ β 1 (-2⁻¹) hβ hx
  · rw [hyx]
    exact commute_heisSU_zero hσ β ζ _ hβ hy
  · rw [hyx]
    exact heisSU_pow_five hσ 0 β hβ
  · rw [hyx, hconj]
    apply SU_ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_heisSU, coe_heisSU, heis_pow, hmul]
    simp [hβdef]

end SUData

section ModelData

open CFSG.Open

theorem unitary_three_five_heisenberg_data {B : Type} [Group B]
    (hB : StatedClassicalModel B .PSU 3 5 1) :
    ∃ (x y h : B) (m : ℕ), (m % 5 = 2 ∨ m % 5 = 3) ∧ x ^ 5 = 1 ∧ y ^ 5 = 1 ∧
      Commute ⁅y, x⁆ x ∧ Commute ⁅y, x⁆ y ∧ ⁅y, x⁆ ^ 5 = 1 ∧ ⁅y, x⁆ ≠ 1 ∧
      h * ⁅y, x⁆ * h⁻¹ = ⁅y, x⁆ ^ m := by
  obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hK, ⟨eB⟩⟩ := hB
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : CharP K 5 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  obtain ⟨x, y, h, m, hm, hx5, hy5, hcx, hcy, hz5, hz1, hhz⟩ := exists_heisenberg_data_SU hK
  let eS := equivStatedSU hK 3
  set D := (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (5 ^ 1) K) with hD
  let ψ : SU (unitaryInvolution K 5 1) 3 →* B :=
    eB.symm.toMonoidHom.comp ((QuotientGroup.mk' D).comp eS.toMonoidHom)
  have hcardD : Nat.card D = 3 := by
    have := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_five hK (by norm_num : 1 ≤ 3)).2.2
    rw [this]
    norm_num
  have hcube : ∀ g : SU (unitaryInvolution K 5 1) 3, ψ g = 1 → g ^ 3 = 1 := by
    intro g hg
    have h1 : QuotientGroup.mk' D (eS g) = 1 := by
      have : eB.symm (QuotientGroup.mk' D (eS g)) = 1 := hg
      exact (MulEquiv.map_eq_one_iff eB.symm).mp this
    have h2 : eS g ∈ D := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (⟨eS g, h2⟩ : D) ^ 3 = 1 := by
      have := pow_card_eq_one' (x := (⟨eS g, h2⟩ : D))
      rwa [hcardD] at this
    have h4 : (eS g) ^ 3 = 1 := congrArg Subtype.val h3
    apply eS.injective
    rw [map_pow, h4, map_one]
  refine ⟨ψ x, ψ y, ψ h, m, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hx5, map_one]
  · rw [← map_pow, hy5, map_one]
  · rw [← map_commutatorElement]
    exact hcx.map ψ
  · rw [← map_commutatorElement]
    exact hcy.map ψ
  · rw [← map_commutatorElement, ← map_pow, hz5, map_one]
  · rw [← map_commutatorElement]
    intro h1
    have h3 := hcube _ h1
    have h5 := hz5
    have hdvd : orderOf ⁅y, x⁆ ∣ Nat.gcd 3 5 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h5)
    have : orderOf ⁅y, x⁆ = 1 := Nat.dvd_one.mp (by simpa using hdvd)
    exact hz1 (orderOf_eq_one_iff.mp this)
  · rw [← map_commutatorElement, ← map_inv, ← map_mul, ← map_mul, hhz, map_pow]

end ModelData

end CFSG.RankThree.PartOne.HNRed
