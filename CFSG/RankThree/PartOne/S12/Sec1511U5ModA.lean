module

public import CFSG.RankThree.PartOne.S12.Sec1511U5Act
public import CFSG.RankThree.PartOne.KC.UnitaryGoodLift

public section

namespace CFSG.RankThree.PartOne

namespace Sec1511

namespace U5M

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem toLinU_scalar {z : primeFormUnitary h (idGram K 5)} {c : Kˣ}
    (hz : (z : GL (Fin 5) K) = GeneralLinearGroup.scalar (Fin 5) c) :
    ((toLinU h 5 z : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) =
      (c : K) • (1 : Module.End K (Fin 5 → K)) := by
  refine LinearMap.ext fun v => ?_
  rw [toLinU_apply_vec, hz, scalar_mulVec]
  rfl

theorem exists_comm_scalar (hq : 3 < 2 ^ f) (A B : primeFormUnitary h (idGram K 5))
    (hAB : primeFormConjHom h (idGram K 5) A * primeFormConjHom h (idGram K 5) B =
      primeFormConjHom h (idGram K 5) B * primeFormConjHom h (idGram K 5) A) :
    ∃ c : K, ((toLinU h 5 A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) *
      ((toLinU h 5 B : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) =
      c • (((toLinU h 5 B : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
          Module.End K (Fin 5 → K)) *
        ((toLinU h 5 A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
          Module.End K (Fin 5 → K))) := by
  set z := (B * A)⁻¹ * (A * B) with hz
  have h1 : primeFormConjHom h (idGram K 5) z = 1 := by
    rw [hz, map_mul, map_inv, map_mul, map_mul, hAB]
    exact inv_mul_cancel _
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff (by norm_num) hq z).1 h1
  refine ⟨c, ?_⟩
  have hz' : A * B = (B * A) * z := by
    rw [hz]
    group
  have h2 := toLinU_scalar hc
  have h3 : ((toLinU h 5 (A * B) : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) =
      ((toLinU h 5 (B * A) : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) * ((toLinU h 5 z : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
          Module.End K (Fin 5 → K)) := by
    rw [hz', map_mul, Units.val_mul]
  rw [map_mul, Units.val_mul, map_mul, Units.val_mul, h2] at h3
  rw [h3, mul_smul_comm, mul_one]

theorem scalar_of_commute (hq : 3 < 2 ^ f) (g : Gam h) (A : primeFormUnitary h (idGram K 5))
    (hcomm : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) g *
        primeFormConjHom h (idGram K 5) A =
      primeFormConjHom h (idGram K 5) A *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) g) :
    ∃ ν : K, ν ≠ 0 ∧ ∀ v, act g (((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v) =
      ν • (((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ act g v) := by
  have h1 : primeFormConjHom h (idGram K 5) (idUAction h 5 g A * A⁻¹) = 1 := by
    rw [map_mul, map_inv, ← primeFormPsi_conj_primeFormConjHom, hcomm]
    group
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff (by norm_num) hq _).1 h1
  refine ⟨c, c.ne_zero, fun v => ?_⟩
  have h2 : ((idUAction h 5 g A : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) c * (A : GL (Fin 5) K) := by
    have : ((idUAction h 5 g A * A⁻¹ : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) *
        (A : GL (Fin 5) K) = (idUAction h 5 g A : GL (Fin 5) K) := by
      simp
    rw [← this, hc]
  rw [← conj_rel, h2, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact scalar_mulVec c _

theorem ringEquiv_fix_zeta {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {ψ : K ≃+* K} (h5 : ψ ^ 5 = 1) :
    ψ ζ = ζ := by
  obtain ⟨i, hi, hiψ⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ψ ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hk : ∀ k : ℕ, (ψ ^ k) ζ = ζ ^ (i ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', RingAut.mul_apply, ih, map_pow, ← hiψ, ← pow_mul, ← pow_succ']
  have h1 : ζ ^ (i ^ 5) = ζ := by
    rw [← hk 5, h5]
    rfl
  have h2 : ζ ^ (i ^ 5 % 5) = ζ ^ 1 := by
    have := pow_mod_orderOf ζ (i ^ 5)
    rw [← hζ.eq_orderOf] at this
    rw [this, h1, pow_one]
  have h3 : i ^ 5 % 5 = 1 := hζ.pow_inj (Nat.mod_lt _ (by norm_num)) (by norm_num) h2
  have key : ∀ j : ℕ, j < 5 → j ^ 5 % 5 = 1 → j = 1 := by decide
  rw [← hiψ, key i hi h3, pow_one]

theorem invol_moves_zeta (h : UnitaryFieldData 2 f K) (hf5 : 5 ∣ 2 ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) {φ : K ≃+* K} (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) : φ ζ ≠ ζ := by
  intro hfix
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := h.finite
  have hf0 : 1 ≤ 2 * f := by
    rcases Nat.eq_zero_or_pos f with hf | hf
    · subst hf
      norm_num at hf5
    · omega
  obtain ⟨σ, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := K) (p := 2) (n := 2 * f) Nat.prime_two hf0 h.card
  obtain ⟨-, S, hS, hScard⟩ := hA (Subgroup.zpowers φ)
  have hord : orderOf φ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hφ2) hφ1
  rw [Nat.card_zpowers, hord, show 2 * f / 2 = f by omega] at hScard
  have hst : Subgroup.zpowers φ ≤ MulAction.stabilizer (K ≃+* K) ζ :=
    Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hfix)
  have hmem : ζ ∈ S := by
    have : ζ ∈ (S : Set K) := by
      rw [hS]
      intro τ hτ
      exact MulAction.mem_stabilizer_iff.1 (hst hτ)
    exact this
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have : Fintype S := Fintype.ofFinite S
  have h1 := FiniteField.pow_card_sub_one_eq_one (⟨ζ, hmem⟩ : S) (fun h0 => hζ0 (congrArg Subtype.val h0))
  have h2 : ζ ^ (2 ^ f - 1) = 1 := by
    have := congrArg Subtype.val h1
    rw [← Nat.card_eq_fintype_card, hScard] at this
    simpa using this
  have h3 : 5 ∣ 2 ^ f - 1 := hζ.dvd_of_pow_eq_one _ h2
  have h4 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  omega

theorem pow_five_data (hq : 3 < 2 ^ f) (g : Gam h)
    (hg : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) g ^ 5 = 1) :
    g.right ^ 5 = 1 ∧ ∃ c : K, c ≠ 0 ∧
      ∀ v, act g (act g (act g (act g (act g v)))) = c • v := by
  have h1 : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) (g ^ 5) = 1 := by
    rw [map_pow]
    exact hg
  obtain ⟨hr, c, hc0, hc⟩ := act_ker hq (g ^ 5) h1
  refine ⟨?_, c, hc0, fun v => ?_⟩
  · have := map_pow (SemidirectProduct.rightHom :
      Gam h →* (K ≃+* K)) g 5
    simp only [SemidirectProduct.rightHom_eq_right] at this
    rw [← this]
    exact hr
  · have : act (g ^ 5) v = act g (act g (act g (act g (act g v)))) := by
      simp only [pow_succ, pow_zero, one_mul, act_mul]
    rw [← this]
    exact hc v

theorem pow_two_data (hq : 3 < 2 ^ f) (g : Gam h)
    (hg : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) g *
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) g = 1) :
    g.right * g.right = 1 ∧ ∃ c : K, c ≠ 0 ∧ ∀ v, act g (act g v) = c • v := by
  have h1 : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) (g * g) = 1 := by
    rw [map_mul]
    exact hg
  obtain ⟨hr, c, hc0, hc⟩ := act_ker hq (g * g) h1
  refine ⟨?_, c, hc0, fun v => ?_⟩
  · have := hr
    rw [SemidirectProduct.mul_right] at this
    exact this
  · rw [← act_mul]
    exact hc v

theorem commute_act (hq : 3 < 2 ^ f) (g g' : Gam h)
    (hcomm : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) g' *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) g =
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) g *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5)) g') :
    ∃ κ : K, ∀ v, act g' (act g v) = κ • act g (act g' v) := by
  have h1 : primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5))
      ((g' * g) * (g * g')⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hcomm]
    exact mul_inv_cancel _
  obtain ⟨-, c, -, hc⟩ := act_ker hq _ h1
  refine ⟨c, fun v => ?_⟩
  have h2 : g' * g = ((g' * g) * (g * g')⁻¹) * (g * g') := by group
  calc act g' (act g v) = act (g' * g) v := (act_mul g' g v).symm
    _ = act (((g' * g) * (g * g')⁻¹) * (g * g')) v := by rw [← h2]
    _ = c • act g (act g' v) := by rw [act_mul, hc, act_mul]

theorem conjHom_eq_of_smul (hq : 3 < 2 ^ f) (A B : primeFormUnitary h (idGram K 5)) (κ : K)
    (hAB : ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      κ • ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) :
    primeFormConjHom h (idGram K 5) B = primeFormConjHom h (idGram K 5) A := by
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hAB
    exact Units.ne_zero _ hAB
  set κ' : Kˣ := Units.mk0 κ hκ0 with hκ'
  have hz : ((B * A⁻¹ : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) κ' := by
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, GeneralLinearGroup.coe_scalar, hAB,
      Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp [hκ', Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  have hmem : GeneralLinearGroup.scalar (Fin 5) κ' ∈
      primeFormUnitary h (idGram K 5 : Matrix (Fin 5) (Fin 5) K) := by
    rw [← hz]
    exact (B * A⁻¹).2
  have hnorm := norm_eq_one_of_scalar_mem_primeFormUnitary h (by norm_num : 1 ≤ 5)
    (1 : GL (Fin 5) K) hmem
  have h1 : primeFormConjHom h (idGram K 5) (B * A⁻¹) = 1 :=
    (primeFormConjHom_eq_one_iff (by norm_num) hq _).2
      ⟨κ', (pow_succ_eq_one_iff_norm h κ').2 hnorm, hz⟩
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

end U5M

end Sec1511

end CFSG.RankThree.PartOne
