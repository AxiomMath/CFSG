module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open Matrix

theorem not_ordProj_dvd_qSubPi {π : Bool} {n : ℕ} (hq : ModThree π (2 ^ (3 * n)))
    (h0 : qSubPi π (2 ^ (3 * n)) ≠ 0) :
    ¬ ordProj[3] (qSubPi π (2 ^ (3 * n))) ∣ qSubPi π (2 ^ n) := by
  have hcube : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [hcube] at hq h0 ⊢
  have hq₀ := modThree_of_cube hq
  intro h
  apply Nat.pow_succ_factorization_not_dvd h0 Nat.prime_three
  rw [pow_succ]
  calc _ ∣ qSubPi π (2 ^ n) * (3 * (3 * (2 ^ n / 3) ^ 2 + 3 * (2 ^ n / 3) + 1)) :=
        Nat.mul_dvd_mul h (Dvd.intro _ rfl)
    _ = qSubPi π ((2 ^ n) ^ 3) := (qSubPi_cube_eq hq₀).symm

theorem pow_three_dvd_qSubPi_of_dvd {π : Bool} {n : ℕ} (hq : ModThree π (2 ^ (3 * n))) {k : ℕ}
    (h : 3 ^ k ∣ piCard π (2 ^ n) - 1) : 3 ^ k ∣ qSubPi π (2 ^ n) := by
  have hcube : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  have hq₀ : ModThree π (2 ^ n) := modThree_of_cube (by rwa [hcube] at hq)
  cases π
  · change 2 ^ n % 3 = 2 at hq₀
    change 3 ^ k ∣ (2 ^ n) ^ 2 - 1 at h
    change 3 ^ k ∣ 2 ^ n + 1
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      have := Nat.sq_sub_sq (2 ^ n) 1
      rwa [one_pow] at this
    rw [hfac] at h
    have h3 : ¬ 3 ∣ 2 ^ n - 1 := by
      generalize 2 ^ n = t at hq₀ ⊢
      omega
    exact (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      h3)).dvd_of_dvd_mul_right h
  · exact h

theorem eq_one_of_forall_sylow_fixed_slPi {X : Type} [Group X] [Finite X] {π : Bool} {n : ℕ}
    {K : Type} [Field K] (hn : 1 ≤ n) (hK : PiField π 2 (3 * n) K)
    (hq : ModThree π (2 ^ (3 * n))) (e : X ≃* slPi π 3 (2 ^ (3 * n)) K) (T : Sylow 3 X)
    {ζ : MulAut X} (hζ : ζ ^ 3 = 1) (hfix : ∀ t ∈ (T : Subgroup X), ζ t = t) : ζ = 1 := by
  have := hK.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  set N := qSubPi π (2 ^ (3 * n)) with hN
  have hN0 : N ≠ 0 := qSubPi_ne_zero hK hq
  have : NeZero N := ⟨hN0⟩
  have := rootsOfUnity.isCyclic K N
  obtain ⟨μ', hμ'⟩ := exists_orderOf_eq_of_dvd_card (G := rootsOfUnity N K)
    (d := ordProj[3] N) (by rw [card_rootsOfUnity_qSubPi hK hq]; exact Nat.ordProj_dvd N 3)
  set μ : Kˣ := (μ' : Kˣ) with hμdef
  have hμT : μ ∈ rootsOfUnity N K := μ'.2
  have hμord : orderOf μ = ordProj[3] N := by rw [hμdef, Subgroup.orderOf_coe, hμ']
  have hge : 2 ≤ N.factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hN0).mp
      (by simpa using nine_dvd_qSubPi hq)
  have h9le : 9 ≤ ordProj[3] N :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ N.factorization 3 := Nat.pow_le_pow_right (by norm_num) hge
  have hμ1 : μ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hμord
    omega
  have hμ2 : μ ^ 2 ≠ 1 := by
    intro h2
    have := Nat.le_of_dvd (by norm_num) (hμord ▸ orderOf_dvd_of_pow_eq_one h2)
    omega
  have hμK2 : (μ : K) ^ 2 ≠ 1 := fun h' => hμ2 (Units.ext (by
    rw [Units.val_pow_eq_pow_val, h', Units.val_one]))
  have hμpow : μ ^ 3 ^ N.factorization 3 = 1 := by rw [← hμord]; exact pow_orderOf_eq_one μ
  have hPM := cycTorus_le_slPi hK hμT
  set PX : Subgroup X :=
    ((Subgroup.zpowers (cycThree : GL (Fin 3) K) ⊔ torusPow μ : Subgroup _).subgroupOf
      (slPi π 3 (2 ^ (3 * n)) K)).map e.symm.toMonoidHom with hPXdef
  have hPX : IsPGroup 3 PX :=
    ((isPGroup_cycTorus hμpow).comap_of_injective _ Subtype.val_injective).map _
  obtain ⟨x, hx⟩ := exists_conj_mem_sylow T hPX
  set t₀ : slPi π 3 (2 ^ (3 * n)) K := ⟨torusHom (μ, μ⁻¹), hPM (torusHom_inv_mem_cycTorus μ)⟩
  set w : slPi π 3 (2 ^ (3 * n)) K := ⟨cycThree, hPM (cycThree_mem_cycTorus μ)⟩
  have ht₀ : e.symm t₀ ∈ PX := ⟨t₀, torusHom_inv_mem_cycTorus μ, rfl⟩
  have hw : e.symm w ∈ PX := ⟨w, cycThree_mem_cycTorus μ, rfl⟩
  set ζ' := MulAut.congr e ζ with hζ'
  have hζ'3 : ζ' ^ 3 = 1 := by rw [hζ', ← map_pow, hζ, map_one]
  set c := e x with hc
  have hfix' : ∀ m : slPi π 3 (2 ^ (3 * n)) K, e.symm m ∈ PX →
      ζ' (c * m * c⁻¹) = c * m * c⁻¹ := by
    intro m hm
    have h1 := hfix _ (hx _ hm)
    have h2 : c * m * c⁻¹ = e (x * e.symm m * x⁻¹) := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [h2, hζ', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, h1]
  rcases exists_conj_or_field_of_pow_three_eq_one hK hq2 hζ'3 with
    ⟨y, -, hy⟩ | ⟨σ, hσ, H, -, hH⟩
  · have h1 : ζ' = 1 := eq_one_of_semiAct_one_of_fixed hy hμ1 hμ2 (c : GL (Fin 3) K)
      (s₁ := c * t₀ * c⁻¹) (s₂ := c * w * c⁻¹) rfl rfl (hfix' t₀ ht₀) (hfix' w hw)
    exact (MulAut.congr e).injective (h1.trans (map_one _).symm)
  · exfalso
    have htr := trace_fixed_of_field hH (hfix' t₀ ht₀)
    have htrace : ((((c * t₀ * c⁻¹ : slPi π 3 (2 ^ (3 * n)) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)).trace = (μ : K) + (μ : K)⁻¹ + 1 := by
      change ((((c : GL (Fin 3) K) * torusHom (μ, μ⁻¹) * (c : GL (Fin 3) K)⁻¹ :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).trace = _
      rw [trace_conj_gl, trace_torusHom_inv]
    rw [htrace, map_add σ ((μ : K) + (μ : K)⁻¹) 1, map_one] at htr
    have hσμ := ringAut_fixed_of_add_inv (ringAut_apply_three hσ) μ.ne_zero hμK2
      (add_right_cancel htr)
    obtain ⟨K₀, hK₀, hK₀card⟩ := exists_fixedField hK (f₀ := n) rfl hσ
    have hμK₀ : (μ : K) ∈ K₀ := (hK₀ μ).mpr hσμ
    have hpow : (μ : K) ^ (Nat.card K₀ - 1) = 1 := by
      have : Fintype K₀ := Fintype.ofFinite K₀
      have h := FiniteField.pow_card_sub_one_eq_one (⟨(μ : K), hμK₀⟩ : K₀) (by
        intro h0
        exact μ.ne_zero (congrArg Subtype.val h0))
      rw [← Nat.card_eq_fintype_card] at h
      exact congrArg Subtype.val h
    have hpow' : μ ^ (Nat.card K₀ - 1) = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, hpow, Units.val_one])
    have hdvd : ordProj[3] N ∣ piCard π (2 ^ n) - 1 := by
      rw [← hμord, ← hK₀card]
      exact orderOf_dvd_of_pow_eq_one hpow'
    exact not_ordProj_dvd_qSubPi hq hN0 (pow_three_dvd_qSubPi_of_dvd hq hdvd)

theorem eq_one_of_forall_sylow_fixed_of_isSLThreePiAt {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 1 ≤ n) (hX : Sec4.IsSLThreePiAt X (2 ^ (3 * n))) (T : Sylow 3 X) {ζ : MulAut X}
    (hζ : ζ ^ 3 = 1) (hfix : ∀ t ∈ (T : Subgroup X), ζ t = t) : ζ = 1 := by
  obtain ⟨π, K, _, hK, hq, ⟨e⟩⟩ := exists_slPi_of_isSLThreePiAt hn hX
  exact eq_one_of_forall_sylow_fixed_slPi hn hK hq e T hζ hfix

end CFSG.RankThree.PartTwo.KFacts
