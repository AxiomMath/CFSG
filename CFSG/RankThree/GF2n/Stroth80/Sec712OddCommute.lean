module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem eqOneOfCommutesOdd_holds :
    ∀ (K E : Type) [Field K] [Finite K] [CharP K 2] [AddCommGroup E] [Module K E] [Finite E]
      (Λ : Subgroup (E ≃ₗ[K] E)), IsPGroup 2 Λ → ∀ b : E, b ≠ 0 → (∀ g ∈ Λ, g b = b) →
      (∀ e : E, (∀ g ∈ Λ, g e = e) → ∃ c : K, e = c • b) →
      ∀ Qf : E → K, (∀ (c : K) e, Qf (c • e) = c ^ 2 * Qf e) → (∃ e, Qf e ≠ 0) →
      ∀ T : E ≃ₗ[K] E, (∀ g ∈ Λ, g * T = T * g) → (∀ e, Qf (T e) = Qf e) →
      ∀ m : ℕ, Odd m → T ^ m = 1 → T = 1 := by
  intro K E _ _ _ _ _ _ Λ hΛ b hb hbfix hline Qf hQ hQne T hcomm hQT m hm hTm
  letI : Fintype K := Fintype.ofFinite K
  have hcx : ∀ g ∈ Λ, ∀ x : E, g (T x) = T (g x) := fun g hg x =>
    DFunLike.congr_fun (hcomm g hg) x
  have hTb : ∀ g ∈ Λ, g (T b) = T b := fun g hg => by
    rw [hcx g hg b, hbfix g hg]
  obtain ⟨α, hα⟩ := hline (T b) hTb
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply hb
    have h0 : T b = 0 := by rw [hα, zero_smul]
    exact T.map_eq_zero_iff.mp h0
  obtain ⟨T', hT'⟩ : ∃ T' : E →ₗ[K] E, T' = α⁻¹ • (T : E →ₗ[K] E) := ⟨_, rfl⟩
  have hT'x : ∀ x, T' x = α⁻¹ • T x := fun x => by
    subst hT'
    rfl
  have hT'g : ∀ g ∈ Λ, ∀ x, g (T' x) = T' (g x) := fun g hg x => by
    rw [hT'x, hT'x, map_smul, hcx g hg x]
  have hT'b : T' b = b := by
    rw [hT'x, hα, inv_smul_smul₀ hα0]
  have hq : 2 ∣ Fintype.card K :=
    (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
  have hqpos : 0 < Fintype.card K := Fintype.card_pos
  have hodd : Odd (Fintype.card K - 1) := by
    obtain ⟨j, hj⟩ := hq
    exact ⟨j - 1, by omega⟩
  have hαn : α⁻¹ ^ (Fintype.card K - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ (inv_ne_zero hα0)
  have hTpow : ∀ k : ℕ, ∀ x : E, (T ^ k) x = ((T : E →ₗ[K] E) ^ k) x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ T k, pow_succ (T : E →ₗ[K] E) k, Module.End.mul_apply]
      exact ih (T x)
  have hPm : (T : E →ₗ[K] E) ^ m = 1 := by
    apply LinearMap.ext
    intro x
    have h1 : (T ^ m) x = x := DFunLike.congr_fun hTm x
    rw [Module.End.one_apply, ← hTpow m x, h1]
  have hpowT' : ∀ k : ℕ, T' ^ k = (α⁻¹ ^ k) • (T : E →ₗ[K] E) ^ k := by
    subst hT'
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ (α⁻¹ • (T : E →ₗ[K] E)) k, ih, smul_mul_assoc, mul_smul_comm, smul_smul,
        pow_succ α⁻¹ k, pow_succ (T : E →ₗ[K] E) k]
  have hT'N : T' ^ (m * (Fintype.card K - 1)) = 1 := by
    rw [hpowT', pow_mul' α⁻¹ m, hαn, one_pow, pow_mul (T : E →ₗ[K] E) m, hPm, one_pow,
      one_smul]
  have hinf := ker_inf_range_eq_bot_of_pow_eq_one (hm.mul hodd) hT'N
  have hbker : b ∈ LinearMap.ker (T' - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hT'b, sub_self]
  have hSinv : ∀ g ∈ Λ, ∀ v ∈ LinearMap.range (T' - 1), g v ∈ LinearMap.range (T' - 1) := by
    intro g hg v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
    refine LinearMap.mem_range.mpr ⟨g u, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub, hT'g g hg u]
  have hSbot : LinearMap.range (T' - 1) = ⊥ := by
    by_contra hS0
    obtain ⟨v, hvS, hv0, hvfix⟩ :=
      exists_fixed_vector_of_isPGroup Λ hΛ (LinearMap.range (T' - 1)) hSinv hS0
    obtain ⟨c, hc⟩ := hline v hvfix
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hv0
      rw [hc, zero_smul]
    have hbS : b ∈ LinearMap.range (T' - 1) := by
      have hb' : b = c⁻¹ • v := by
        rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hb']
      exact Submodule.smul_mem _ _ hvS
    have hbot : b ∈ LinearMap.ker (T' - 1) ⊓ LinearMap.range (T' - 1) :=
      Submodule.mem_inf.mpr ⟨hbker, hbS⟩
    rw [hinf, Submodule.mem_bot] at hbot
    exact hb hbot
  have hfixT' : ∀ x, T' x = x := by
    intro x
    have hx : (T' - 1) x ∈ LinearMap.range (T' - 1) := LinearMap.mem_range_self _ x
    rw [hSbot, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    exact hx
  have hTx : ∀ x, T x = α • x := by
    intro x
    have h := hfixT' x
    rw [hT'x] at h
    calc T x = α • (α⁻¹ • T x) := (smul_inv_smul₀ hα0 _).symm
      _ = α • x := by rw [h]
  obtain ⟨e₀, he₀⟩ := hQne
  have hQα : α ^ 2 * Qf e₀ = Qf e₀ := by
    rw [← hQ α e₀, ← hTx e₀]
    exact hQT e₀
  have hα2 : α ^ 2 = 1 := by
    apply mul_right_cancel₀ he₀
    rw [one_mul]
    exact hQα
  have hα1 : α = 1 := by
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : (α - 1) ^ 2 = 0 := by
      linear_combination hα2 + (1 - α) * h2K
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  refine LinearEquiv.ext fun x => ?_
  have h1 : α • x = x := by rw [hα1, one_smul]
  exact (hTx x).trans h1

end CFSG.RankThree.GF2n.Stroth80
