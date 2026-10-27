module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIU3OddTools
import CFSG.Open.StatedCenterThree
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeSylow

public section

namespace CFSG.RankThree.PartTwo.Sec18

open Matrix CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {p f : ℕ}

theorem eq_one_of_mem_normalizer_sd_u3odd189 (hK : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hq3 : p ^ f % 3 = 1) (hq4 : p ^ f % 4 = 1) {z : Kˣ}
    (hz : orderOf z = 2 * 2 ^ (p ^ f - 1).factorization 2)
    {u τ : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)}
    (hu : (u : GL (Fin 3) K) = diagGL ![z, z ^ (-(p : ℤ) ^ f), z ^ ((p : ℤ) ^ f - 1)])
    (hτ : (τ : GL (Fin 3) K) = swapNegGL)
    (hou : orderOf u = 2 * 2 ^ (p ^ f - 1).factorization 2) (hτ2 : τ ^ 2 = 1)
    (hτu : τ⁻¹ * u * τ = u ^ (-(p : ℤ) ^ f))
    (hnf : ∀ w ∈ Subgroup.closure {u, τ}, ∃ i e : ℕ, e < 2 ∧ w = u ^ i * τ ^ e)
    {y : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)}
    (hy : y ∈ Subgroup.normalizer (Subgroup.closure ({u, τ} :
      Set (SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K))) : Set _))
    (hy3 : y ^ 3 = 1) : y = 1 := by
  have := hK.finite
  set W := Subgroup.closure ({u, τ} :
    Set (SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K))) with hWdef
  set q := p ^ f with hqdef
  set r := 2 ^ (q - 1).factorization 2 with hrdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hK.prime.pos
  have hq2 : 2 ≤ q := Nat.one_lt_pow (by have := hK.one_le; omega) hK.prime.one_lt
  have hr4 : 4 ∣ r := by
    have h4 : 2 ^ 2 ∣ q - 1 := by omega
    exact pow_dvd_pow 2 ((Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).1 h4)
  have hrq : r ∣ q - 1 := Nat.ordProj_dvd (q - 1) 2
  have hr0 : 0 < r := by positivity
  have hQ : ((q : ℕ) : ℤ) = (p : ℤ) ^ f := by rw [hqdef]; push_cast; rfl
  have mat_mul : ∀ g h : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K),
      (((g * h : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)) :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((h : GL (Fin 3) K) : Matrix _ _ K) :=
    fun g h => by rw [Subgroup.coe_mul, Units.val_mul]
  have mat_inj : ∀ g h : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K),
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ((h : GL (Fin 3) K) : Matrix _ _ K) →
        g = h := fun g h e => Subtype.ext (Units.ext e)
  have huW : u ∈ W := Subgroup.subset_closure (by simp)
  have hτW : τ ∈ W := Subgroup.subset_closure (by simp)
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by rw [← sq, hτ2])
  obtain ⟨i, e, he, hw⟩ := hnf (y * u * y⁻¹) ((Subgroup.mem_normalizer_iff.1 hy u).1 huW)
  have hwo : orderOf (y * u * y⁻¹) = 2 * r := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hou]
  have he0 : e = 0 := by
    interval_cases e
    · rfl
    · exfalso
      have h4 : (u ^ i * τ ^ 1) ^ 4 = 1 := by
        have hsq : (u ^ i * τ) ^ 2 = u ^ ((i : ℤ) + -(p : ℤ) ^ f * i) := by
          have h1 : τ⁻¹ * u ^ i * τ = (u ^ (-(p : ℤ) ^ f)) ^ i := by
            have h := conj_pow (i := i) (a := τ⁻¹) (b := u)
            rw [inv_inv] at h
            rw [← hτu, h]
          calc (u ^ i * τ) ^ 2 = u ^ i * (τ⁻¹ * u ^ i * τ) := by
                rw [sq, hτinv]
                group
            _ = u ^ ((i : ℤ) + -(p : ℤ) ^ f * i) := by
                rw [h1, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_add]
        rw [pow_one, show 4 = 2 * 2 from rfl, pow_mul, hsq, ← zpow_natCast, ← _root_.zpow_mul]
        rw [← orderOf_dvd_iff_zpow_eq_one, hou]
        obtain ⟨c, hc⟩ := hrq
        have hc' : (p : ℤ) ^ f - 1 = r * c := by
          rw [← hQ]
          have : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by push_cast [Nat.cast_sub hq1]; ring
          rw [← this, hc]
          push_cast
          ring
        exact ⟨-(i * c), by push_cast; linear_combination (-2 * (i : ℤ)) * hc'⟩
      have := orderOf_dvd_of_pow_eq_one h4
      rw [← hw, hwo] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
  rw [he0, pow_zero, mul_one] at hw
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hw
    have hu1 : u = 1 := by
      calc u = y⁻¹ * (y * u * y⁻¹) * y := by group
        _ = 1 := by rw [hw, mul_one, inv_mul_cancel]
    rw [hu1, orderOf_one] at hou
    omega
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hpow : ∀ n : ℕ, y * u ^ n * y⁻¹ = u ^ ((k + 1) * n) := fun n => by
    rw [← conj_pow, hw, pow_mul]
  have hcube : u ^ ((k + 1) * ((k + 1) * (k + 1))) = u := by
    calc u ^ ((k + 1) * ((k + 1) * (k + 1))) = y * u ^ ((k + 1) * (k + 1)) * y⁻¹ :=
          (hpow _).symm
      _ = y * (y * u ^ (k + 1) * y⁻¹) * y⁻¹ := by rw [hpow (k + 1)]
      _ = y * (y * (y * u * y⁻¹) * y⁻¹) * y⁻¹ := by rw [hw]
      _ = y ^ 3 * u * (y ^ 3)⁻¹ := by rw [pow_three]; group
      _ = u := by rw [hy3, one_mul, inv_one, mul_one]
  have hyu : y * u * y⁻¹ = u := by
    have hk : u ^ (k * (k ^ 2 + 3 * k + 3)) = 1 := by
      have e1 : (k + 1) * ((k + 1) * (k + 1)) = k * (k ^ 2 + 3 * k + 3) + 1 := by ring
      rw [e1, pow_succ] at hcube
      exact mul_eq_right.1 hcube
    have hdvd := orderOf_dvd_of_pow_eq_one hk
    rw [hou] at hdvd
    have hodd : Odd (k ^ 2 + 3 * k + 3) := by
      have : Even (k * (k + 3)) := by
        rcases Nat.even_or_odd k with h | h
        · exact h.mul_right _
        · exact (h.add_odd (by decide : Odd 3)).mul_left _
      have e2 : k ^ 2 + 3 * k + 3 = k * (k + 3) + 3 := by ring
      rw [e2]
      exact this.add_odd (by decide)
    have hcop : Nat.Coprime (2 * r) (k ^ 2 + 3 * k + 3) := by
      rw [hrdef, ← pow_succ']
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
    have hk' : u ^ k = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hou]
      exact hcop.dvd_of_dvd_mul_right hdvd
    rw [hw, pow_succ, hk', one_mul]
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  set dz : Fin 3 → K := fun k => ((![z, z ^ (-(p : ℤ) ^ f), z ^ ((p : ℤ) ^ f - 1)] k : Kˣ) : K)
    with hdz
  have hU : ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal dz := by
    rw [hu, coe_diagGL]
  have hzpow : ∀ a b : ℤ, z ^ a = z ^ b → (2 * (r : ℤ)) ∣ b - a := fun a b h => by
    have := (zpow_eq_zpow_iff_modEq.1 h)
    rw [hz] at this
    push_cast at this
    exact (Int.ModEq.dvd this)
  have hQodd : (p : ℤ) ^ f % 4 = 1 := by rw [← hQ]; omega
  have h4r : (4 : ℤ) ∣ 2 * r := by
    obtain ⟨c, hc⟩ := hr4
    exact ⟨2 * c, by rw [hc]; push_cast; ring⟩
  have hdz_inj : Function.Injective dz := by
    have h01 : z ≠ z ^ (-(p : ℤ) ^ f) := by
      intro h
      have := hzpow 1 (-(p : ℤ) ^ f) ((zpow_one z).trans h)
      obtain ⟨c, hc⟩ := h4r.trans this
      omega
    have h02 : z ≠ z ^ ((p : ℤ) ^ f - 1) := by
      intro h
      have := hzpow 1 ((p : ℤ) ^ f - 1) ((zpow_one z).trans h)
      obtain ⟨c, hc⟩ := (dvd_mul_right 2 (r : ℤ)).trans this
      omega
    have h12 : z ^ (-(p : ℤ) ^ f) ≠ z ^ ((p : ℤ) ^ f - 1) := by
      intro h
      have := hzpow _ _ h
      obtain ⟨c, hc⟩ := (dvd_mul_right 2 (r : ℤ)).trans this
      omega
    have hinj := injective_vec_three_u3odd189 (fun h => h01 (Units.ext h))
      (fun h => h02 (Units.ext h)) (fun h => h12 (Units.ext h))
    intro a b hab
    apply hinj
    fin_cases a <;> fin_cases b <;> simpa [hdz] using hab
  have hYU : Y * diagonal dz = diagonal dz * Y := by
    have h1 : y * u = u * y := by
      calc y * u = y * u * y⁻¹ * y := by group
        _ = u * y := by rw [hyu]
    have := congrArg (fun g : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) K) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
    simpa only [mat_mul, hU, ← hYdef] using this
  have hYd := CFSG.Open.StatedCenterThree.eq_diagonal_of_commute hdz_inj hYU
  have hY3 : Y * Y * Y = 1 := by
    have := congrArg (fun g : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) K) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hy3
    simp only [pow_three, mat_mul, Subgroup.coe_one, Units.val_one, ← hYdef] at this
    rw [← this, Matrix.mul_assoc]
  have hcube3 : ∀ k, Y k k ^ 3 = 1 := by
    intro k
    have := congrFun (congrFun hY3 k) k
    rw [hYd, diagonal_mul_diagonal, diagonal_mul_diagonal] at this
    simpa [pow_three, mul_assoc] using this
  have hgram := y.2.2
  rw [← hYdef, hYd, ctr_diagonal] at hgram
  have h01 : hK.bar (Y 0 0) * Y 1 1 = 1 := by
    have := congrFun (congrFun hgram 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have h22 : hK.bar (Y 2 2) * Y 2 2 = 1 := by
    have := congrFun (congrFun hgram 2) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using this
  have hbar0 : hK.bar (Y 0 0) = Y 0 0 := by
    rw [hK.bar_apply, ← Nat.div_add_mod (p ^ f) 3, hq3, pow_add, pow_mul, hcube3 0, one_pow,
      one_mul, pow_one]
  rw [hbar0] at h01
  have hc1 : Y 2 2 = 1 :=
    eq_one_of_pow_three_u3odd189 hq3 (hcube3 2) (by rw [← hK.bar_apply]; exact h22)
  have ha0 : Y 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one h01
  obtain ⟨j, e', he', hw'⟩ := hnf (y * τ * y⁻¹) ((Subgroup.mem_normalizer_iff.1 hy τ).1 hτW)
  have huj : (((u ^ j : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun k => (((![z, z ^ (-(p : ℤ) ^ f), z ^ ((p : ℤ) ^ f - 1)] ^ j) k : Kˣ) : K) := by
    rw [Subgroup.coe_pow, hu, diagGL_pow_u3odd189, coe_diagGL]
  have hyτ : Y * !![0, 1, 0; 1, 0, 0; 0, 0, -1] = diagonal (fun k =>
      (((![z, z ^ (-(p : ℤ) ^ f), z ^ ((p : ℤ) ^ f - 1)] ^ j) k : Kˣ) : K)) *
      (((τ ^ e' : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)) :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Y := by
    have h1 : y * τ = u ^ j * τ ^ e' * y := by rw [← hw']; group
    have := congrArg (fun g : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) K) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
    rw [mat_mul y τ, mat_mul (u ^ j * τ ^ e') y, mat_mul (u ^ j) (τ ^ e'), huj, hτ,
      coe_swapNegGL, ← hYdef] at this
    exact this
  have hentry := congrFun (congrFun hyτ 0) 1
  rw [hYd] at hentry
  interval_cases e'
  ·
    exfalso
    simp [Matrix.mul_apply, Fin.sum_univ_three] at hentry
    exact ha0 hentry
  ·
    rw [pow_one, hτ, coe_swapNegGL] at hentry
    simp [Matrix.mul_apply, Fin.sum_univ_three] at hentry
    have hsq : Y 0 0 * Y 0 0 = ((z ^ j : Kˣ) : K) := by
      rw [Units.val_pow_eq_pow_val]
      calc Y 0 0 * Y 0 0 = Y 0 0 * ((z : K) ^ j * Y 1 1) := by rw [← hentry]
        _ = (z : K) ^ j * (Y 0 0 * Y 1 1) := by ring
        _ = (z : K) ^ j := by rw [h01, mul_one]
    have hzj : z ^ j = 1 := by
      have h3 : (z ^ j) ^ 3 = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, ← hsq, Units.val_one]
        calc (Y 0 0 * Y 0 0) ^ 3 = (Y 0 0 ^ 3) ^ 2 := by ring
          _ = 1 := by rw [hcube3 0, one_pow])
      have h2r : (z ^ j) ^ (2 * r) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, ← hz, pow_orderOf_eq_one, one_pow]
      have hcop : Nat.Coprime 3 (2 * r) := by
        rw [hrdef, ← pow_succ']
        exact Nat.Coprime.pow_right _ (by decide)
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2r))
    have ha1 : Y 0 0 = 1 := by
      have hsq1 : Y 0 0 * Y 0 0 = 1 := by rw [hsq, hzj, Units.val_one]
      calc Y 0 0 = Y 0 0 * (Y 0 0 * Y 0 0) := by rw [hsq1, mul_one]
        _ = Y 0 0 ^ 3 := by ring
        _ = 1 := hcube3 0
    have hb1 : Y 1 1 = 1 := by rw [ha1, one_mul] at h01; exact h01
    apply mat_inj
    rw [← hYdef, hYd, Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext k
    fin_cases k
    · exact ha1
    · exact hb1
    · exact hc1

theorem eq_one_of_mem_normalizer_sylow_sd_u3odd189 (hK : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hq3 : p ^ f % 3 = 1) (hq4 : p ^ f % 4 = 1)
    (T : Sylow 2 (SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)))
    {y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)}
    (hy : y ∈ Subgroup.normalizer
      ((T : Subgroup (SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K))) : Set _))
    (hy3 : y ^ 3 = 1) : y = 1 := by
  have := hK.finite
  have hG : ∀ i j, hK.bar ((1 : Matrix (Fin 3) (Fin 3) K) j i) =
      (1 : Matrix (Fin 3) (Fin 3) K) i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by simp
  obtain ⟨-, -, -, -, -, h6⟩ :=
    odd_unitary_three_exact_coordinate_and_Sylow_models hK hp2 hG hdet ⊥ bot_le
  obtain ⟨⟨z, hzo⟩, ⟨M, hM⟩, hm⟩ := h6 hq4
  obtain ⟨u, τ, hu, hτ, hou, hτ2, hτu, -, hnf, -, hWcard, -⟩ := hm M hM z hzo
  let ψ := gramEquiv (τ := hK.bar) (G₁ := !![0, 1, 0; 1, 0, 0; 0, 0, 1])
    (G₂ := (1 : Matrix (Fin 3) (Fin 3) K)) M hM
  have hu' : ((ψ u : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)) :
      GL (Fin 3) K) = diagGL ![z, z ^ (-(p : ℤ) ^ f), z ^ ((p : ℤ) ^ f - 1)] := by
    rw [coe_gramEquiv, hu]
    group
  have hτ' : ((ψ τ : SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)) :
      GL (Fin 3) K) = swapNegGL := by
    rw [coe_gramEquiv, hτ]
    group
  have hW : (Subgroup.closure ({u, τ} : Set (SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)))).map
      ψ.toMonoidHom = Subgroup.closure {ψ u, ψ τ} := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have hcard : Nat.card (Subgroup.closure ({ψ u, ψ τ} : Set (SUgram hK.bar
      (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)))) =
      2 ^ (Nat.card (SUgram hK.bar (!![0, 1, 0; 1, 0, 0; 0, 0, 1] :
        Matrix (Fin 3) (Fin 3) K))).factorization 2 := by
    rw [← hW, Subgroup.card_map_of_injective ψ.injective, hWcard, Nat.card_congr ψ.toEquiv]
  have hnf' : ∀ w ∈ Subgroup.closure ({ψ u, ψ τ} : Set (SUgram hK.bar
      (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K))),
      ∃ i e : ℕ, e < 2 ∧ w = ψ u ^ i * ψ τ ^ e := by
    intro w hw
    rw [← hW] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    obtain ⟨i, e, -, he, rfl⟩ := hnf w₀ hw₀
    exact ⟨i, e, he, by simp [map_mul, map_pow]⟩
  refine eq_one_of_mulEquiv_u3odd189 ψ (fun T' y' hy' hy3' => ?_) T hy hy3
  refine eq_one_of_sylow_u3odd189 hcard (fun y'' hy'' hy3'' => ?_) T' hy' hy3'
  exact eq_one_of_mem_normalizer_sd_u3odd189 hK hp2 hq3 hq4 hzo hu' hτ'
    (by rw [MulEquiv.orderOf_eq, hou]) (by rw [← map_pow, hτ2, map_one])
    (by rw [← map_inv, ← map_mul, ← map_mul, hτu, map_zpow]) hnf' hy'' hy3''

end CFSG.RankThree.PartTwo.Sec18
