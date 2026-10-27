module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Open.StatedAPI CFSG.Quasithin

theorem uIn_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : UIn X) : UIn Y := by
  obtain ⟨hconj, z, g, hz, hord⟩ := h
  refine ⟨fun a b ha hb => ?_, e z, e g, (e.orderOf_eq z).trans hz, ?_⟩
  · obtain ⟨c, hc⟩ := isConj_iff.1 (hconj (e.symm a) (e.symm b)
      ((e.symm.orderOf_eq a).trans ha) ((e.symm.orderOf_eq b).trans hb))
    refine isConj_iff.2 ⟨e c, e.symm.injective ?_⟩
    simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using hc
  · have h1 : e z * ((e g)⁻¹ * e z * e g) = e (z * (g⁻¹ * z * g)) := by
      simp only [map_mul, map_inv]
    rw [h1, e.orderOf_eq]
    exact hord

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  letI := Fintype.ofFinite K
  obtain ⟨p, hp, m, hpp, hcard⟩ := FiniteField.card' (K := K)
  have hdvd : p ∣ 2 ^ n := by
    rw [← hK, Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p m.ne_zero
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact hp

theorem coprime_three_two_pow_sub_one {n : ℕ} (hn : Odd n) : Nat.Coprime 3 (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ := hn
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num [mul_comm]
  have hpos : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three, h2]
  omega

theorem units_eq_one_of_pow_three {K : Type} [Field K] {n : ℕ} (hn : Odd n)
    (hK : Nat.card K = 2 ^ n) {c : Kˣ} (hc : c ^ 3 = 1) : c = 1 := by
  have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc
  have h2 : orderOf c ∣ 2 ^ n - 1 := by
    have := orderOf_dvd_natCard c
    rwa [Nat.card_units, hK] at this
  have h3 : orderOf c ∣ Nat.gcd 3 (2 ^ n - 1) := Nat.dvd_gcd h1 h2
  rw [(coprime_three_two_pow_sub_one hn).gcd_eq_one] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem statedScalars_subgroupOf_sl3_eq_bot {K : Type} [Field K] [Finite K] {n : ℕ} (hn : Odd n)
    (hK : Nat.card K = 2 ^ n) :
    (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hmem : (g : GL (Fin 3) K) ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range :=
    Subgroup.mem_subgroupOf.1 hg
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hmem
  have hdet : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    det_of_mem_statedSL g.2
  rw [← hc] at hdet
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hc3 : c ^ 3 = 1 := Units.ext (by simpa using hdet)
  have hc1 : c = 1 := units_eq_one_of_pow_three hn hK hc3
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1]
  simp

noncomputable def statedSL3EquivProj {K : Type} [Field K] [Finite K] {n : ℕ} (hn : Odd n)
    (hK : Nat.card K = 2 ^ n) : StatedSL 3 K ≃* StatedProj (StatedSL 3 K) :=
  ((QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_sl3_eq_bot hn hK)).trans
    QuotientGroup.quotientBot).symm

section Involutions

open Matrix

variable {K : Type} [Field K]

@[expose] def nkE (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 0, 0; 0, 0, 0]

theorem two_le_finrank_ker_of_sq_zero {N : Matrix (Fin 3) (Fin 3) K} (hsq : N * N = 0) :
    2 ≤ Module.finrank K (LinearMap.ker N.mulVecLin) := by
  have hle : LinearMap.range N.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hsq,
      Matrix.zero_mulVec]
  have h1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  have h2 := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at h1
  omega

theorem exists_mulVec_ne_zero {N : Matrix (Fin 3) (Fin 3) K} (hN : N ≠ 0) :
    ∃ x : Fin 3 → K, N *ᵥ x ≠ 0 := by
  by_contra h
  apply hN
  have hall : ∀ x : Fin 3 → K, N *ᵥ x = 0 := fun x =>
    Classical.byContradiction fun hx => h ⟨x, hx⟩
  ext i j
  have h' := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h'

theorem exists_unit_of_sq_zero {N : Matrix (Fin 3) (Fin 3) K} (hsq : N * N = 0) (hN : N ≠ 0) :
    ∃ P : Matrix (Fin 3) (Fin 3) K, IsUnit P.det ∧ N * P = P * nkE K := by
  obtain ⟨e3, he3⟩ := exists_mulVec_ne_zero hN
  have hdim := two_le_finrank_ker_of_sq_zero hsq
  have hkey : ∀ x : Fin 3 → K, x ∈ LinearMap.ker N.mulVecLin ↔ N *ᵥ x = 0 := fun x => by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → K, u = N *ᵥ e3 := ⟨_, rfl⟩
  rw [← hu] at he3
  have hu0 : N *ᵥ u = 0 := by
    rw [hu, Matrix.mulVec_mulVec, hsq, Matrix.zero_mulVec]
  have huK : u ∈ LinearMap.ker N.mulVecLin := (hkey u).2 hu0
  have hle : K ∙ u ≤ LinearMap.ker N.mulVecLin :=
    (Submodule.span_singleton_le_iff_mem u _).2 huK
  have hlt : K ∙ u < LinearMap.ker N.mulVecLin := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 := finrank_span_singleton (K := K) he3
    rw [heq] at h1
    omega
  obtain ⟨e2, he2K, he2u⟩ := SetLike.exists_of_lt hlt
  have he2 : N *ᵥ e2 = 0 := (hkey e2).1 he2K
  have hmv : ∀ v : Fin 3 → K, (Matrix.of fun i j => ![u, e2, e3] j i) *ᵥ v =
      v 0 • u + v 1 • e2 + v 2 • e3 := by
    intro v
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  refine ⟨Matrix.of fun i j => ![u, e2, e3] j i, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hN' : N *ᵥ ((Matrix.of fun i j => ![u, e2, e3] j i) *ᵥ v) = 0 := by
      rw [hPv, Matrix.mulVec_zero]
    rw [hmv, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hu0, he2, ← hu] at hN'
    have hv2 : v 2 = 0 := by
      simp only [smul_zero, add_zero, zero_add] at hN'
      exact (smul_eq_zero.1 hN').resolve_right he3
    have hPv2 : v 0 • u + v 1 • e2 = 0 := by
      have h := hPv
      rw [hmv, hv2, zero_smul, add_zero] at h
      exact h
    have hv1 : v 1 = 0 := by
      by_contra hv1
      apply he2u
      have h1 : v 1 • e2 = -(v 0 • u) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hPv2
      have hmem : v 1 • e2 ∈ K ∙ u := by
        rw [h1]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
      have := Submodule.smul_mem (K ∙ u) (v 1)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hv1, one_smul] at this
    have hv0 : v 0 = 0 := by
      rw [hv1, zero_smul, add_zero] at hPv2
      exact (smul_eq_zero.1 hPv2).resolve_right he3
    apply hv
    funext k
    fin_cases k
    · exact hv0
    · exact hv1
    · exact hv2
  · ext i j
    fin_cases j
    · have h := congrFun hu0 i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, nkE, Matrix.mul_apply] at h ⊢
      exact h
    · have h := congrFun he2 i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, nkE, Matrix.mul_apply] at h ⊢
      first | exact h | exact h.symm | linarith
    · have h := congrFun hu i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, nkE, Matrix.mul_apply] at h ⊢
      first | exact h | exact h.symm | linarith

theorem nkJ_mul_self (K : Type) [Field K] [CharP K 2] :
    (1 + nkE K) * (1 + nkE K) = (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nkE, Matrix.mul_apply, Fin.sum_univ_three, one_add_one_eq_two, h2]

@[expose] def nkJGL (K : Type) [Field K] [CharP K 2] : GL (Fin 3) K :=
  ⟨1 + nkE K, 1 + nkE K, nkJ_mul_self K, nkJ_mul_self K⟩

@[expose] def nkC (K : Type) [Field K] (d : Kˣ) : GL (Fin 3) K :=
  ⟨diagonal ![1, (d : K), 1], diagonal ![1, ((d⁻¹ : Kˣ) : K), 1], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

theorem nkC_det (K : Type) [Field K] (d : Kˣ) : Matrix.GeneralLinearGroup.det (nkC K d) = d := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (diagonal ![1, (d : K), 1]).det = (d : K)
  rw [det_diagonal, Fin.prod_univ_three]
  simp

theorem nkC_mul_nkJGL_comm (K : Type) [Field K] [CharP K 2] (d : Kˣ) :
    nkC K d * nkJGL K = nkJGL K * nkC K d := by
  apply Units.ext
  show diagonal ![1, (d : K), 1] * (1 + nkE K) = (1 + nkE K) * diagonal ![1, (d : K), 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nkE, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply]

theorem exists_conj_nkJGL {K : Type} [Field K] [CharP K 2] (t : GL (Fin 3) K)
    (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ g : GL (Fin 3) K, Matrix.GeneralLinearGroup.det g = 1 ∧ g * t * g⁻¹ = nkJGL K := by
  have htt : (t : Matrix (Fin 3) (Fin 3) K) * t = 1 := by
    have := congrArg Units.val ht
    simpa using this
  have h2 : (2 : Matrix (Fin 3) (Fin 3) K) = 0 := by
    rw [← map_ofNat (algebraMap K (Matrix (Fin 3) (Fin 3) K)) 2, CharTwo.two_eq_zero, map_zero]
  set N : Matrix (Fin 3) (Fin 3) K := (t : Matrix (Fin 3) (Fin 3) K) - 1 with hNdef
  have hsq : N * N = 0 := by
    have e1 : N * N =
        (t : Matrix (Fin 3) (Fin 3) K) * t - 2 * (t : Matrix (Fin 3) (Fin 3) K) + 1 := by
      rw [hNdef]
      noncomm_ring
    rw [e1, htt, h2, zero_mul, sub_zero, one_add_one_eq_two, h2]
  have hN : N ≠ 0 := by
    intro h0
    apply ht1
    apply Units.ext
    rw [Units.val_one]
    exact sub_eq_zero.1 h0
  obtain ⟨P, hPu, hNP⟩ := exists_unit_of_sq_zero hsq hN
  let g : GL (Fin 3) K :=
    Units.mk P⁻¹ P (Matrix.nonsing_inv_mul P hPu) (Matrix.mul_nonsing_inv P hPu)
  have hgt : g * t * g⁻¹ = nkJGL K := by
    apply Units.ext
    have hg : ((g * t * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        P⁻¹ * (t : Matrix (Fin 3) (Fin 3) K) * P := rfl
    rw [hg]
    show P⁻¹ * (t : Matrix (Fin 3) (Fin 3) K) * P = 1 + nkE K
    have ht' : (t : Matrix (Fin 3) (Fin 3) K) = N + 1 := by
      rw [hNdef, sub_add_cancel]
    rw [ht']
    calc P⁻¹ * (N + 1) * P = P⁻¹ * (N * P) + P⁻¹ * P := by
          simp only [mul_add, add_mul, mul_one, Matrix.mul_assoc]
      _ = P⁻¹ * (P * nkE K) + P⁻¹ * P := by rw [hNP]
      _ = nkE K + 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPu, one_mul]
      _ = 1 + nkE K := add_comm _ _
  set d : Kˣ := (Matrix.GeneralLinearGroup.det g)⁻¹ with hd
  refine ⟨nkC K d * g, ?_, ?_⟩
  · rw [map_mul, nkC_det, hd, inv_mul_cancel]
  · calc nkC K d * g * t * (nkC K d * g)⁻¹ = nkC K d * (g * t * g⁻¹) * (nkC K d)⁻¹ := by group
      _ = nkC K d * nkJGL K * (nkC K d)⁻¹ := by rw [hgt]
      _ = nkJGL K * nkC K d * (nkC K d)⁻¹ := by rw [nkC_mul_nkJGL_comm]
      _ = nkJGL K := by rw [mul_assoc, mul_inv_cancel, mul_one]

end Involutions


section SL3

open Matrix

theorem mem_statedSL3_of_det {K : Type} [Field K] {g : GL (Fin 3) K}
    (h : Matrix.GeneralLinearGroup.det g = 1) : g ∈ StatedSL 3 K := by
  rw [statedSL_eq_ker_det, MonoidHom.mem_ker]
  exact h

theorem mul_self_ne_one_of_orderOf_two {K : Type} [Field K] {x : ↥(StatedSL 3 K)}
    (hx : orderOf x = 2) : (x : GL (Fin 3) K) * x = 1 ∧ (x : GL (Fin 3) K) ≠ 1 := by
  obtain ⟨h1, h2⟩ := orderOf_eq_prime_iff.1 hx
  refine ⟨?_, fun h => h2 (Subtype.ext h)⟩
  have := congrArg Subtype.val h1
  simpa [sq] using this

theorem sl3_isConj_of_orderOf_two {K : Type} [Field K] [CharP K 2] (a b : ↥(StatedSL 3 K))
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨ha2, ha1⟩ := mul_self_ne_one_of_orderOf_two ha
  obtain ⟨hb2, hb1⟩ := mul_self_ne_one_of_orderOf_two hb
  obtain ⟨ga, hga, hgaJ⟩ := exists_conj_nkJGL _ ha2 ha1
  obtain ⟨gb, hgb, hgbJ⟩ := exists_conj_nkJGL _ hb2 hb1
  refine isConj_iff.2 ⟨⟨gb⁻¹ * ga, mem_statedSL3_of_det (by
    rw [map_mul, map_inv, hga, hgb, inv_one, mul_one])⟩, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc gb⁻¹ * ga * (a : GL (Fin 3) K) * (gb⁻¹ * ga)⁻¹
      = gb⁻¹ * (ga * (a : GL (Fin 3) K) * ga⁻¹) * gb := by group
    _ = gb⁻¹ * nkJGL K * gb := by rw [hgaJ]
    _ = gb⁻¹ * (gb * (b : GL (Fin 3) K) * gb⁻¹) * gb := by rw [hgbJ]
    _ = (b : GL (Fin 3) K) := by group

@[expose] def nkD (K : Type) [Field K] (a : Kˣ) : GL (Fin 3) K :=
  ⟨diagonal ![(a : K), 1, ((a⁻¹ : Kˣ) : K)], diagonal ![((a⁻¹ : Kˣ) : K), 1, (a : K)], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

theorem nkD_mul (K : Type) [Field K] (a b : Kˣ) : nkD K (a * b) = nkD K a * nkD K b := by
  apply Units.ext
  show diagonal ![((a * b : Kˣ) : K), 1, (((a * b)⁻¹ : Kˣ) : K)] =
    diagonal ![(a : K), 1, ((a⁻¹ : Kˣ) : K)] * diagonal ![(b : K), 1, ((b⁻¹ : Kˣ) : K)]
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_inv, mul_comm]

@[expose] def nkDHom (K : Type) [Field K] : Kˣ →* GL (Fin 3) K :=
  MonoidHom.mk' (nkD K) (nkD_mul K)

theorem nkDHom_injective (K : Type) [Field K] : Function.Injective (nkDHom K) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply Units.ext
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) ha
  simpa [nkDHom, nkD] using h

theorem nkD_det (K : Type) [Field K] (a : Kˣ) : Matrix.GeneralLinearGroup.det (nkD K a) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (diagonal ![(a : K), 1, ((a⁻¹ : Kˣ) : K)]).det = 1
  rw [det_diagonal, Fin.prod_univ_three]
  simp

@[expose] def nkZ (K : Type) [Field K] : GL (Fin 3) K :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem nkZ_mul_nkD_mul_nkZ (K : Type) [Field K] (b : Kˣ) :
    nkZ K * nkD K b * nkZ K = nkD K b⁻¹ := by
  apply Units.ext
  show !![(0 : K), 0, 1; 0, 1, 0; 1, 0, 0] * diagonal ![(b : K), 1, ((b⁻¹ : Kˣ) : K)] *
      !![(0 : K), 0, 1; 0, 1, 0; 1, 0, 0] = diagonal ![((b⁻¹ : Kˣ) : K), 1, (b : K)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, diagonal_apply]

theorem nkZ_det (K : Type) [Field K] [CharP K 2] : Matrix.GeneralLinearGroup.det (nkZ K) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (!![(0 : K), 0, 1; 0, 1, 0; 1, 0, 0]).det = 1
  rw [Matrix.det_fin_three]
  simp [CharTwo.neg_eq]

theorem sl3_uin_order {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : Odd n)
    (h3 : 3 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ z g : ↥(StatedSL 3 K), orderOf z = 2 ∧ 6 ≤ orderOf (z * (g⁻¹ * z * g)) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hordA : orderOf a = 2 ^ n - 1 := by rw [ha, Nat.card_units, hK]
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1n : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hcop : Nat.Coprime (orderOf a) 2 := by
    rw [hordA]
    have hodd : ¬ 2 ∣ 2 ^ n - 1 := by omega
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hsq : orderOf (a * a) = orderOf a := by
    rw [← sq]
    exact Nat.Coprime.orderOf_pow hcop
  have hzmem : nkZ K ∈ StatedSL 3 K := mem_statedSL3_of_det (nkZ_det K)
  have hdmem : ∀ b : Kˣ, nkD K b ∈ StatedSL 3 K := fun b => mem_statedSL3_of_det (nkD_det K b)
  let z : ↥(StatedSL 3 K) := ⟨nkZ K, hzmem⟩
  let g : ↥(StatedSL 3 K) := ⟨nkD K a, hdmem a⟩
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, sq]
    show nkZ K * nkZ K = 1
    exact Units.ext (by
      show (!![(0 : K), 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) *
        !![(0 : K), 0, 1; 0, 1, 0; 1, 0, 0] = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three])
  have hz1 : z ≠ 1 := by
    intro h
    have h' := congrArg
      (fun g : ↥(StatedSL 3 K) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2) h
    simp [z, nkZ] at h'
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hcomp : ((z * (g⁻¹ * z * g) : ↥(StatedSL 3 K)) : GL (Fin 3) K) = nkDHom K (a * a) := by
    have hinv : ((g⁻¹ : ↥(StatedSL 3 K)) : GL (Fin 3) K) = nkD K a⁻¹ :=
      (map_inv (nkDHom K) a).symm
    simp only [Subgroup.coe_mul, hinv, z, g]
    show nkZ K * (nkD K a⁻¹ * nkZ K * nkD K a) = nkD K (a * a)
    calc nkZ K * (nkD K a⁻¹ * nkZ K * nkD K a)
        = (nkZ K * nkD K a⁻¹ * nkZ K) * nkD K a := by group
      _ = nkD K a * nkD K a := by rw [nkZ_mul_nkD_mul_nkZ, inv_inv]
      _ = nkD K (a * a) := (nkD_mul K a a).symm
  refine ⟨z, g, hzord, ?_⟩
  rw [← Subgroup.orderOf_coe, hcomp]
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
  rw [orderOf_injective (nkDHom K) (nkDHom_injective K) (a * a)]
  change 6 ≤ orderOf (a * a)
  rw [hsq, hordA]
  omega

theorem uIn_statedSL3 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : Odd n)
    (h3 : 3 ≤ n) (hK : Nat.card K = 2 ^ n) : UIn ↥(StatedSL 3 K) := by
  obtain ⟨z, g, hz, hord⟩ := sl3_uin_order hn h3 hK
  exact ⟨fun a b ha hb => sl3_isConj_of_orderOf_two a b ha hb, z, g, hz, hord⟩

theorem nk_l3_uin (n : ℕ) (hn : Odd n) (h3 : 3 ≤ n) (X : Type) [Group X] (hX : IsPSL 3 2 n X) :
    UIn X := by
  obtain ⟨-, K, hKf, hfin, hcard, ⟨e⟩⟩ := hX
  have hchar : CharP K 2 := charP_two_of_card (by omega) hcard
  have hU : UIn ↥(StatedSL 3 K) := uIn_statedSL3 hn h3 hcard
  exact uIn_of_mulEquiv (e.trans (statedSL3EquivProj hn hcard).symm).symm hU

end SL3

end CFSG.Quasithin.H13.L829NK
