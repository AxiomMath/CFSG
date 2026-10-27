module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofLinDickson
public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofGU2

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU27

open scoped MatrixGroups commutatorElement

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.LieType.SeitzGeneration

variable {K : Type} [Field K]

@[expose] noncomputable def gl2Proj (K : Type) [Field K] : GL (Fin 2) K →* PGL(Fin 2, K) :=
  ProjGenLinGroup.mk

theorem ker_gl2Proj : (gl2Proj K).ker = Subgroup.center (GL (Fin 2) K) := by
  ext g
  rw [MonoidHom.mem_ker]
  exact ProjGenLinGroup.mk_eq_one

theorem card_center_gl2 [Finite K] :
    Nat.card (Subgroup.center (GL (Fin 2) K)) = Nat.card K - 1 := by
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := K)) := by
    intro u v huv
    have h := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) huv
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h
    exact Units.ext h
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar,
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units]

theorem card_range_gl2Proj [Finite K] :
    Nat.card (gl2Proj K).range = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite K
  have h1 := Subgroup.card_ker_mul_card_range (gl2Proj K)
  rw [ker_gl2Proj, card_center_gl2, Matrix.card_GL_field, Fin.prod_univ_two, Fin.val_zero,
    Fin.val_one, pow_zero, pow_one, ← Nat.card_eq_fintype_card] at h1
  have hq : 1 < Nat.card K := Finite.one_lt_card
  set q := Nat.card K with hqdef
  have e : (q ^ 2 - 1) * (q ^ 2 - q) = (q - 1) * (q * (q ^ 2 - 1)) := by
    have hq2 : q ≤ q ^ 2 := by nlinarith
    have : q ^ 2 - q = q * (q - 1) := by
      rw [Nat.mul_sub_one, sq]
    rw [this]
    ring
  rw [e] at h1
  exact Nat.eq_of_mul_eq_mul_left (by omega) h1

section Ext

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem charP_ext : CharP (FiniteField.Extension K p 2) p :=
  charP_of_injective_algebraMap (algebraMap K (FiniteField.Extension K p 2)).injective p

theorem isSquare_algebraMap (x : K) :
    IsSquare (algebraMap K (FiniteField.Extension K p 2) x) := by
  classical
  have := charP_ext (K := K) (p := p)
  set K₂ := FiniteField.Extension K p 2
  have := Fintype.ofFinite K₂
  have := Fintype.ofFinite K
  by_cases h2 : ringChar K₂ = 2
  · exact FiniteField.isSquare_of_char_two h2 _
  by_cases hx : x = 0
  · rw [hx, map_zero]
    exact ⟨0, by ring⟩
  have hx' : algebraMap K K₂ x ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact hx
  rw [FiniteField.isSquare_iff h2 hx']
  have hcard : Fintype.card K₂ = Fintype.card K ^ 2 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, FiniteField.natCard_extension]
  have hp2 : p ≠ 2 := by
    intro hp
    apply h2
    rw [ringChar.eq K₂ p, hp]
  have hodd : Odd (Fintype.card K) := by
    obtain ⟨n, hn, hcK⟩ := FiniteField.card K p
    rw [hcK]
    exact Odd.pow (Nat.Prime.odd_of_ne_two (Fact.out) hp2)
  obtain ⟨k, hk⟩ := hodd
  have hexp : Fintype.card K₂ / 2 = (Fintype.card K - 1) * (k + 1) := by
    rw [hcard, hk]
    have : (2 * k + 1) ^ 2 = 2 * ((2 * k + 1 - 1) * (k + 1)) + 1 := by
      rw [show 2 * k + 1 - 1 = 2 * k by omega]
      ring
    rw [this]
    omega
  rw [hexp, pow_mul, ← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, map_one, one_pow]

@[expose] noncomputable def gl2ProjExt (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : GL (Fin 2) K →* PGL(Fin 2, FiniteField.Extension K p 2) :=
  ProjGenLinGroup.mk.comp
    (Matrix.GeneralLinearGroup.map (algebraMap K (FiniteField.Extension K p 2)))

theorem coe_map_algebraMap (g : GL (Fin 2) K) :
    ((Matrix.GeneralLinearGroup.map (algebraMap K (FiniteField.Extension K p 2)) g :
      GL (Fin 2) (FiniteField.Extension K p 2)) :
        Matrix (Fin 2) (Fin 2) (FiniteField.Extension K p 2)) =
      (g : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (FiniteField.Extension K p 2)) :=
  rfl

theorem ker_gl2ProjExt : (gl2ProjExt K p).ker = (gl2Proj K).ker := by
  rw [ker_gl2Proj]
  ext g
  rw [MonoidHom.mem_ker, gl2ProjExt, MonoidHom.comp_apply, ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  set ι := algebraMap K (FiniteField.Extension K p 2) with hι
  constructor
  · rintro ⟨u, hu⟩
    have hm : ∀ i j, ι ((g : Matrix (Fin 2) (Fin 2) K) i j) =
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) _) :
          Matrix (Fin 2) (Fin 2) _) i j := fun i j => by
      rw [hu, coe_map_algebraMap, Matrix.map_apply]
    have h01 := hm 0 1
    have h10 := hm 1 0
    have h00 := hm 0 0
    have h11 := hm 1 1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide),
      Matrix.diagonal_apply_eq] at h01 h10 h00 h11
    have h01' : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
      apply ι.injective; rw [h01, map_zero]
    have h10' : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      apply ι.injective; rw [h10, map_zero]
    have h0011 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      apply ι.injective; rw [h00, h11]
    have hg00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
      intro h0
      have hd : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]
        exact Units.ne_zero _
      rw [Matrix.det_fin_two, h01', h10', ← h0011, h0] at hd
      simp at hd
    refine ⟨Units.mk0 _ hg00, Units.ext ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, h01', h10', h0011]
  · rintro ⟨u, hu⟩
    refine ⟨Units.map ι.toMonoidHom u, Units.ext ?_⟩
    rw [coe_map_algebraMap, ← hu]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hι]

theorem range_gl2ProjExt_le :
    (gl2ProjExt K p).range ≤
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
        (R := FiniteField.Extension K p 2)).range := by
  rintro _ ⟨g, rfl⟩
  refine mk_mem_range_toPGL _ ?_
  rw [coe_map_algebraMap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact isSquare_algebraMap _

omit [Fact p.Prime] [CharP K p] in
theorem sl2_le_of_card_ge_lin (hq4 : 4 ≤ Nat.card K) (Y : Subgroup (GL (Fin 2) K))
    (hcard : Nat.card K * (Nat.card K ^ 2 - 1) ≤ 2 * Nat.card (Y.map (gl2Proj K))) :
    ∀ g : SpecialLinearGroup (Fin 2) K, SpecialLinearGroup.toGL g ∈ Y := by
  classical
  set ψ := gl2Proj K with hψ
  set J := Y.map ψ with hJ
  set T : Subgroup (GL (Fin 2) K) := J.comap ψ with hT
  have hJle : J ≤ ψ.range := Y.map_le_range ψ
  have hTJ : T.map ψ = J := Subgroup.map_comap_eq_self hJle
  have hkT : ψ.ker ≤ T := fun z hz => by
    show ψ z ∈ J
    rw [MonoidHom.mem_ker.1 hz]
    exact J.one_mem
  have h1 : ψ.ker.relIndex T * T.index = ψ.ker.index := Subgroup.relIndex_mul_index hkT
  rw [Subgroup.relIndex_ker, hTJ, Subgroup.index_ker, card_range_gl2Proj] at h1
  have : Finite PGL(Fin 2, K) :=
    inferInstanceAs (Finite (GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)))
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hindex : T.index ≤ 2 := by
    have : Nat.card J * T.index ≤ Nat.card J * 2 := by rw [h1]; linarith
    exact Nat.le_of_mul_le_mul_left this hJpos
  have hindex0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  set S : Subgroup (GL (Fin 2) K) :=
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range with hS
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) := by
    apply CFSG.LinearGroups.special_linear_dimension_two_perfect
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hq4)
    exact ⟨t, ht⟩
  have hperf : Group.IsPerfect S :=
    Group.IsPerfect.ofSurjective (f := (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  have hSS : ⁅S, S⁆ = S := Subgroup.commutator_eq_self
  have hST : S ≤ T := by
    rw [← hSS]
    exact Subgroup.commutator_le.2 fun x _ y _ => commutator_mem_of_index_le_two hindex0 hindex x y
  have hker : ∀ z ∈ ψ.ker, z ∈ Subgroup.center (GL (Fin 2) K) := fun z hz => by
    rwa [hψ, ker_gl2Proj] at hz
  have hSY : S ≤ Y := by
    rw [← hSS]
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    obtain ⟨x', hx', hxx'⟩ := hST hx
    obtain ⟨y', hy', hyy'⟩ := hST hy
    have hz : x'⁻¹ * x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel]
    have hw : y'⁻¹ * y ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyy', inv_mul_cancel]
    have e : ⁅x, y⁆ = ⁅x', y'⁆ := by
      have hx2 : x = x' * (x'⁻¹ * x) := by group
      have hy2 : y = y' * (y'⁻¹ * y) := by group
      rw [hx2, hy2]
      exact commutatorElement_mul_central (hker _ hz) (hker _ hw)
    rw [e, commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hx' hy') (Y.inv_mem hx')) (Y.inv_mem hy')
  intro g
  exact hSY ⟨g, rfl⟩

theorem card_image_ge_lin {f : ℕ} (hKq : Nat.card K = p ^ f)
    (Y : Subgroup (GL (Fin 2) K)) {μ₁ μ₂ ν₁ ν₂ : K} {c ψ : Fin 2 → K} (hμ₁ : μ₁ ≠ 0)
    (hμ₂ : μ₂ ≠ 0) (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0) (hψc : ψ 0 * c 0 + ψ 1 * c 1 = 1)
    (hc0 : c 0 ≠ 0) (hc1 : c 1 ≠ 0) (hψ0 : ψ 0 ≠ 0) (hψ1 : ψ 1 ≠ 0)
    (hμ6 : 6 ≤ orderOf (μ₁ / μ₂)) (hsf : SubfieldOK p f (orderOf (μ₁ / μ₂)))
    (hν3 : 3 ≤ orderOf (ν₁ / ν₂)) {A B : GL (Fin 2) K}
    (hAm : (A : Matrix (Fin 2) (Fin 2) K) = diagonal ![μ₁, μ₂])
    (hBm : (B : Matrix (Fin 2) (Fin 2) K) =
      ν₂ • (1 : Matrix (Fin 2) (Fin 2) K) + (ν₁ - ν₂) • vecMulVec c ψ)
    (hA : A ∈ Y) (hB : B ∈ Y) :
    p ^ f * ((p ^ f) ^ 2 - 1) ≤ 2 * Nat.card (Y.map (gl2Proj K)) := by
  classical
  have := charP_ext (K := K) (p := p)
  set K₂ := FiniteField.Extension K p 2 with hK₂def
  set ι := algebraMap K K₂ with hι
  have hK₂ : Nat.card K₂ = p ^ (2 * f) := by
    rw [hK₂def, FiniteField.natCard_extension, hKq, ← pow_mul, mul_comm]
  have hιinj : Function.Injective ι := ι.injective
  have hρ : μ₁ / μ₂ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hμ6
    omega
  have hρν : ν₁ / ν₂ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hν3
    omega
  have hμ12 : μ₁ ≠ μ₂ := fun h1 => hρ (by rw [h1, div_self hμ₂])
  have hν12 : ν₁ ≠ ν₂ := fun h1 => hρν (by rw [h1, div_self hν₂])
  have hcop : Nat.Coprime p (orderOf (μ₁ / μ₂)) := by
    have := Fintype.ofFinite K
    have hpow : (μ₁ / μ₂) ^ (p ^ f - 1) = 1 := by
      have h := FiniteField.pow_card_sub_one_eq_one (μ₁ / μ₂) (div_ne_zero hμ₁ hμ₂)
      rwa [← Nat.card_eq_fintype_card, hKq] at h
    have hdvd : orderOf (μ₁ / μ₂) ∣ p ^ f - 1 := orderOf_dvd_of_pow_eq_one hpow
    have hf0 : f ≠ 0 := by
      rintro rfl
      have := Finite.one_lt_card (α := K)
      rw [hKq] at this
      simp at this
    have hcp : Nat.Coprime p (p ^ f - 1) := by
      have hp1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      have h' : Nat.Coprime (p ^ f) (p ^ f - 1) :=
        (Nat.coprime_self_sub_right hp1).mpr (Nat.coprime_one_right _)
      exact Nat.Coprime.coprime_dvd_left (dvd_pow_self p hf0) h'
    exact Nat.Coprime.coprime_dvd_right hdvd hcp
  obtain ⟨s, hs⟩ := isSquare_algebraMap (p := p) ((μ₁ * μ₂)⁻¹)
  obtain ⟨s', hs'⟩ := isSquare_algebraMap (p := p) ((ν₁ * ν₂)⁻¹)
  have hss : s * s * (ι μ₁ * ι μ₂) = 1 := by
    rw [← hs, ← map_mul, ← map_mul, inv_mul_cancel₀ (mul_ne_zero hμ₁ hμ₂), map_one]
  have hss' : s' * s' * (ι ν₁ * ι ν₂) = 1 := by
    rw [← hs', ← map_mul, ← map_mul, inv_mul_cancel₀ (mul_ne_zero hν₁ hν₂), map_one]
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hss
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    simp at hss'
  have hιμ₁ : ι μ₁ ≠ 0 := by rw [Ne, map_eq_zero]; exact hμ₁
  have hιμ₂ : ι μ₂ ≠ 0 := by rw [Ne, map_eq_zero]; exact hμ₂
  have hιν₁ : ι ν₁ ≠ 0 := by rw [Ne, map_eq_zero]; exact hν₁
  have hιν₂ : ι ν₂ ≠ 0 := by rw [Ne, map_eq_zero]; exact hν₂
  set Bmat : Matrix (Fin 2) (Fin 2) K₂ :=
    ι ν₂ • (1 : Matrix (Fin 2) (Fin 2) K₂) + (ι ν₁ - ι ν₂) • vecMulVec (ι ∘ c) (ι ∘ ψ) with hBmat
  have hψc' : ι (ψ 0) * ι (c 0) + ι (ψ 1) * ι (c 1) = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, hψc, map_one]
  have hdetB : Bmat.det = ι ν₁ * ι ν₂ := by
    rw [hBmat, Matrix.det_fin_two]
    simp [Matrix.vecMulVec_apply]
    linear_combination (ι ν₂ * (ι ν₁ - ι ν₂)) * hψc'
  let A' : SpecialLinearGroup (Fin 2) K₂ := ⟨s • diagonal ![ι μ₁, ι μ₂], by
    rw [Matrix.det_smul, Matrix.det_diagonal, Fin.prod_univ_two]
    simp only [Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hss⟩
  let B' : SpecialLinearGroup (Fin 2) K₂ := ⟨s' • Bmat, by
    rw [Matrix.det_smul, hdetB]
    simp only [Fintype.card_fin]
    linear_combination hss'⟩
  have hinvA : (s * ι μ₁)⁻¹ = s * ι μ₂ :=
    (eq_inv_of_mul_eq_one_right (by linear_combination hss : s * ι μ₁ * (s * ι μ₂) = 1)).symm
  have hinvB : (s' * ι ν₁)⁻¹ = s' * ι ν₂ :=
    (eq_inv_of_mul_eq_one_right (by linear_combination hss' : s' * ι ν₁ * (s' * ι ν₂) = 1)).symm
  have hAP : ((A' : Matrix (Fin 2) (Fin 2) K₂)) * (1 : Matrix (Fin 2) (Fin 2) K₂) =
      1 * diagonal ![s * ι μ₁, (s * ι μ₁)⁻¹] := by
    rw [hinvA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A']
  have hμsq : (s * ι μ₁) ^ 2 = ι (μ₁ / μ₂) := by
    rw [map_div₀, eq_div_iff hιμ₂]
    linear_combination ι μ₁ * hss
  have hνsq : (s' * ι ν₁) ^ 2 = ι (ν₁ / ν₂) := by
    rw [map_div₀, eq_div_iff hιν₂]
    linear_combination ι ν₁ * hss'
  have hord : ∀ x : K, orderOf (ι x) = orderOf x := fun x =>
    orderOf_injective ι.toMonoidHom hιinj x
  let PB : Matrix (Fin 2) (Fin 2) K₂ := !![ι (c 0), ι (ψ 1); ι (c 1), -ι (ψ 0)]
  have hPB : PB.det ≠ 0 := by
    have : PB.det = -1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination (-1 : K₂) * hψc'
    rw [this]
    exact neg_ne_zero.mpr one_ne_zero
  have hBP : ((B' : Matrix (Fin 2) (Fin 2) K₂)) * PB =
      PB * diagonal ![s' * ι ν₁, (s' * ι ν₁)⁻¹] := by
    rw [hinvB]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B', Bmat, PB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
        Matrix.vecMulVec_apply, Matrix.one_apply] <;>
      first | ring1 | linear_combination (s' * ι (c 0) * (ι ν₁ - ι ν₂)) * hψc' |
        linear_combination (s' * ι (c 1) * (ι ν₁ - ι ν₂)) * hψc'
  have hB3 : 2 < orderOf (B' : PSL2MatrixGroup K₂) := by
    rw [orderOf_mk_eq hPB hBP, hνsq, hord]
    omega
  have hno : ∀ x : Fin 2 → K₂, x ≠ 0 →
      (∃ c : K₂, (A' : Matrix (Fin 2) (Fin 2) K₂) *ᵥ x = c • x) →
      (∃ c : K₂, (B' : Matrix (Fin 2) (Fin 2) K₂) *ᵥ x = c • x) → False := by
    rintro x hx0 ⟨e, he⟩ ⟨e', he'⟩
    have hA0 := congrFun he 0
    have hA1 := congrFun he 1
    have hB0 := congrFun he' 0
    have hB1 := congrFun he' 1
    simp [A', B', Bmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecMulVec_apply,
      Matrix.one_apply] at hA0 hA1 hB0 hB1
    have hιc0 : ι (c 0) ≠ 0 := by rw [Ne, map_eq_zero]; exact hc0
    have hιc1 : ι (c 1) ≠ 0 := by rw [Ne, map_eq_zero]; exact hc1
    have hιψ0 : ι (ψ 0) ≠ 0 := by rw [Ne, map_eq_zero]; exact hψ0
    have hιψ1 : ι (ψ 1) ≠ 0 := by rw [Ne, map_eq_zero]; exact hψ1
    have hιν : ι ν₁ - ι ν₂ ≠ 0 := by
      rw [← map_sub, Ne, map_eq_zero, sub_eq_zero]
      exact hν12
    by_cases hx0' : x 0 = 0
    · have hx1' : x 1 ≠ 0 := fun h1 => hx0 (by
        ext i
        fin_cases i <;> simp [hx0', h1])
      rw [hx0'] at hB0
      have : s' * ((ι ν₁ - ι ν₂) * (ι (c 0) * ι (ψ 1))) * x 1 = 0 := by
        linear_combination hB0
      exact (mul_ne_zero (mul_ne_zero hs'0 (mul_ne_zero hιν (mul_ne_zero hιc0 hιψ1))) hx1') this
    · by_cases hx1' : x 1 = 0
      · rw [hx1'] at hB1
        have : s' * ((ι ν₁ - ι ν₂) * (ι (c 1) * ι (ψ 0))) * x 0 = 0 := by
          linear_combination hB1
        exact (mul_ne_zero (mul_ne_zero hs'0 (mul_ne_zero hιν (mul_ne_zero hιc1 hιψ0))) hx0')
          this
      · have h1 : s * ι μ₁ = e := hA0.resolve_right hx0'
        have h2 : s * ι μ₂ = e := hA1.resolve_right hx1'
        apply hμ12
        apply hιinj
        exact mul_left_cancel₀ hs0 (h1.trans h2.symm)
  have hmk : ∀ (g : GL (Fin 2) K) (u : K₂) (hu : u ≠ 0) (T : SpecialLinearGroup (Fin 2) K₂),
      ((T : Matrix (Fin 2) (Fin 2) K₂) = u • (g : Matrix (Fin 2) (Fin 2) K).map ι) →
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL T) = gl2ProjExt K p g := by
    intro g u hu T hT
    show _ = ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map ι g)
    symm
    rw [ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 u hu, Units.ext ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hT, coe_map_algebraMap]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
    fin_cases j <;> simp [mul_comm] <;> exact Or.inl rfl
  have hAJ : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A') ∈ Y.map (gl2ProjExt K p) := by
    rw [hmk A s hs0 A' (by
      rw [hAm]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [A'])]
    exact Subgroup.mem_map_of_mem _ hA
  have hBJ : ProjGenLinGroup.mk (SpecialLinearGroup.toGL B') ∈ Y.map (gl2ProjExt K p) := by
    rw [hmk B s' hs'0 B' (by
      rw [hBm]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [B', Bmat, Matrix.vecMulVec_apply])]
    exact Subgroup.mem_map_of_mem _ hB
  have hJ := card_ge_of_pgl_pair_gen hK₂ (Y.map (gl2ProjExt K p))
    ((Y.map_le_range (gl2ProjExt K p)).trans range_gl2ProjExt_le) hAJ hBJ
    (P := (1 : Matrix (Fin 2) (Fin 2) K₂)) (Matrix.det_one.trans_ne one_ne_zero) hAP
    (by rw [hμsq, hord]; exact hμ6) (by rw [hμsq, hord]; exact hsf) (by rw [hμsq, hord]; exact hcop)
    hB3 hno
  rwa [card_map_eq_of_ker_eq _ _ ker_gl2ProjExt Y] at hJ

theorem sl2_le_of_pair_lin {f : ℕ} (hKq : Nat.card K = p ^ f)
    (hq4 : 4 ≤ p ^ f) (Y : Subgroup (GL (Fin 2) K)) {μ₁ μ₂ ν₁ ν₂ : K} {c ψ : Fin 2 → K}
    (hμ₁ : μ₁ ≠ 0) (hμ₂ : μ₂ ≠ 0) (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0)
    (hψc : ψ 0 * c 0 + ψ 1 * c 1 = 1) (hc0 : c 0 ≠ 0) (hc1 : c 1 ≠ 0) (hψ0 : ψ 0 ≠ 0)
    (hψ1 : ψ 1 ≠ 0) (hμ6 : 6 ≤ orderOf (μ₁ / μ₂)) (hsf : SubfieldOK p f (orderOf (μ₁ / μ₂)))
    (hν3 : 3 ≤ orderOf (ν₁ / ν₂)) {A B : GL (Fin 2) K}
    (hAm : (A : Matrix (Fin 2) (Fin 2) K) = diagonal ![μ₁, μ₂])
    (hBm : (B : Matrix (Fin 2) (Fin 2) K) =
      ν₂ • (1 : Matrix (Fin 2) (Fin 2) K) + (ν₁ - ν₂) • vecMulVec c ψ)
    (hA : A ∈ Y) (hB : B ∈ Y) :
    ∀ g : SpecialLinearGroup (Fin 2) K, SpecialLinearGroup.toGL g ∈ Y := by
  refine sl2_le_of_card_ge_lin (by rw [hKq]; exact hq4) Y ?_
  rw [hKq]
  exact card_image_ge_lin hKq Y hμ₁ hμ₂ hν₁ hν₂ hψc hc0 hc1 hψ0 hψ1 hμ6 hsf hν3 hAm hBm hA hB

end Ext

end CFSG.RankThree.PartTwo.Sec14.L3PGLU27
