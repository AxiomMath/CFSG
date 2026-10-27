module

public import CFSG.RankThree.GF2n.Smith81.OrthE1KFSmall
public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcClOrth

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem omegaComm_ne_zero {F : Type} [Field F] {v : Fin 2 → F} (hv : v ≠ 0) :
    v 0 ≠ 0 ∨ v 1 ≠ 0 := by
  by_contra h
  push_neg at h
  apply hv
  ext i
  fin_cases i <;> simp [h.1, h.2]

theorem omegaComm_diag_eq {F : Type} [Field F] [CharP F 2] {p q a b c d : F}
    (hpq : p ≠ 0 ∨ q ≠ 0) (hA1 : a * p + b * q = p) (hA2 : c * p + d * q = q)
    (hA3 : a * d - b * c = 1) : a = d := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hDp : ((a - 1) * (d - 1) - b * c) * p = 0 := by
    linear_combination (d - 1) * hA1 - b * hA2
  have hDq : ((a - 1) * (d - 1) - b * c) * q = 0 := by
    linear_combination (a - 1) * hA2 - c * hA1
  have hD : (a - 1) * (d - 1) - b * c = 0 := by
    rcases hpq with hp | hq
    · exact (mul_eq_zero.1 hDp).resolve_right hp
    · exact (mul_eq_zero.1 hDq).resolve_right hq
  have hsum : a + d = 0 := by
    linear_combination (-1 : F) * hD + hA3 + two
  linear_combination hsum - d * two

theorem omegaComm_off_eq {F : Type} [Field F] [CharP F 2] {p q a b c d a' b' c' d' : F}
    (hpq : p ≠ 0 ∨ q ≠ 0)
    (hA1 : a * p + b * q = p) (hA2 : c * p + d * q = q) (hA3 : a * d - b * c = 1)
    (hB1 : a' * p + b' * q = p) (hB2 : c' * p + d' * q = q) (hB3 : a' * d' - b' * c' = 1) :
    b * c' = c * b' := by
  have had : a = d := omegaComm_diag_eq hpq hA1 hA2 hA3
  have had' : a' = d' := omegaComm_diag_eq hpq hB1 hB2 hB3
  have hp : (b * c' - c * b') * p = 0 := by
    linear_combination b * hB2 + (1 - d') * hA1 - b' * hA2 - (1 - d) * hB1 +
      (1 - a) * p * had' - (1 - a') * p * had
  have hq : (b * c' - c * b') * q = 0 := by
    linear_combination c' * hA1 + (1 - a) * hB2 - c * hB1 - (1 - a') * hA2 +
      (1 - a) * q * had' - (1 - a') * q * had
  have h0 : b * c' - c * b' = 0 := by
    rcases hpq with hp' | hq'
    · exact (mul_eq_zero.1 hp).resolve_right hp'
    · exact (mul_eq_zero.1 hq).resolve_right hq'
  exact sub_eq_zero.1 h0

theorem omegaComm_mat_comm {F : Type} [Field F] [CharP F 2] {v : Fin 2 → F} (hv : v ≠ 0)
    {A B : Matrix (Fin 2) (Fin 2) F} (hA : A.det = 1) (hB : B.det = 1)
    (hAv : A *ᵥ v = v) (hBv : B *ᵥ v = v) : A * B = B * A := by
  have hpq := omegaComm_ne_zero hv
  have hA1 : A 0 0 * v 0 + A 0 1 * v 1 = v 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hAv 0
  have hA2 : A 1 0 * v 0 + A 1 1 * v 1 = v 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hAv 1
  have hB1 : B 0 0 * v 0 + B 0 1 * v 1 = v 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hBv 0
  have hB2 : B 1 0 * v 0 + B 1 1 * v 1 = v 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hBv 1
  have hA3 : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h := hA
    rw [Matrix.det_fin_two] at h
    exact h
  have hB3 : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    have h := hB
    rw [Matrix.det_fin_two] at h
    exact h
  have hkey := omegaComm_off_eq hpq hA1 hA2 hA3 hB1 hB2 hB3
  have had := omegaComm_diag_eq hpq hA1 hA2 hA3
  have had' := omegaComm_diag_eq hpq hB1 hB2 hB3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination hkey
    | linear_combination (-1 : F) * hkey
    | linear_combination B 0 1 * had - A 0 1 * had'
    | linear_combination A 1 0 * had' - B 1 0 * had

theorem omegaComm_sl2_fix {F : Type} [Field F] [CharP F 2] {v : Fin 2 → F} (hv : v ≠ 0)
    (x y : ↥(StatedSL 2 F)) (hx : kfsMat x *ᵥ v = v) (hy : kfsMat y *ᵥ v = v) :
    x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  exact omegaComm_mat_comm (A := kfsMat x) (B := kfsMat y) hv
    (CFSG.Open.StatedAPI.det_of_mem_statedSL x.2)
    (CFSG.Open.StatedAPI.det_of_mem_statedSL y.2) hx hy

theorem omegaComm_sl2_pgroup {F : Type} [Field F] [Finite F] [CharP F 2]
    (Q : Subgroup ↥(StatedSL 2 F)) (hQ : IsPGroup 2 ↥Q) :
    ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  obtain ⟨v, hv, hfix⟩ := kfs_exists_fixed Q hQ
  intro x hx y hy
  exact omegaComm_sl2_fix hv x y (hfix x hx) (hfix y hy)

theorem omegaComm_prod {G₁ G₂ : Type} [Group G₁] [Group G₂]
    (h₁ : ∀ Q : Subgroup G₁, IsPGroup 2 ↥Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (h₂ : ∀ Q : Subgroup G₂, IsPGroup 2 ↥Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (Q : Subgroup (G₁ × G₂)) (hQ : IsPGroup 2 ↥Q) :
    ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  intro x hx y hy
  have c₁ := h₁ (Q.map (MonoidHom.fst G₁ G₂)) (hQ.map (MonoidHom.fst G₁ G₂)) x.1
    (Subgroup.mem_map_of_mem _ hx) y.1 (Subgroup.mem_map_of_mem _ hy)
  have c₂ := h₂ (Q.map (MonoidHom.snd G₁ G₂)) (hQ.map (MonoidHom.snd G₁ G₂)) x.2
    (Subgroup.mem_map_of_mem _ hx) y.2 (Subgroup.mem_map_of_mem _ hy)
  exact Prod.ext (by simpa only [Prod.fst_mul] using c₁)
    (by simpa only [Prod.snd_mul] using c₂)

theorem omegaComm_of_mulEquiv {H G : Type} [Group H] [Group G] {Ω : Subgroup H}
    (e : ↥Ω ≃* G) (hG : ∀ Q : Subgroup G, IsPGroup 2 ↥Q → ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (P : Subgroup H) (hPΩ : P ≤ Ω) (hP : IsPGroup 2 ↥P) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  intro x hx y hy
  have hP' : IsPGroup 2 ↥(P.comap Ω.subtype) := hP.comap_subtype
  have hQ : IsPGroup 2 ↥((P.comap Ω.subtype).map (e.toMonoidHom)) := hP'.map _
  have hx' : (⟨x, hPΩ hx⟩ : ↥Ω) ∈ P.comap Ω.subtype := hx
  have hy' : (⟨y, hPΩ hy⟩ : ↥Ω) ∈ P.comap Ω.subtype := hy
  have key := hG _ hQ (e ⟨x, hPΩ hx⟩) (Subgroup.mem_map_of_mem _ hx')
    (e ⟨y, hPΩ hy⟩) (Subgroup.mem_map_of_mem _ hy')
  have h2 : (⟨x, hPΩ hx⟩ : ↥Ω) * ⟨y, hPΩ hy⟩ = ⟨y, hPΩ hy⟩ * ⟨x, hPΩ hx⟩ :=
    e.injective (by rw [map_mul, map_mul]; exact key)
  exact congrArg Subtype.val h2

theorem omegaComm_charP_two (F : Type) [Field F] [Finite F] {q : ℕ}
    (hq : Nat.card F = 2 ^ q) : CharP F 2 := by
  letI := Fintype.ofFinite F
  obtain ⟨p, hc, n, hp, hcard⟩ := FiniteField.card' F
  rw [← Nat.card_eq_fintype_card, hq] at hcard
  have hdvd : p ∣ 2 ^ q := by
    rw [hcard]
    exact dvd_pow_self p n.ne_zero
  have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst h2
  exact hc

section Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem omega_comm_plus (h4 : 4 ≤ Nat.card K) :
    ∀ P : Subgroup (GL (Fin 2 ⊕ Fin 2) K), P ≤ StatedOmega (StatedQuadPlus 2 K) →
      IsPGroup 2 P → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  intro P hPΩ hP
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  have hG : ∀ Q : Subgroup (↥(StatedSL 2 K) × ↥(StatedSL 2 K)), IsPGroup 2 ↥Q →
      ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x :=
    omegaComm_prod (fun Q hQ => omegaComm_sl2_pgroup Q hQ)
      (fun Q hQ => omegaComm_sl2_pgroup Q hQ)
  exact omegaComm_of_mulEquiv e hG P hPΩ hP

theorem omega_comm_minus {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ P : Subgroup (GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K),
      P ≤ StatedOmega (StatedQuadMinus 2 K b c) → IsPGroup 2 P →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  intro P hPΩ hP
  obtain ⟨F, hF, hFin, hcardF, ⟨e⟩⟩ := exists_statedOmega_quadMinus_two_mulEquiv hirr
  obtain ⟨k, -, hk⟩ := kfs_card_eq_two_pow K
  have hcard2 : Nat.card F = 2 ^ (k * 2) := by
    rw [hcardF, hk, ← pow_mul]
  haveI : CharP F 2 := omegaComm_charP_two F hcard2
  exact omegaComm_of_mulEquiv e (fun Q hQ => omegaComm_sl2_pgroup Q hQ) P hPΩ hP

theorem isometry_index_plus (h4 : 4 ≤ Nat.card K) :
    Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)) =
      2 * Nat.card (StatedOmega (StatedQuadPlus 2 K)) := by
  have h1 : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 K)) =
      2 * Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - 1) := by
    have := CFSG.LocalAnalysis.RankFourTheoremC.crossExcCl_card_isoPlus (K := K) 1
    norm_num [Finset.Icc_self] at this
    exact this
  rw [h1, kfs_natCard_plus h4]
  ring

theorem isometry_index_minus {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) =
      2 * Nat.card (StatedOmega (StatedQuadMinus 2 K b c)) := by
  have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus (1 + 1) K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (1 * (1 + 1)) * ((Nat.card K : ℤ) ^ (1 + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 1, ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    have := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus hirr 1
    simp only [← pow_mul] at this
    exact this
  have h1 : Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)) =
      2 * Nat.card K ^ 2 * (Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 - 1) := by
    have := CFSG.LocalAnalysis.RankFourTheoremC.crossExcCl_card_isoMinus (m := 1) hO
    norm_num [Finset.Icc_self] at this
    exact this
  rw [h1, kfs_natCard_minus hirr]
  have hq2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have hq4 : 1 ≤ Nat.card K ^ 4 := Nat.one_le_pow _ _ Nat.card_pos
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hq2, Nat.cast_sub hq4]
  ring

end Omega

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end
