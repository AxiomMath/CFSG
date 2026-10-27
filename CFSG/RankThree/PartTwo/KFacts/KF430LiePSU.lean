module

public import CFSG.RankThree.PartTwo.KFacts.KF430LiePSL
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2SU4
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofLieP
public import CFSG.RankThree.PartTwo.Sec21.Item211Res4ProofPlusU4
public import CFSG.RankThree.PartTwo.Sec4.E27.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzUE
public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalTransport

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF430

open Matrix
open CFSG.Open (StatedSU StatedProj)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

section Planes

variable {K : Type} [Field K]

@[expose] def hypJ : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

@[expose] def uniIdx : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 0]
  invFun := Sum.elim ![0, 1] ![3, 2]
  left_inv := by decide
  right_inv := by decide

@[expose] noncomputable def reindexGLU : GL (Fin 2 ⊕ Fin 2) K ≃* GL (Fin 4) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K uniIdx.symm).toRingEquiv.toMulEquiv

theorem coe_reindexGLU (A : GL (Fin 2 ⊕ Fin 2) K) :
    ((reindexGLU A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix uniIdx uniIdx := rfl

theorem reindexGLU_scalar (c : Kˣ) :
    reindexGLU (Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
  apply Units.ext
  rw [coe_reindexGLU, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.scalar_apply, submatrix_diagonal_equiv]
  rfl

theorem antidiag_four_eq :
    antidiag 4 = (planeMat (hypJ (K := K)) hypJ).submatrix uniIdx uniIdx := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag, planeMat, uniIdx, hypJ, Fin.rev]

variable (σ : K ≃+* K)

theorem conjTr_planeMat (M N : Matrix (Fin 2) (Fin 2) K) :
    ((planeMat M N).map σ)ᵀ = planeMat (M.map σ)ᵀ (N.map σ)ᵀ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeMat]

theorem conjTr_swapMat : ((swapMat (F := K)).map σ)ᵀ = swapMat := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [swapMat]

theorem conjTr_reindex_mul (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    conjTr σ (A.submatrix uniIdx uniIdx) * antidiag 4 * A.submatrix uniIdx uniIdx =
      ((A.map σ)ᵀ * planeMat hypJ hypJ * A).submatrix uniIdx uniIdx := by
  rw [antidiag_four_eq, conjTr, ← Matrix.submatrix_map, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

theorem mem_SU_reindexGLU {M N : Matrix (Fin 2) (Fin 2) K} (hM : M.det = 1) (hN : N.det = 1)
    (hMu : (M.map σ)ᵀ * hypJ * M = hypJ) (hNu : (N.map σ)ᵀ * hypJ * N = hypJ)
    (g : GL (Fin 2 ⊕ Fin 2) K)
    (hg : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = planeMat M N) :
    reindexGLU g ∈ SU σ 4 := by
  rw [mem_SU, coe_reindexGLU, hg]
  refine ⟨by rw [det_submatrix_equiv_self, det_planeMat, hM, hN, one_mul], ?_⟩
  rw [conjTr_reindex_mul, conjTr_planeMat, planeMat_mul, planeMat_mul, hMu, hNu,
    antidiag_four_eq]

theorem swap_mem_SU : reindexGLU (swapGL (F := K)) ∈ SU σ 4 := by
  rw [mem_SU, coe_reindexGLU]
  refine ⟨by rw [det_submatrix_equiv_self]; exact det_swapMat, ?_⟩
  rw [conjTr_reindex_mul]
  change (((swapMat (F := K)).map σ)ᵀ * planeMat hypJ hypJ * swapMat).submatrix uniIdx uniIdx = _
  rw [conjTr_swapMat, swapMat_mul_planeMat, mul_assoc, swapMat_mul_self, mul_one,
    antidiag_four_eq]

end Planes

section Two

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def uniU (ω : Kˣ) : Matrix (Fin 2) (Fin 2) K := diagonal ![(ω : K), ((ω⁻¹ : Kˣ) : K)]

@[expose] def uniX (c d : Kˣ) : Matrix (Fin 2) (Fin 2) K := !![0, (d : K); (c : K), 0]

@[expose] def uniXinv (c d : Kˣ) : Matrix (Fin 2) (Fin 2) K :=
  !![0, ((c⁻¹ : Kˣ) : K); ((d⁻¹ : Kˣ) : K), 0]

theorem uniU_pow (ω : Kˣ) (n : ℕ) :
    uniU ω ^ n = diagonal ![((ω ^ n : Kˣ) : K), (((ω⁻¹) ^ n : Kˣ) : K)] := by
  rw [uniU, diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem uniU_cube {ω : Kˣ} (hω : ω ^ 3 = 1) : uniU ω ^ 3 = 1 := by
  rw [uniU_pow, hω, inv_pow, hω, inv_one, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem uniX_mul_inv (c d : Kˣ) : uniX c d * uniXinv c d = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniX, uniXinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem uniX_inv_mul (c d : Kˣ) : uniXinv c d * uniX c d = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniX, uniXinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem uniX_mul_uniU {ω : Kˣ} (hω : ω ^ 3 = 1) (c d : Kˣ) :
    uniX c d * uniU ω = uniU ω ^ 2 * uniX c d := by
  have h2 : ((ω ^ 2 : Kˣ) : K) = ((ω⁻¹ : Kˣ) : K) := by
    congr 1
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hω]
  have h2' : (((ω⁻¹) ^ 2 : Kˣ) : K) = (ω : K) := by
    congr 1
    rw [inv_pow, inv_eq_iff_eq_inv, eq_inv_iff_mul_eq_one, ← pow_succ, hω]
  rw [uniU_pow, h2, h2']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniX, uniU, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem det_uniU (ω : Kˣ) : (uniU ω).det = 1 := by
  simp [uniU, det_diagonal, Fin.prod_univ_two]

theorem det_uniX {c d : Kˣ} (hcd : (c : K) * d = -1) : (uniX c d).det = 1 := by
  rw [uniX, det_fin_two_of]
  linear_combination -hcd

theorem uniU_unitary {ω : Kˣ} (hσω : σ (ω : K) = ω) :
    ((uniU ω).map σ)ᵀ * hypJ * uniU ω = hypJ := by
  have hσω' : σ ((ω⁻¹ : Kˣ) : K) = ((ω⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hσω]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniU, hypJ, Matrix.mul_apply, Fin.sum_univ_two, hσω, hσω']

theorem uniX_unitary {c d : Kˣ} (h1 : σ (c : K) * d = 1) (h2 : σ (d : K) * c = 1) :
    ((uniX c d).map σ)ᵀ * hypJ * uniX c d = hypJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniX, hypJ, Matrix.mul_apply, Fin.sum_univ_two, h1, h2]

theorem one_unitary : (((1 : Matrix (Fin 2) (Fin 2) K)).map σ)ᵀ * hypJ * 1 = hypJ := by
  rw [Matrix.map_one (σ : K → K) (map_zero σ) (map_one σ), transpose_one, one_mul, mul_one]

theorem uniU_ind {ω : Kˣ} (hω : orderOf ω = 3) (i j : ZMod 3) (c : K)
    (h : planeMat (uniU ω ^ i.val) (uniU ω ^ j.val) = diagonal (fun _ => c)) :
    i = 0 ∧ j = 0 := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have key : ∀ k : ZMod 3, (ω : K) ^ k.val = ((ω : K) ^ k.val)⁻¹ → k = 0 := by
    intro k hk
    have hne : (ω : K) ^ k.val ≠ 0 := pow_ne_zero _ ω.ne_zero
    have hk2 : (ω : K) ^ k.val * (ω : K) ^ k.val = 1 := by
      calc (ω : K) ^ k.val * (ω : K) ^ k.val = (ω : K) ^ k.val * ((ω : K) ^ k.val)⁻¹ := by
            rw [← hk]
        _ = 1 := mul_inv_cancel₀ hne
    have hk' : ω ^ (k.val + k.val) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_add, hk2, Units.val_one]
    have hdvd : orderOf ω ∣ k.val + k.val := orderOf_dvd_of_pow_eq_one hk'
    rw [hω] at hdvd
    have : 3 ∣ k.val := by omega
    have hk3 : k.val < 3 := ZMod.val_lt k
    have hk0 : k.val = 0 := by omega
    exact (ZMod.val_eq_zero k).1 hk0
  rw [uniU_pow, uniU_pow] at h
  have e00 := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
  have e11 := congrFun (congrFun h (Sum.inr 0)) (Sum.inr 0)
  have f00 := congrFun (congrFun h (Sum.inl 1)) (Sum.inl 1)
  have f11 := congrFun (congrFun h (Sum.inr 1)) (Sum.inr 1)
  simp [planeMat] at e00 e11 f00 f11
  exact ⟨key i (e00.trans e11.symm), key j (f00.trans f11.symm)⟩

end Two

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem sylow_comm_of_mulEquiv (e : X ≃* Y)
    (h : ∀ (Q : Sylow 3 Y) (a b : Y), a ∈ (Q : Subgroup Y) → b ∈ (Q : Subgroup Y) → a * b = b * a)
    (P : Sylow 3 X) (a b : X) (ha : a ∈ (P : Subgroup X)) (hb : b ∈ (P : Subgroup X)) :
    a * b = b * a := by
  have hP : IsPGroup 3 ((P : Subgroup X).map e.toMonoidHom) := P.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have := h Q (e a) (e b) (hQ ⟨a, ha, rfl⟩) (hQ ⟨b, hb, rfl⟩)
  apply e.injective
  rw [map_mul, map_mul, this]

theorem card_le_of_mulEquiv (e : X ≃* Y)
    (h : ∀ E : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 9)
    (E : Subgroup X) (hE : CFSG.Assembly.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have := h (E.map e.toMonoidHom) (isElemAbelian_map e.toMonoidHom hE)
  rwa [Subgroup.card_map_of_injective e.injective] at this

end Transport

section E9

variable {p : ℕ} [Fact p.Prime]

abbrev KU (p : ℕ) [Fact p.Prime] : Type := GaloisField p (2 * 1)

theorem card_KU : Nat.card (KU p) = (p ^ 1) ^ 2 := by
  rw [GaloisField.card p (2 * 1) (by norm_num), pow_one, mul_one]

theorem exists_pow_sub_one_eq_neg_one (hp2 : p ≠ 2) : ∃ c : (KU p)ˣ, c ^ (p - 1) = -1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨r, hr⟩ := hp.odd_of_ne_two hp2
  have hr1 : 1 ≤ r := by
    have := hp.two_le
    omega
  have hcard : Nat.card (KU p)ˣ = p ^ 2 - 1 := by
    rw [Nat.card_units, card_KU, pow_one]
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (KU p)ˣ)
  have hp1 : p - 1 = 2 * r := by omega
  have hsq : p ^ 2 - 1 = (r + 1) * (p - 1) * 2 := by
    rw [hp1, hr]
    apply Nat.sub_eq_of_eq_add
    ring
  have hord : orderOf γ = (r + 1) * (p - 1) * 2 := by rw [hγ, hcard, hsq]
  set y := γ ^ ((r + 1) * (p - 1)) with hy
  have hy2 : y * y = 1 := by
    have e : y * y = γ ^ ((r + 1) * (p - 1) * 2) := by
      rw [hy, ← pow_add]
      congr 1
      ring
    rw [e, ← hord, pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · rw [hp1]
      positivity
    · rw [hord]
      have : 0 < (r + 1) * (p - 1) := by rw [hp1]; positivity
      omega
  have hy' : y = -1 := by
    have h := congrArg Units.val hy2
    rw [Units.val_mul, Units.val_one] at h
    rcases mul_self_eq_one_iff.1 h with h1 | h1
    · exact absurd (Units.ext h1) hy1
    · exact Units.ext (by rw [h1, Units.val_neg, Units.val_one])
  exact ⟨γ ^ (r + 1), by rw [← pow_mul]; exact hy'⟩

theorem e9Move_projSU4 (hp3 : 3 < p) (hp1 : p % 3 = 1) :
    E9Move (CFSG.PGLModel.projSU 4 p 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : p.Prime := Fact.out
  set σ := unitaryInvolution (KU p) p 1 with hσdef
  obtain ⟨e2⟩ := CFSG.ClassicalGroups.SUnThreeLocal.statedProj_statedSU_mulEquiv_SU_of_card
    (F := KU p) (p := p) (f := 1) card_KU 4
  let E : CFSG.PGLModel.projSU 4 p 1 ≃* CFSG.PGLModel.projImage (SU σ 4) :=
    (CFSG.PGLModel.projSUEquivStatedProj 4 p 1).trans
      (e2.trans (CFSG.Open.StatedAPI.mapMkEquivStatedProj (SU σ 4)).symm)
  have hsyl₀ : ∀ (Q : Sylow 3 (CFSG.PGLModel.projSU 4 p 1)) (a b : CFSG.PGLModel.projSU 4 p 1),
      a ∈ (Q : Subgroup _) → b ∈ (Q : Subgroup _) → a * b = b * a := by
    rw [← CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 4 p 1]
    exact CFSG.RankThree.PartTwo.Sec4.Ronan148L.comm_sylow_projImage fun P hP =>
      CFSG.RankThree.PartTwo.Sec4.Ronan148L.comm_of_isPGroup_SU4_mod_one hp1 P hP
  have hle₀ : ∀ E' : Subgroup (CFSG.PGLModel.projSU 4 p 1), CFSG.Assembly.IsElemAbelian 3 E' →
      Nat.card E' ≤ 9 := by
    intro E' hE'
    have hrank := CFSG.RankThree.PartTwo.Sec4.Res417Four.pRank_projSU_four_le_two (p := p) (f := 1)
      (by omega) le_rfl (by rw [pow_one]; exact hp1)
    haveI : CFSG.IsElementaryAbelian 3 E' :=
      { toIsMulCommutative := hE'.1
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
          Subtype.ext (by simpa using hE'.2 g g.2) }
    have hP : IsPGroup 3 E' := fun x => ⟨1, Subtype.ext (by simpa using hE'.2 x x.2)⟩
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hkr := CFSG.RankThree.PartOne.le_pRank_of_card' (by norm_num) E' inferInstance hk
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hkr.trans hrank)
      _ = 9 := by norm_num
  have hsyl := sylow_comm_of_mulEquiv E.symm hsyl₀
  have hle := card_le_of_mulEquiv E.symm hle₀
  haveI : Finite (CFSG.PGLModel.projImage (SU σ 4)) := inferInstance
  have h3p : 3 ∣ p - 1 := by omega
  obtain ⟨ω, hω⟩ := CFSG.RankThree.Chevalley.exists_units_orderOf_eq_of_dvd_card_sub_one
    (k := KU p) Nat.prime_three (by
      rw [card_KU, pow_one, show p ^ 2 - 1 = (p - 1) * (p + 1) by
        zify [(by omega : 1 ≤ p), Nat.one_le_pow 2 p (by omega)]
        ring]
      exact Dvd.dvd.mul_right h3p _)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hωp : ω ^ p = ω := by
    have h1 : ω ^ (p - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hω ▸ h3p)
    calc ω ^ p = ω ^ (p - 1) * ω := by rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
      _ = ω := by rw [h1, one_mul]
  have hσω : σ (ω : KU p) = ω := by
    rw [hσdef, unitaryInvolution_apply, pow_one, ← Units.val_pow_eq_pow_val, hωp]
  obtain ⟨c, hc⟩ := exists_pow_sub_one_eq_neg_one (p := p) (by omega)
  have hcp : c ^ p = -c := by
    calc c ^ p = c ^ (p - 1) * c := by rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
      _ = -c := by rw [hc, neg_one_mul]
  have hσc : σ (c : KU p) = -(c : KU p) := by
    rw [hσdef, unitaryInvolution_apply, pow_one, ← Units.val_pow_eq_pow_val, hcp, Units.val_neg]
  set d : (KU p)ˣ := -c⁻¹ with hd
  have hcd : (c : KU p) * d = -1 := by
    rw [hd, Units.val_neg, mul_neg, Units.mul_inv]
  have h1 : σ (c : KU p) * d = 1 := by
    rw [hσc, hd, Units.val_neg, neg_mul_neg, Units.mul_inv]
  have h2 : σ (d : KU p) * c = 1 := by
    rw [hd, Units.val_neg, map_neg, Units.val_inv_eq_inv_val, map_inv₀, hσc, inv_neg, neg_neg,
      inv_mul_cancel₀ c.ne_zero]
  obtain ⟨a, b, w, ⟨ha, hb, hw⟩, ha3, hb3, hab, hind, hsa, hsb, hwa, hwb⟩ :=
    exists_std_gen (uniU ω) (uniX c d) (uniXinv c d) (uniU_cube hω3) (uniX_mul_inv c d)
      (uniX_inv_mul c d) (uniX_mul_uniU hω3 c d) (uniU_ind hω)
  have hA := mem_SU_reindexGLU σ (det_uniU ω) det_one (uniU_unitary σ hσω) (one_unitary σ) a ha
  have hB := mem_SU_reindexGLU σ det_one (det_uniU ω) (one_unitary σ) (uniU_unitary σ hσω) b hb
  have hW := mem_SU_reindexGLU σ (det_uniX hcd) det_one (uniX_unitary σ h1 h2) (one_unitary σ)
    w hw
  refine E9Move.of_mulEquiv E (e9Move_projImage_of_mats hsyl hle hA hB (swap_mem_SU σ) hW
    (by rw [← map_pow, ha3, map_one]) (by rw [← map_pow, hb3, map_one])
    (by rw [← map_mul, hab, map_mul]) ?_
    (by rw [← map_inv, ← map_mul, ← map_mul, hsa])
    (by rw [← map_inv, ← map_mul, ← map_mul, hsb])
    (by rw [← map_inv, ← map_mul, ← map_mul, hwa, map_pow])
    (by rw [← map_inv, ← map_mul, ← map_mul, hwb]))
  intro i j c' hc'
  rw [← map_pow, ← map_pow, ← map_mul, ← reindexGLU_scalar] at hc'
  exact hind i j c' (reindexGLU.injective hc')

theorem concl_projSU4 (hp3 : 3 < p) (hp1 : p % 3 = 1) :
    Concl (CFSG.PGLModel.projSU 4 p 1) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 (KU p) :=
    ⟨Fact.out, le_rfl, GaloisField.card p (2 * 1) (by norm_num)⟩
  have e := (CFSG.PGLModel.projSUEquivStatedProj 4 p 1).trans
    (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.statedProjEquivPrimeFormOne h
      (n := 4) (by norm_num))
  refine ⟨inner_of_mulEquiv e fun σ hσ =>
      CFSG.RankThree.PartTwo.Sec4.E27.primeFormP_prime_order_three_inner h hp3 σ
        (by rw [← hσ]; exact pow_orderOf_eq_one σ), ?_, e9Move_projSU4 hp3 hp1⟩
  rw [← CFSG.PGLModel.projImage_statedSU 4 p 1,
    ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU card_KU 4]
  exact CFSG.RankThree.PartTwo.Sec21.Item211Res4Proof.center_projImage_SUid_eq_bot

theorem kf430LiePSU_holds : KF430LiePSU := by
  intro p _ hp hp1 L _ _ ⟨e⟩
  exact Concl.of_mulEquiv e (concl_projSU4 hp hp1)

end E9

end CFSG.RankThree.PartTwo.KFacts.KF430
