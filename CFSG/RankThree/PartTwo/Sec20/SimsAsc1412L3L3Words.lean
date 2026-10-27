module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutClass
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Unipotent

variable {F : Type} [Field F]

private theorem det_one_add_smul_vecMulVec (u w : Fin 3 → F) (c : F) :
    (1 + c • Matrix.vecMulVec u w).det = 1 + c * (w ⬝ᵥ u) := by
  rw [Matrix.det_fin_three]
  simp [Matrix.vecMulVec_apply, Matrix.one_apply, dotProduct, Fin.sum_univ_succ]
  ring

private theorem vecMulVec_mul_self_of_dotProduct_eq_zero {u w : Fin 3 → F} (h : w ⬝ᵥ u = 0) :
    Matrix.vecMulVec u w * Matrix.vecMulVec u w = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, h, zero_smul, Matrix.vecMulVec_zero]

private theorem exists_ne_mul_ne_zero {u w : Fin 3 → F} (hu : u ≠ 0) (hw : w ≠ 0)
    (h : w ⬝ᵥ u = 0) : ∃ i j : Fin 3, i ≠ j ∧ u i * w j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  simp only [Pi.zero_apply] at hi hj
  have hij : i = j := by
    by_contra hne
    exact hj ((mul_eq_zero.1 (hcon i j hne)).resolve_left hi)
  subst hij
  have hwk : ∀ k, k ≠ i → w k = 0 := fun k hk =>
    (mul_eq_zero.1 (hcon i k (Ne.symm hk))).resolve_left hi
  have hsum : w ⬝ᵥ u = w i * u i := by
    rw [dotProduct, Finset.sum_eq_single i]
    · intro k _ hk
      rw [hwk k hk, zero_mul]
    · simp
  rw [hsum] at h
  exact mul_ne_zero hj hi h

private def l3wUnip (N : Matrix (Fin 3) (Fin 3) F) (hdet : ∀ c : F, (1 + c • N).det = 1) (c : F) :
    SL(3, F) :=
  ⟨1 + c • N, hdet c⟩

variable {N : Matrix (Fin 3) (Fin 3) F} {hdet : ∀ c : F, (1 + c • N).det = 1}

private theorem coe_l3wUnip (c : F) :
    ((l3wUnip N hdet c : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 + c • N :=
  rfl

private theorem l3wUnip_mul (hN : N * N = 0) (c d : F) :
    l3wUnip N hdet c * l3wUnip N hdet d = l3wUnip N hdet (c + d) := by
  have h : (1 + c • N) * (1 + d • N) = 1 + (c + d) • N := by
    have e : (1 + c • N) * (1 + d • N) = 1 + (c + d) • N + (c * d) • (N * N) := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
      module
    rw [e, hN, smul_zero, add_zero]
  exact Subtype.ext h

private theorem l3wUnip_zero : l3wUnip N hdet 0 = 1 :=
  Subtype.ext (by
    show (1 + (0 : F) • N : Matrix (Fin 3) (Fin 3) F) = 1
    rw [zero_smul, add_zero])

private theorem l3wUnip_inv (hN : N * N = 0) (c : F) :
    (l3wUnip N hdet c)⁻¹ = l3wUnip N hdet (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [l3wUnip_mul hN, add_neg_cancel, l3wUnip_zero])

private theorem l3wUnip_pow (hN : N * N = 0) (c : F) (n : ℕ) :
    l3wUnip N hdet c ^ n = l3wUnip N hdet (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, l3wUnip_zero]
  | succ n ih => rw [pow_succ, ih, l3wUnip_mul hN, Nat.cast_succ, add_mul, one_mul]

private theorem proj_l3wUnip_ne_one (hoff : ∃ i j, i ≠ j ∧ N i j ≠ 0) {c : F} (hc : c ≠ 0) :
    proj 3 F (l3wUnip N hdet c) ≠ 1 := by
  intro h
  obtain ⟨c', -, hc'⟩ := proj_eq_one_iff.1 h
  obtain ⟨i, j, hij, hN⟩ := hoff
  have := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) hc'
  simp only [coe_l3wUnip, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
    Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, smul_eq_mul, zero_add] at this
  exact hN ((mul_eq_zero.1 this).resolve_left hc)

private theorem orderOf_proj_l3wUnip {p : ℕ} [Fact p.Prime] (hp : (p : F) = 0) (hN : N * N = 0)
    (hoff : ∃ i j, i ≠ j ∧ N i j ≠ 0) {c : F} (hc : c ≠ 0) :
    orderOf (proj 3 F (l3wUnip N hdet c)) = p := by
  refine orderOf_eq_prime ?_ (proj_l3wUnip_ne_one hoff hc)
  rw [← map_pow, l3wUnip_pow hN, hp, zero_mul, l3wUnip_zero, map_one]

private theorem exists_ne_zero_dotProduct_mulVec_eq_zero {p : ℕ} [Fact p.Prime] [Fintype F]
    [CharP F p] (B : Matrix (Fin 3) (Fin 3) F) :
    ∃ u : Fin 3 → F, u ≠ 0 ∧ u ⬝ᵥ (B *ᵥ u) = 0 := by
  classical
  set P : MvPolynomial (Fin 3) F :=
    ∑ i, ∑ j, MvPolynomial.C (B i j) * MvPolynomial.X i * MvPolynomial.X j with hP
  have hval : ∀ u : Fin 3 → F, MvPolynomial.eval u P = u ⬝ᵥ (B *ᵥ u) := by
    intro u
    simp only [hP, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, dotProduct,
      Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdeg : P.totalDegree < Fintype.card (Fin 3) := by
    have hle : P.totalDegree ≤ 2 := by
      rw [hP]
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
      calc (MvPolynomial.C (B i j) * MvPolynomial.X i * MvPolynomial.X j :
            MvPolynomial (Fin 3) F).totalDegree
          ≤ (MvPolynomial.C (B i j) * MvPolynomial.X i : MvPolynomial (Fin 3) F).totalDegree +
            (MvPolynomial.X j : MvPolynomial (Fin 3) F).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
        _ ≤ ((MvPolynomial.C (B i j) : MvPolynomial (Fin 3) F).totalDegree +
              (MvPolynomial.X i : MvPolynomial (Fin 3) F).totalDegree) +
            (MvPolynomial.X j : MvPolynomial (Fin 3) F).totalDegree := by
            gcongr
            exact MvPolynomial.totalDegree_mul _ _
        _ = 2 := by
            rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X,
              MvPolynomial.totalDegree_X]
    rw [Fintype.card_fin]
    omega
  have hdvd := char_dvd_card_solutions p hdeg
  by_contra hall
  push Not at hall
  have hsub : Subsingleton { x : Fin 3 → F // MvPolynomial.eval x P = 0 } := by
    constructor
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    have hx0 : x = 0 := by
      by_contra h
      exact hall x h (by rw [← hval]; exact hx)
    have hy0 : y = 0 := by
      by_contra h
      exact hall y h (by rw [← hval]; exact hy)
    exact Subtype.ext (hx0.trans hy0.symm)
  have hne : Nonempty { x : Fin 3 → F // MvPolynomial.eval x P = 0 } :=
    ⟨⟨0, by rw [hval, Matrix.mulVec_zero, dotProduct_zero]⟩⟩
  have hcard : Fintype.card { x : Fin 3 → F // MvPolynomial.eval x P = 0 } = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨hne.some, fun y => Subsingleton.elim _ _⟩
  rw [hcard] at hdvd
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hdvd)

private theorem exists_word_conjAut_dualAut {p : ℕ} [Fact p.Prime] [Fintype F] [CharP F p]
    (hp : (p : F) = 0) (h2 : (2 : F) ≠ 0) {A : GL (Fin 3) F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A) :
    ∃ x : projectiveSL 3 F, p ∣ orderOf ((conjAut 3 F A * dualAut 3 F) x * x⁻¹) := by
  set B : Matrix (Fin 3) (Fin 3) F := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hB
  have hAB : (A : Matrix (Fin 3) (Fin 3) F) * B = 1 := by
    rw [hB, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBT : Bᵀ = B := by
    have h1 : Bᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
      have := congrArg Matrix.transpose hAB
      rwa [Matrix.transpose_mul, hA, Matrix.transpose_one] at this
    calc Bᵀ = Bᵀ * ((A : Matrix (Fin 3) (Fin 3) F) * B) := by rw [hAB, mul_one]
      _ = (Bᵀ * (A : Matrix (Fin 3) (Fin 3) F)) * B := by rw [mul_assoc]
      _ = B := by rw [h1, one_mul]
  obtain ⟨u, hu0, hu⟩ := exists_ne_zero_dotProduct_mulVec_eq_zero (p := p) B
  set w : Fin 3 → F := B *ᵥ u with hw
  have huw : w ⬝ᵥ u = 0 := by rw [hw, dotProduct_comm]; exact hu
  have hAw : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ w = u := by
    rw [hw, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  have huB : u ᵥ* B = w := by
    have := Matrix.vecMul_transpose B u
    rwa [hBT] at this
  set N : Matrix (Fin 3) (Fin 3) F := Matrix.vecMulVec u w with hN
  have hdet : ∀ c : F, (1 + c • N).det = 1 := fun c => by
    rw [hN, det_one_add_smul_vecMulVec, huw, mul_zero, add_zero]
  have hN2 : N * N = 0 := vecMulVec_mul_self_of_dotProduct_eq_zero huw
  have hANB : (A : Matrix (Fin 3) (Fin 3) F) * Nᵀ * B = N := by
    rw [hN, Matrix.transpose_vecMulVec, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hAw, huB]
  have hoff : ∃ i j : Fin 3, i ≠ j ∧ N i j ≠ 0 := by
    have hw0 : w ≠ 0 := by
      intro h
      apply hu0
      rw [← hAw, h, Matrix.mulVec_zero]
    obtain ⟨i, j, hij, h⟩ := exists_ne_mul_ne_zero hu0 hw0 huw
    exact ⟨i, j, hij, by rwa [hN, Matrix.vecMulVec_apply]⟩
  have hconj : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
      ((l3wUnip N hdet (-1) : SL(3, F)).transpose) = l3wUnip N hdet (-1) := by
    have hmat : (A : Matrix (Fin 3) (Fin 3) F) * (1 + (-1 : F) • N)ᵀ * B = 1 + (-1 : F) • N := by
      rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, mul_add, add_mul,
        mul_one, Matrix.mul_smul, Matrix.smul_mul, hANB, hAB]
    exact Subtype.ext ((coe_slConjugation A _).trans hmat)
  refine ⟨proj 3 F (l3wUnip N hdet 1), ?_⟩
  have key : (conjAut 3 F A * dualAut 3 F) (proj 3 F (l3wUnip N hdet 1)) *
      (proj 3 F (l3wUnip N hdet 1))⁻¹ = proj 3 F (l3wUnip N hdet (-2)) := by
    rw [MulAut.mul_apply, dualAut_proj, l3wUnip_inv hN2, conjAut_proj, hconj, ← map_inv,
      l3wUnip_inv hN2, ← map_mul, l3wUnip_mul hN2]
    norm_num
  rw [key, orderOf_proj_l3wUnip hp hN2 hoff (neg_ne_zero.2 h2)]

private theorem proj_eq_one_of_coe_eq_smul_one (S : SL(3, F)) {a : F}
    (h : (S : Matrix (Fin 3) (Fin 3) F) = a • 1) : proj 3 F S = 1 := by
  have hdet : a ^ 3 = 1 := by
    have h1 := S.2
    rw [h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    exact h1
  have ha : a ≠ 0 := fun h0 => by simp [h0] at hdet
  refine proj_eq_one_iff.2 ⟨Units.mk0 a ha, Units.ext (by simpa using hdet), ?_⟩
  rw [h, Units.val_mk0, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

private theorem exists_word_conj_of_sq_eq_one {p : ℕ} [Fact p.Prime] (hp : (p : F) = 0)
    (h2 : (2 : F) ≠ 0) {s : projectiveSL 3 F} (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    ∃ x : projectiveSL 3 F, p ∣ orderOf (MulAut.conj s x * x⁻¹) := by
  obtain ⟨S, rfl⟩ := proj_surjective 3 F s
  have hS2 : S * S ∈ scalars 3 F := by
    rw [← proj_eq_one_iff, map_mul, ← sq]
    exact hs2
  obtain ⟨c, hc3, hcS⟩ := hS2
  have hc3' : (c : F) ^ 3 = 1 := by
    have := congrArg Units.val hc3
    simpa using this
  set r : F := (c : F) ^ 2 with hr
  have hr2 : r * r = (c : F) := by
    calc r * r = (c : F) ^ 3 * (c : F) := by rw [hr]; ring
      _ = (c : F) := by rw [hc3', one_mul]
  set S₀ : Matrix (Fin 3) (Fin 3) F := (S : Matrix (Fin 3) (Fin 3) F) with hS₀
  have hSS : S₀ * S₀ = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have h := hcS
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at h
    exact h
  have hMmMp : (S₀ - r • 1) * (S₀ + r • 1) = 0 := by
    have : (S₀ - r • 1) * (S₀ + r • 1) = S₀ * S₀ - (r * r) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    rw [this, hSS, hr2, sub_self]
  have hSMp : S₀ * (S₀ + r • 1) = r • (S₀ + r • 1) := by
    simp only [mul_add, mul_smul_comm, mul_one, smul_add, smul_smul]
    rw [hSS, hr2]
    module
  have hMmS : (S₀ - r • 1) * S₀ = (-r) • (S₀ - r • 1) := by
    simp only [sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]
    rw [hSS, neg_mul, hr2]
    module
  have hMp : S₀ + r • 1 ≠ 0 := by
    intro h
    exact hs1 (proj_eq_one_of_coe_eq_smul_one S (a := -r)
      (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h))
  have hMm : S₀ - r • 1 ≠ 0 := by
    intro h
    exact hs1 (proj_eq_one_of_coe_eq_smul_one S (a := r) (sub_eq_zero.1 h))
  obtain ⟨a₀, j, hj⟩ : ∃ a j, (S₀ + r • 1) a j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hMp (Matrix.ext fun a j => hcon a j)
  obtain ⟨i, b₀, hi⟩ : ∃ i b, (S₀ - r • 1) i b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hMm (Matrix.ext fun i b => hcon i b)
  set u : Fin 3 → F := (S₀ + r • 1) *ᵥ Pi.single j 1 with hu
  set w : Fin 3 → F := Pi.single i 1 ᵥ* (S₀ - r • 1) with hw
  have hu0 : u ≠ 0 := fun h => hj (by
    have := congrFun h a₀
    simpa [hu, Matrix.mulVec_single_one] using this)
  have hw0 : w ≠ 0 := fun h => hi (by
    have := congrFun h b₀
    simpa [hw, Matrix.single_one_vecMul] using this)
  have hSu : S₀ *ᵥ u = r • u := by
    rw [hu, Matrix.mulVec_mulVec, hSMp, Matrix.smul_mulVec]
  have hwS : w ᵥ* S₀ = (-r) • w := by
    rw [hw, Matrix.vecMul_vecMul, hMmS, Matrix.vecMul_smul]
  have huw : w ⬝ᵥ u = 0 := by
    rw [hw, hu, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hMmMp, Matrix.zero_mulVec,
      dotProduct_zero]
  set N : Matrix (Fin 3) (Fin 3) F := Matrix.vecMulVec u w with hN
  have hdet : ∀ c : F, (1 + c • N).det = 1 := fun c => by
    rw [hN, det_one_add_smul_vecMulVec, huw, mul_zero, add_zero]
  have hN2 : N * N = 0 := vecMulVec_mul_self_of_dotProduct_eq_zero huw
  have hSN : S₀ * N = r • N := by
    rw [hN, Matrix.mul_vecMulVec, hSu, Matrix.smul_vecMulVec]
  have hNS : N * S₀ = (-r) • N := by
    rw [hN, Matrix.vecMulVec_mul, hwS, Matrix.vecMulVec_smul]
  have hanti : S₀ * N = -(N * S₀) := by
    rw [hSN, hNS, neg_smul, neg_neg]
  have hoff : ∃ a b : Fin 3, a ≠ b ∧ N a b ≠ 0 := by
    obtain ⟨a, b, hab, h⟩ := exists_ne_mul_ne_zero hu0 hw0 huw
    exact ⟨a, b, hab, by rwa [hN, Matrix.vecMulVec_apply]⟩
  have hconj : ∀ c : F, S * l3wUnip N hdet c * S⁻¹ = l3wUnip N hdet (-c) := fun c => by
    have hSS' : S₀ * ((S⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 :=
      congrArg Subtype.val (mul_inv_cancel S)
    have h1 : S₀ * N * ((S⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = -N := by
      rw [hanti, Matrix.neg_mul, mul_assoc, hSS', mul_one]
    have hmat : S₀ * (1 + c • N) * ((S⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        1 + (-c) • N := by
      rw [mul_add, add_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul, h1, hSS', smul_neg,
        neg_smul]
    exact Subtype.ext hmat
  refine ⟨proj 3 F (l3wUnip N hdet 1), ?_⟩
  have key : MulAut.conj (proj 3 F S) (proj 3 F (l3wUnip N hdet 1)) *
      (proj 3 F (l3wUnip N hdet 1))⁻¹ = proj 3 F (l3wUnip N hdet (-2)) := by
    rw [MulAut.conj_apply, ← map_inv, ← map_inv, ← map_mul, ← map_mul, hconj,
      l3wUnip_inv hN2, ← map_mul, l3wUnip_mul hN2]
    norm_num
  rw [key, orderOf_proj_l3wUnip hp hN2 hoff (neg_ne_zero.2 h2)]

end Unipotent

theorem exists_dvd_orderOf_mul_inv_projectiveSL3 {F : Type} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p) (hp5 : 5 ≤ p) (β : MulAut (projectiveSL 3 F))
    (hβ : orderOf β = 2) : ∃ x : projectiveSL 3 F, p ∣ orderOf (β x * x⁻¹) := by
  have : Fintype F := Fintype.ofFinite F
  have hKF : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F p := charP_of_card_eq_prime hKF
  have hp0 : (p : F) = 0 := CharP.cast_eq_zero F p
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff F p 2).1 h')
    omega
  have hβ2 : β * β = 1 := by rw [← sq, ← hβ, pow_orderOf_eq_one]
  rcases CFSG.QuasithinUnique.Ch1.classify_involution hF h2 β hβ2 with ⟨g, hg⟩ | ⟨A, hA, hβA⟩
  ·
    have hβs : β = MulAut.conj g⁻¹ := by
      ext x
      rw [hg x, MulAut.conj_apply, inv_inv]
    have hZ := CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (k := F) (n := 3) le_rfl
    have hs2 : g⁻¹ ^ 2 = 1 := by
      have hc : MulAut.conj (g⁻¹ ^ 2) = 1 := by rw [map_pow, ← hβs, ← hβ, pow_orderOf_eq_one]
      have hmem : g⁻¹ ^ 2 ∈ Subgroup.center (projectiveSL 3 F) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have e := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ y) hc
        simp only [MulAut.conj_apply, MulAut.one_apply] at e
        calc y * g⁻¹ ^ 2 = g⁻¹ ^ 2 * y * (g⁻¹ ^ 2)⁻¹ * g⁻¹ ^ 2 := by rw [e]
          _ = g⁻¹ ^ 2 * y := by group
      rw [hZ, Subgroup.mem_bot] at hmem
      exact hmem
    have hs1 : g⁻¹ ≠ 1 := fun h1 => by
      rw [h1, map_one] at hβs
      rw [hβs, orderOf_one] at hβ
      exact absurd hβ (by norm_num)
    rw [hβs]
    exact exists_word_conj_of_sq_eq_one hp0 h2 hs2 hs1
  ·
    rw [hβA]
    exact exists_word_conjAut_dualAut hp0 h2 hA

end CFSG.RankThree.PartTwo.Sec20
