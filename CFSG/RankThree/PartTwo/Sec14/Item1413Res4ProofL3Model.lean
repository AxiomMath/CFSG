module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjFieldTwo
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofSignal
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec14.Proof1413Res4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

variable {K : Type} [Field K]

@[expose] def sgnAt (i j : Fin 3) : Kˣ := if j = i then 1 else -1

@[expose] def tInv (i : Fin 3) : GL (Fin 3) K := diagUnits (sgnAt i 0) (sgnAt i 1) (sgnAt i 2)

theorem sgnAt_mul_self (i j : Fin 3) : (sgnAt i j : Kˣ) * sgnAt i j = 1 := by
  unfold sgnAt
  split_ifs <;> simp

theorem tInv_mul_self (i : Fin 3) : (tInv i : GL (Fin 3) K) * tInv i = 1 := by
  rw [tInv, diagUnits_mul, sgnAt_mul_self, sgnAt_mul_self, sgnAt_mul_self, diagUnits_one]

theorem cycThree_conj_tInv (i : Fin 3) :
    (cycThree : GL (Fin 3) K) * tInv i * cycThree⁻¹ = tInv (i + 1) := by
  rw [tInv, cycThree_conj_diagUnits, tInv]
  fin_cases i <;> simp [sgnAt]

theorem cycThree_pow_conj_tInv (i k : Fin 3) :
    (cycThree : GL (Fin 3) K) ^ (k : ℕ) * tInv i * (cycThree ^ (k : ℕ))⁻¹ = tInv (i + k) := by
  fin_cases k
  · simp
  · simpa using cycThree_conj_tInv (K := K) i
  · have h := cycThree_conj_tInv (K := K) (i + 1)
    rw [← cycThree_conj_tInv i] at h
    calc (cycThree : GL (Fin 3) K) ^ (((2 : Fin 3) : ℕ)) * tInv i *
          (cycThree ^ (((2 : Fin 3) : ℕ)))⁻¹ =
        cycThree * (cycThree * tInv i * cycThree⁻¹) * cycThree⁻¹ := by
          simp only [Fin.isValue, Fin.val_two, pow_two]
          group
      _ = tInv (i + 1 + 1) := h
      _ = tInv (i + 2) := by rw [add_assoc]; rfl

theorem diagUnits_comm (a b c a' b' c' : Kˣ) :
    diagUnits a b c * diagUnits a' b' c' = diagUnits a' b' c' * diagUnits a b c := by
  rw [diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b, mul_comm c]

theorem mk_commute_iff {x y : GL (Fin 3) K} :
    ProjGenLinGroup.mk x * ProjGenLinGroup.mk y = ProjGenLinGroup.mk y * ProjGenLinGroup.mk x ↔
      x * y * x⁻¹ * y⁻¹ ∈ StatedScalars (Fin 3) K := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
    mk_eq_one_iff_mem_statedScalars, commutatorElement_def]

theorem scalar_comm (u : Kˣ) (A : GL (Fin 3) K) :
    A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
  (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq

theorem det_diagTau {τ : K} (hτ : τ ^ 3 = 1) : GeneralLinearGroup.det (diagTau hτ) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_diagTau_eq_diagonal, Matrix.det_diagonal,
    Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, mul_one, Units.val_one]
  rw [← pow_succ']
  exact hτ

variable {p f : ℕ} {π : Bool}

theorem exists_decomp (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {m : GL (Fin 3) K} (hm : m ∈ slPi π 3 (p ^ f) K)
    (hcomm : ProjGenLinGroup.mk m * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk m) :
    ∃ k : Fin 3, ∃ a b : Kˣ, m = cycThree ^ (k : ℕ) * diagUnits a b (a * b)⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set d := diagTau hτ with hd
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  obtain ⟨lam, hlam⟩ := mk_commute_iff.mp hcomm
  have hmd : m * d * m⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * d := by
    rw [hlam]
    group
  have hlam3 : lam ^ 3 = 1 := by
    have h := congrArg GeneralLinearGroup.det hmd
    rw [map_mul, map_mul, map_inv, map_mul, Proof142Res.det_scalar_units, det_diagTau hτ,
      mul_one, mul_one, mul_inv_cancel] at h
    exact h.symm
  have hlam3' : (lam : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hlam3, Units.val_one]
  have hτu3 : τu ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hτ,
    Units.val_one])
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, lam = τu ^ (2 * (k : ℕ)) := by
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hlam3' with h | h | h
    · exact ⟨0, Units.ext (by simp [h])⟩
    · refine ⟨2, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, h]
      simp only [Fin.isValue, Fin.val_two]
      rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, hτ, one_mul, pow_one]
    · refine ⟨1, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, h]
      simp
  have hck := cycThree_pow_conj_diagTau hτ hτ0 (k : ℕ)
  rw [← hτu, ← hk] at hck
  have hmd' : m * d * m⁻¹ = cycThree ^ (k : ℕ) * d * (cycThree ^ (k : ℕ))⁻¹ := by
    rw [hmd, hck]
  set n := (cycThree ^ (k : ℕ))⁻¹ * m with hn
  have hnd : n * d = d * n := by
    have h2 : n * d * n⁻¹ = d := by
      calc n * d * n⁻¹ = (cycThree ^ (k : ℕ))⁻¹ * (m * d * m⁻¹) * cycThree ^ (k : ℕ) := by
            rw [hn]
            group
        _ = (cycThree ^ (k : ℕ))⁻¹ * (cycThree ^ (k : ℕ) * d * (cycThree ^ (k : ℕ))⁻¹) *
            cycThree ^ (k : ℕ) := by rw [hmd']
        _ = d := by group
    calc n * d = n * d * n⁻¹ * n := by group
      _ = d * n := by rw [h2]
  have hnL : n ∈ slPi π 3 (p ^ f) K :=
    mul_mem (inv_mem (pow_mem (cycThree_mem_slPi hπ) _)) hm
  have hnC : n ∈ slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {d} :=
    Subgroup.mem_inf.mpr ⟨hnL, Subgroup.mem_centralizer_singleton_iff.mpr hnd⟩
  rw [hd, centralizer_diagTau_eq hK hq hτ hτ1] at hnC
  obtain ⟨⟨a, b⟩, hab⟩ := hnC
  refine ⟨k, (a : Kˣ), (b : Kˣ), ?_⟩
  have hab' : n = diagUnits (a : Kˣ) (b : Kˣ) ((a : Kˣ) * (b : Kˣ))⁻¹ := hab.symm
  calc m = cycThree ^ (k : ℕ) * n := by rw [hn]; group
    _ = _ := by rw [hab']

theorem neg_one_ne_one_units (h2 : (2 : K) ≠ 0) : (-1 : Kˣ) ≠ 1 := by
  intro h
  apply h2
  have h' := congrArg Units.val h
  simp only [Units.val_neg, Units.val_one] at h'
  linear_combination -h'

theorem mk_tInv_ne (h2 : (2 : K) ≠ 0) {i j : Fin 3} (hij : i ≠ j) :
    ProjGenLinGroup.mk (tInv i : GL (Fin 3) K) ≠ ProjGenLinGroup.mk (tInv j) := by
  intro h
  have h' : ProjGenLinGroup.mk ((tInv i : GL (Fin 3) K) * tInv j) = 1 := by
    rw [map_mul, h, ← map_mul, tInv_mul_self, map_one]
  rw [tInv, tInv, diagUnits_mul] at h'
  obtain ⟨h0, h1⟩ := eq_of_diagUnits_mem_statedScalars (mk_eq_one_iff_mem_statedScalars.mp h')
  have hne := neg_one_ne_one_units h2
  fin_cases i <;> fin_cases j <;> simp [sgnAt] at hij h0 h1 <;>
    first | exact hne h0 | exact hne h0.symm | exact hne h1 | exact hne h1.symm

theorem tInv_eq_one (h2 : (2 : K) = 0) (i : Fin 3) : (tInv i : GL (Fin 3) K) = 1 := by
  have hn : (-1 : Kˣ) = 1 := Units.ext (by
    simp only [Units.val_neg, Units.val_one]
    linear_combination -h2)
  rw [tInv, ← diagUnits_one]
  fin_cases i <;> simp [sgnAt, hn]

theorem commute_of_mk_commute_tInv {m : GL (Fin 3) K} {i : Fin 3}
    (h : ProjGenLinGroup.mk m * ProjGenLinGroup.mk (tInv i) =
      ProjGenLinGroup.mk (tInv i) * ProjGenLinGroup.mk m) :
    m * tInv i = tInv i * m := by
  obtain ⟨lam, hlam⟩ := mk_commute_iff.mp h
  have hmt : m * tInv i * m⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * tInv i := by
    rw [hlam]
    group
  have hsq : lam ^ 2 = 1 := by
    have e1 : (m * tInv i * m⁻¹) ^ 2 = 1 := by
      rw [pow_two, show m * tInv i * m⁻¹ * (m * tInv i * m⁻¹) = m * (tInv i * tInv i) * m⁻¹ by
        group, tInv_mul_self, mul_one, mul_inv_cancel]
    have hc : Commute (GeneralLinearGroup.scalar (Fin 3) lam) (tInv i : GL (Fin 3) K) :=
      (scalar_comm lam (tInv i)).symm
    rw [hmt, hc.mul_pow, pow_two (tInv i : GL (Fin 3) K), tInv_mul_self, mul_one, ← map_pow]
      at e1
    exact scalar_injective_three (by rw [e1, map_one])
  have hdett : GeneralLinearGroup.det (tInv i : GL (Fin 3) K) = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, tInv, coe_diagUnits_eq, Matrix.det_fin_three]
    fin_cases i <;> simp [sgnAt]
  have hcube : lam ^ 3 = 1 := by
    have e := congrArg GeneralLinearGroup.det hmt
    rw [map_mul, map_mul, map_inv, map_mul, Proof142Res.det_scalar_units, hdett, mul_one,
      mul_one, mul_inv_cancel] at e
    exact e.symm
  have hlam1 : lam = 1 := by
    calc lam = lam ^ 3 * (lam ^ 2)⁻¹ := by group
      _ = 1 := by rw [hcube, hsq, inv_one, mul_one]
  rw [hlam1, map_one, one_mul] at hmt
  calc m * tInv i = m * tInv i * m⁻¹ * m := by group
    _ = tInv i * m := by rw [hmt]

theorem entry_eq_zero_of_commute_tInv (h2 : (2 : K) ≠ 0) {m : GL (Fin 3) K} {i : Fin 3}
    (h : m * tInv i = tInv i * m) {a b : Fin 3} (hab : (a = i ∧ b ≠ i) ∨ (a ≠ i ∧ b = i)) :
    (m : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
  have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) a b) h
  simp only [Units.val_mul, tInv, coe_diagUnits, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at h'
  have hs : ∀ x : Fin 3, (![((sgnAt i 0 : Kˣ) : K), ((sgnAt i 1 : Kˣ) : K),
      ((sgnAt i 2 : Kˣ) : K)] x) = ((sgnAt i x : Kˣ) : K) := by
    intro x
    fin_cases x <;> rfl
  have hval : ∀ x : Fin 3, ((sgnAt i x : Kˣ) : K) = if x = i then 1 else -1 := by
    intro x
    unfold sgnAt
    split_ifs <;> simp
  have hd : ∀ x y : Fin 3, x = i → y ≠ i →
      ((sgnAt i y : Kˣ) : K) - ((sgnAt i x : Kˣ) : K) ≠ 0 := by
    intro x y hx hy
    have e1 : ((sgnAt i x : Kˣ) : K) = 1 := by simp [hval, hx]
    have e2 : ((sgnAt i y : Kˣ) : K) = -1 := by simp [hval, hy]
    rw [e1, e2]
    intro h0
    apply h2
    linear_combination -h0
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have e : (m : Matrix (Fin 3) (Fin 3) K) a b * (((sgnAt i b : Kˣ) : K) -
        ((sgnAt i a : Kˣ) : K)) = 0 := by
      have h'' : (m : Matrix (Fin 3) (Fin 3) K) a b * ((sgnAt i b : Kˣ) : K) =
          ((sgnAt i a : Kˣ) : K) * (m : Matrix (Fin 3) (Fin 3) K) a b := by
        have := h'
        rw [hs, hs] at this
        exact this
      rw [mul_sub, h'', mul_comm, sub_self]
    exact (mul_eq_zero.mp e).resolve_right (hd a b ha hb)
  · have e : (m : Matrix (Fin 3) (Fin 3) K) a b * (((sgnAt i a : Kˣ) : K) -
        ((sgnAt i b : Kˣ) : K)) = 0 := by
      have h'' : (m : Matrix (Fin 3) (Fin 3) K) a b * ((sgnAt i b : Kˣ) : K) =
          ((sgnAt i a : Kˣ) : K) * (m : Matrix (Fin 3) (Fin 3) K) a b := by
        have := h'
        rw [hs, hs] at this
        exact this
      rw [mul_sub, mul_comm _ ((sgnAt i a : Kˣ) : K), ← h'', sub_self]
    exact (mul_eq_zero.mp e).resolve_right (hd b a hb ha)

theorem mk_commute_of_tInv (h2 : (2 : K) ≠ 0) {τ : K} (hτ : τ ^ 3 = 1) {m : GL (Fin 3) K}
    {i j : Fin 3} (hij : i ≠ j)
    (hi : ProjGenLinGroup.mk m * ProjGenLinGroup.mk (tInv i) =
      ProjGenLinGroup.mk (tInv i) * ProjGenLinGroup.mk m)
    (hj : ProjGenLinGroup.mk m * ProjGenLinGroup.mk (tInv j) =
      ProjGenLinGroup.mk (tInv j) * ProjGenLinGroup.mk m) :
    ProjGenLinGroup.mk m * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk m := by
  have ci := commute_of_mk_commute_tInv hi
  have cj := commute_of_mk_commute_tInv hj
  have hoff : ∀ a b : Fin 3, a ≠ b → (m : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
    intro a b hab
    by_cases hai : a = i
    · exact entry_eq_zero_of_commute_tInv h2 ci (Or.inl ⟨hai, fun h => hab (hai.trans h.symm)⟩)
    by_cases hbi : b = i
    · exact entry_eq_zero_of_commute_tInv h2 ci (Or.inr ⟨hai, hbi⟩)
    by_cases haj : a = j
    · exact entry_eq_zero_of_commute_tInv h2 cj (Or.inl ⟨haj, fun h => hab (haj.trans h.symm)⟩)
    by_cases hbj : b = j
    · exact entry_eq_zero_of_commute_tInv h2 cj (Or.inr ⟨haj, hbj⟩)
    exfalso
    fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> simp_all
  have hmd : m * diagTau hτ = diagTau hτ * m := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diagTau_eq_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
    · rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hoff a b hab, zero_mul, mul_zero]
  rw [← map_mul, hmd, map_mul]

theorem mk_diagUnits_eq_of {a b c a' b' c' : Kˣ} (s : K) (h0 : (a : K) = s * a')
    (h1 : (b : K) = s * b') (h2 : (c : K) = s * c') :
    ProjGenLinGroup.mk (diagUnits a b c) = ProjGenLinGroup.mk (diagUnits a' b' c') := by
  refine mk_eq_of_coe_eq_smul (a := s) ?_
  rw [coe_diagUnits, coe_diagUnits]
  ext r t
  fin_cases r <;> fin_cases t <;> simp [h0, h1, h2]

theorem mk_eq_of_sq_eq_one (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {m : GL (Fin 3) K} (hm : m ∈ slPi π 3 (p ^ f) K)
    (hcomm : ProjGenLinGroup.mk m * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk m)
    (hsq : ProjGenLinGroup.mk m ^ 2 = 1) :
    ProjGenLinGroup.mk m = 1 ∨ ∃ i : Fin 3, ProjGenLinGroup.mk m = ProjGenLinGroup.mk (tInv i) := by
  obtain ⟨k, a, b, rfl⟩ := exists_decomp hK hq hτ hτ1 hm hcomm
  obtain ⟨μ, hμ⟩ : (cycThree ^ (k : ℕ) * diagUnits a b (a * b)⁻¹) ^ 2 ∈
      StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hsq]
  have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hμ
  have h11 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) hμ
  have h22 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) hμ
  fin_cases k
  ·
    simp only [Fin.isValue, pow_zero, one_mul] at h00 h11 h22 ⊢
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      pow_two, Units.val_mul, coe_diagUnits, Matrix.diagonal_mul_diagonal] at h00 h11 h22
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h00 h11 h22
    have hy : (b : K) = a ∨ (b : K) = -a := sq_eq_sq_iff_eq_or_eq_neg.mp (by
      rw [pow_two, pow_two, ← h11, ← h00])
    have hz : ((((a * b)⁻¹ : Kˣ)) : K) = a ∨ ((((a * b)⁻¹ : Kˣ)) : K) = -a :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [pow_two, pow_two, ← h22, ← h00])
    rcases hy with hy | hy <;> rcases hz with hz | hz
    · left
      have h1 : ProjGenLinGroup.mk (diagUnits (1 : Kˣ) 1 1) = 1 := by
        rw [diagUnits_one, map_one]
      rw [← h1]
      exact mk_diagUnits_eq_of (a : K) (by simp) (by rw [hy]; simp) (by rw [hz]; simp)
    · right
      exact ⟨2, mk_diagUnits_eq_of (-(a : K)) (by simp [sgnAt]) (by rw [hy]; simp [sgnAt])
        (by rw [hz]; simp [sgnAt])⟩
    · right
      exact ⟨1, mk_diagUnits_eq_of (-(a : K)) (by simp [sgnAt]) (by rw [hy]; simp [sgnAt])
        (by rw [hz]; simp [sgnAt])⟩
    · right
      exact ⟨0, mk_diagUnits_eq_of (a : K) (by simp [sgnAt]) (by rw [hy]; simp [sgnAt])
        (by rw [hz]; simp [sgnAt])⟩
  ·
    exfalso
    simp [pow_two, Units.val_mul, coe_cycThree, coe_diagUnits_eq, Matrix.mul_apply,
      Fin.sum_univ_three] at h00
  ·
    exfalso
    simp [pow_succ, Units.val_mul, coe_cycThree, coe_diagUnits_eq, Matrix.mul_apply,
      Fin.sum_univ_three] at h00

theorem diagTau_pow_eq {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) (j : ℕ) :
    diagTau hτ ^ j = diagUnits (Units.mk0 τ hτ0 ^ j) (Units.mk0 τ hτ0 ^ (2 * j)) 1 := by
  rw [diagTau_eq_diagUnits hτ hτ0]
  induction j with
  | zero => simp [diagUnits_one]
  | succ j ih =>
    rw [pow_succ, ih, diagUnits_mul, mul_one, ← pow_succ, mul_add, mul_one,
      pow_add (_ : Kˣ) (2 * j)]

theorem mk_mem_zpowers_of_cube {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {a b : Kˣ}
    (h3 : diagUnits a b (a * b)⁻¹ ^ 3 = 1) :
    ProjGenLinGroup.mk (diagUnits a b (a * b)⁻¹) ∈
      Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h00 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h3
  have h11 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) h3
  simp only [Units.val_pow_eq_pow_val, coe_diagUnits, Matrix.diagonal_pow, Units.val_one,
    Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h00 h11
  simp only [Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h11
  have hpow : ∀ j : ℕ, ProjGenLinGroup.mk (diagTau hτ) ^ j ∈
      Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) := fun j => Subgroup.npow_mem_zpowers _ j
  have key : ∀ (j : ℕ) (s : K), (a : K) = s * τ ^ j → (b : K) = s * τ ^ (2 * j) →
      s * ((a : K) * b) = 1 →
      ProjGenLinGroup.mk (diagUnits a b (a * b)⁻¹) ∈
        Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) := by
    intro j s e0 e1 e2
    have e2' : (((a * b)⁻¹ : Kˣ) : K) = s * ((1 : Kˣ) : K) := by
      rw [Units.val_one, mul_one, Units.val_inv_eq_inv_val, Units.val_mul]
      exact (eq_inv_of_mul_eq_one_left e2).symm
    rw [mk_diagUnits_eq_of (a' := Units.mk0 τ hτ0 ^ j) (b' := Units.mk0 τ hτ0 ^ (2 * j))
      (c' := 1) s (by rw [e0]; simp) (by rw [e1]; simp) e2', ← diagTau_pow_eq hτ hτ0, map_pow]
    exact hpow j
  have hexp : ∀ x : K, x ^ 3 = 1 → ∃ i : ℕ, i < 3 ∧ x = τ ^ i := by
    intro x hx
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hx with h | h | h
    · exact ⟨0, by norm_num, by simp [h]⟩
    · exact ⟨1, by norm_num, by simp [h]⟩
    · exact ⟨2, by norm_num, h⟩
  obtain ⟨i, hi, ha⟩ := hexp _ h00
  obtain ⟨l, hl, hb⟩ := hexp _ h11
  have htm : ∀ n : ℕ, τ ^ n = τ ^ (n % 3) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hτ, one_pow, one_mul]
  refine key ((2 * i + l) % 3) (τ ^ (6 - i - l)) ?_ ?_ ?_
  · rw [ha, ← pow_add]
    conv_rhs => rw [htm]
    congr 1
    omega
  · rw [hb, ← pow_add]
    conv_rhs => rw [htm]
    congr 1
    omega
  · rw [ha, hb, ← pow_add, ← pow_add, show 6 - i - l + (i + l) = 3 * 2 by omega, pow_mul, hτ,
      one_pow]

theorem mk_mul_ne_of_cube (h2 : (2 : K) ≠ 0) (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {m : GL (Fin 3) K} (hm : m ∈ slPi π 3 (p ^ f) K)
    (hcomm : ProjGenLinGroup.mk m * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk m) (h3 : m ^ 3 = 1)
    (hnot : ProjGenLinGroup.mk m ∉ Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)))
    (i : Fin 3) :
    ProjGenLinGroup.mk m * ProjGenLinGroup.mk (tInv i) ≠
      ProjGenLinGroup.mk (tInv i) * ProjGenLinGroup.mk m := by
  obtain ⟨k, a, b, rfl⟩ := exists_decomp hK hq hτ hτ1 hm hcomm
  intro hc
  by_cases hk : k = 0
  · subst hk
    simp only [Fin.isValue, Fin.val_zero, pow_zero, one_mul] at h3 hnot
    exact hnot (mk_mem_zpowers_of_cube hτ hτ1 h3)
  · have hD : diagUnits a b (a * b)⁻¹ * tInv i * (diagUnits a b (a * b)⁻¹)⁻¹ = tInv i := by
      rw [tInv, diagUnits_comm, mul_inv_cancel_right]
    have hconj : cycThree ^ (k : ℕ) * diagUnits a b (a * b)⁻¹ * tInv i *
        (cycThree ^ (k : ℕ) * diagUnits a b (a * b)⁻¹)⁻¹ = tInv (i + k) := by
      calc cycThree ^ (k : ℕ) * diagUnits a b (a * b)⁻¹ * tInv i *
            (cycThree ^ (k : ℕ) * diagUnits a b (a * b)⁻¹)⁻¹ =
          cycThree ^ (k : ℕ) * (diagUnits a b (a * b)⁻¹ * tInv i *
            (diagUnits a b (a * b)⁻¹)⁻¹) * (cycThree ^ (k : ℕ))⁻¹ := by group
        _ = tInv (i + k) := by rw [hD, cycThree_pow_conj_tInv]
    have heq : ProjGenLinGroup.mk (tInv (i + k) : GL (Fin 3) K) = ProjGenLinGroup.mk (tInv i) := by
      rw [← hconj, map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
    have hik : i + k ≠ i := by
      intro h
      apply hk
      have := congrArg (fun x => x - i) h
      simpa using this
    exact mk_tInv_ne h2 hik heq

theorem mk_conj (k z : GL (Fin 3) K) :
    ProjGenLinGroup.mk (k⁻¹ * z * k) =
      (ProjGenLinGroup.mk k)⁻¹ * ProjGenLinGroup.mk z * ProjGenLinGroup.mk k := by
  rw [map_mul, map_mul, map_inv]

theorem conj_inv_pow {Γ : Type*} [Group Γ] (κ X : Γ) (n : ℕ) :
    (κ⁻¹ * X * κ) ^ n = κ⁻¹ * X ^ n * κ := by
  simpa using conj_pow (a := κ⁻¹) (b := X) (i := n)

theorem conj_inv_zpow {Γ : Type*} [Group Γ] (κ X : Γ) (n : ℤ) :
    (κ⁻¹ * X * κ) ^ n = κ⁻¹ * X ^ n * κ := by
  simpa using conj_zpow (a := κ⁻¹) (b := X) (i := n)

theorem conj_commute {Γ : Type*} [Group Γ] (κ : Γ) {X Y : Γ} (h : X * Y = Y * X) :
    κ⁻¹ * X * κ * (κ⁻¹ * Y * κ) = κ⁻¹ * Y * κ * (κ⁻¹ * X * κ) := by
  rw [show κ⁻¹ * X * κ * (κ⁻¹ * Y * κ) = κ⁻¹ * (X * Y) * κ by group, h]
  group

theorem commute_of_conj {Γ : Type*} [Group Γ] (κ : Γ) {X Y : Γ}
    (h : κ⁻¹ * X * κ * (κ⁻¹ * Y * κ) = κ⁻¹ * Y * κ * (κ⁻¹ * X * κ)) : X * Y = Y * X := by
  have h' := conj_commute κ⁻¹ h
  simp only [inv_inv] at h'
  rwa [show κ * (κ⁻¹ * X * κ) * κ⁻¹ = X by group,
    show κ * (κ⁻¹ * Y * κ) * κ⁻¹ = Y by group] at h'

theorem exists_conj_diagTau (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : GL (Fin 3) K} (hg : g ∈ slPi π 3 (p ^ f) K)
    (hg3 : g ^ 3 = 1) (hgS : g ∉ StatedScalars (Fin 3) K) :
    ∃ k ∈ glPi π 3 (p ^ f) K, k⁻¹ * g * k = diagTau hτ := by
  have hgZ : g ∉ zPi π 3 (p ^ f) K := fun h =>
    hgS (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h)
  have hg1 : g ≠ 1 := fun h => hgS (h ▸ one_mem _)
  exact rank3II_4_10_three hK hq hτ hτ1 hg hgZ (orderOf_eq_prime hg3 hg1)

theorem conj_inv_mem_slPi (hK : PiField π p f K) {k m : GL (Fin 3) K}
    (hk : k ∈ glPi π 3 (p ^ f) K) (hm : m ∈ slPi π 3 (p ^ f) K) :
    k⁻¹ * m * k ∈ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := conj_mem_slPi hπ (inv_mem hk) hm
  rwa [inv_inv] at this

theorem exists_tInv_of_involution (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g k : GL (Fin 3) K} (hk : k ∈ glPi π 3 (p ^ f) K)
    (hkg : k⁻¹ * g * k = diagTau hτ) {m : GL (Fin 3) K} (hm : m ∈ slPi π 3 (p ^ f) K)
    (hmg : ProjGenLinGroup.mk m * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk m)
    (hm2 : ProjGenLinGroup.mk m ^ 2 = 1) (hm1 : ProjGenLinGroup.mk m ≠ 1) :
    (2 : K) ≠ 0 ∧ ∃ i : Fin 3, ProjGenLinGroup.mk (k⁻¹ * m * k) = ProjGenLinGroup.mk (tInv i) := by
  have hm' := conj_inv_mem_slPi hK hk hm
  have hcomm : ProjGenLinGroup.mk (k⁻¹ * m * k) * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk (k⁻¹ * m * k) := by
    rw [← hkg, mk_conj, mk_conj]
    exact conj_commute _ hmg
  have hsq : ProjGenLinGroup.mk (k⁻¹ * m * k) ^ 2 = 1 := by
    rw [mk_conj, conj_inv_pow, hm2]
    group
  have hne : ProjGenLinGroup.mk (k⁻¹ * m * k) ≠ 1 := by
    rw [mk_conj]
    intro h
    apply hm1
    have := congrArg (fun x => ProjGenLinGroup.mk k * x * (ProjGenLinGroup.mk k)⁻¹) h
    simpa [mul_assoc] using this
  rcases mk_eq_of_sq_eq_one hK hq hτ hτ1 hm' hcomm hsq with h | ⟨i, hi⟩
  · exact absurd h hne
  · refine ⟨fun h2 => hne ?_, i, hi⟩
    rw [hi, tInv_eq_one h2, map_one]

theorem commute_of_two_involutions (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : GL (Fin 3) K} (hg : g ∈ slPi π 3 (p ^ f) K)
    (hg3 : g ^ 3 = 1) (hgS : g ∉ StatedScalars (Fin 3) K) {s t : GL (Fin 3) K}
    (hs : s ∈ slPi π 3 (p ^ f) K) (ht : t ∈ slPi π 3 (p ^ f) K)
    (hsg : ProjGenLinGroup.mk s * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk s)
    (htg : ProjGenLinGroup.mk t * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk t)
    (hs2 : ProjGenLinGroup.mk s ^ 2 = 1) (ht2 : ProjGenLinGroup.mk t ^ 2 = 1)
    (hs1 : ProjGenLinGroup.mk s ≠ 1) (ht1 : ProjGenLinGroup.mk t ≠ 1)
    (hst : ProjGenLinGroup.mk s ≠ ProjGenLinGroup.mk t) {y : GL (Fin 3) K}
    (hys : ProjGenLinGroup.mk y * ProjGenLinGroup.mk s =
      ProjGenLinGroup.mk s * ProjGenLinGroup.mk y)
    (hyt : ProjGenLinGroup.mk y * ProjGenLinGroup.mk t =
      ProjGenLinGroup.mk t * ProjGenLinGroup.mk y) :
    ProjGenLinGroup.mk y * ProjGenLinGroup.mk g = ProjGenLinGroup.mk g * ProjGenLinGroup.mk y := by
  obtain ⟨k, hk, hkg⟩ := exists_conj_diagTau hK hq hτ hτ1 hg hg3 hgS
  obtain ⟨h2, i, hi⟩ := exists_tInv_of_involution hK hq hτ hτ1 hk hkg hs hsg hs2 hs1
  obtain ⟨-, j, hj⟩ := exists_tInv_of_involution hK hq hτ hτ1 hk hkg ht htg ht2 ht1
  have hij : i ≠ j := by
    rintro rfl
    apply hst
    have h := hi.trans hj.symm
    rw [mk_conj, mk_conj] at h
    have := congrArg (fun x => ProjGenLinGroup.mk k * x * (ProjGenLinGroup.mk k)⁻¹) h
    simpa [mul_assoc] using this
  have hyi : ProjGenLinGroup.mk (k⁻¹ * y * k) * ProjGenLinGroup.mk (tInv i) =
      ProjGenLinGroup.mk (tInv i) * ProjGenLinGroup.mk (k⁻¹ * y * k) := by
    rw [← hi, mk_conj, mk_conj]
    exact conj_commute _ hys
  have hyj : ProjGenLinGroup.mk (k⁻¹ * y * k) * ProjGenLinGroup.mk (tInv j) =
      ProjGenLinGroup.mk (tInv j) * ProjGenLinGroup.mk (k⁻¹ * y * k) := by
    rw [← hj, mk_conj, mk_conj]
    exact conj_commute _ hyt
  have hyd := mk_commute_of_tInv h2 hτ hij hyi hyj
  rw [← hkg, mk_conj, mk_conj] at hyd
  exact commute_of_conj _ hyd

theorem not_commute_of_point (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : GL (Fin 3) K} (hg : g ∈ slPi π 3 (p ^ f) K)
    (hg3 : g ^ 3 = 1) (hgS : g ∉ StatedScalars (Fin 3) K) {e t : GL (Fin 3) K}
    (he : e ∈ slPi π 3 (p ^ f) K) (he3 : e ^ 3 = 1)
    (heg : ProjGenLinGroup.mk e * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk e)
    (hez : ProjGenLinGroup.mk e ∉ Subgroup.zpowers (ProjGenLinGroup.mk g))
    (ht : t ∈ slPi π 3 (p ^ f) K)
    (htg : ProjGenLinGroup.mk t * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk t)
    (ht2 : ProjGenLinGroup.mk t ^ 2 = 1) (ht1 : ProjGenLinGroup.mk t ≠ 1) :
    ProjGenLinGroup.mk e * ProjGenLinGroup.mk t ≠ ProjGenLinGroup.mk t * ProjGenLinGroup.mk e := by
  obtain ⟨k, hk, hkg⟩ := exists_conj_diagTau hK hq hτ hτ1 hg hg3 hgS
  obtain ⟨h2, i, hi⟩ := exists_tInv_of_involution hK hq hτ hτ1 hk hkg ht htg ht2 ht1
  have he' := conj_inv_mem_slPi hK hk he
  have hed : ProjGenLinGroup.mk (k⁻¹ * e * k) * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk (k⁻¹ * e * k) := by
    rw [← hkg, mk_conj, mk_conj]
    exact conj_commute _ heg
  have he3' : (k⁻¹ * e * k) ^ 3 = 1 := by
    rw [show k⁻¹ * e * k = k⁻¹ * e * k from rfl, conj_inv_pow, he3]
    group
  have hez' : ProjGenLinGroup.mk (k⁻¹ * e * k) ∉
      Subgroup.zpowers (ProjGenLinGroup.mk (diagTau hτ)) := by
    rw [← hkg, mk_conj, mk_conj]
    intro hmem
    apply hez
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [conj_inv_zpow] at hn
    have := congrArg (fun x => ProjGenLinGroup.mk k * x * (ProjGenLinGroup.mk k)⁻¹) hn
    simpa [mul_assoc] using this
  intro hc
  apply mk_mul_ne_of_cube h2 hK hq hτ hτ1 he' hed he3' hez' i
  rw [← hi, mk_conj, mk_conj]
  exact conj_commute _ hc

end CFSG.RankThree.PartTwo.Sec14.Proof1413Res4
