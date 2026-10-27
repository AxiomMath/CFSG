module

public import CFSG.RankThree.PartOne.SLB4A.Sign
public import CFSG.RankThree.PartOne.SLB4A.Unip

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K]

theorem eps_pow_odd {q : ℕ} (hq : Odd q) (x : C2) : eps K x ^ q = eps K x := by
  rcases c2_eq_one_or_gen x with rfl | rfl
  · rw [eps_one, one_pow]
  · rw [eps_gen, hq.neg_one_pow]

theorem signD_mem_statedSU {n q : ℕ} (hq : Odd q) (v : Fin n → C2) (hv : ∏ x, v x = 1) :
    signD K v ∈ StatedSU n q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [det_signD, hv, eps_one]
  · rw [coe_signD, diagonal_map (by simp [zero_pow hq.pos.ne']), diagonal_transpose,
      diagonal_mul_diagonal]
    simp only [eps_pow_odd hq, eps_mul_self]
    exact diagonal_one

theorem scalar_mul_signD_mem_statedSU {q : ℕ} (hq : Odd q) (u : Kˣ) (hu : (u : K) * u = -1)
    (huq : (u : K) ^ q * u = 1) (v : Fin 6 → C2) (hv : ∏ x, v x = c2gen) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) u * signD K v ∈ StatedSU 6 q K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_mul, det_signD, hv,
      eps_gen, Matrix.scalar_apply, Matrix.det_diagonal]
    have h6 : (u : K) ^ 6 = -1 := by
      calc (u : K) ^ 6 = ((u : K) * u) ^ 3 := by ring
        _ = (-1) ^ 3 := by rw [hu]
        _ = -1 := by norm_num
    simp [Finset.prod_const, h6]
  · rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_signD, Matrix.scalar_apply,
      diagonal_mul_diagonal, diagonal_map (by simp [zero_pow hq.pos.ne']), diagonal_transpose,
      diagonal_mul_diagonal]
    have : ∀ a : Fin 6, ((u : K) * eps K (v a)) ^ q * ((u : K) * eps K (v a)) = 1 := fun a => by
      rw [mul_pow, eps_pow_odd hq]
      calc (u : K) ^ q * eps K (v a) * ((u : K) * eps K (v a))
          = ((u : K) ^ q * u) * (eps K (v a) * eps K (v a)) := by ring
        _ = 1 := by rw [huq, eps_mul_self, one_mul]
    simp only [this]
    exact diagonal_one

theorem exists_two_pow_five_psu_odd {q : ℕ} (hq : Odd q) (n : ℕ) (hn : 7 ≤ n) (h2 : (-1 : K) ≠ 1) :
    ∃ U : Subgroup (StatedProj (StatedSU n q K)), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_sign_seven h2 (fun j : Fin 7 => (⟨j.1, by omega⟩ : Fin n)) ?_ _ ?_
  · intro i j h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro v hv
    exact signD_mem_statedSU hq v hv

theorem exists_two_pow_five_psu_six {q : ℕ} (hq : Odd q) (h2 : (-1 : K) ≠ 1) (u : Kˣ)
    (hu : (u : K) * u = -1) (huq : (u : K) ^ q * u = 1) :
    ∃ U : Subgroup (StatedProj (StatedSU 6 q K)), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_sign_six h2 u (fun j : Fin 6 => j) (fun i j h => h) _ ?_ ?_
  · intro v hv
    exact signD_mem_statedSU hq v hv
  · intro v hv
    exact scalar_mul_signD_mem_statedSU hq u hu huq v hv

def PF (x : K) : Prop := x = 0 ∨ x = 1

theorem PF.zero : PF (0 : K) := Or.inl rfl

theorem PF.one : PF (1 : K) := Or.inr rfl

theorem PF.mul {x y : K} (hx : PF x) (hy : PF y) : PF (x * y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [PF]

theorem PF.pow {x : K} (hx : PF x) {q : ℕ} (hq : 0 < q) : x ^ q = x := by
  rcases hx with rfl | rfl
  · exact zero_pow hq.ne'
  · exact one_pow q

theorem PF.add [CharP K 2] {x y : K} (hx : PF x) (hy : PF y) : PF (x + y) := by
  have h2 : (1 : K) + 1 = 0 := by
    have := CharP.cast_eq_zero K 2
    rw [Nat.cast_ofNat] at this
    rw [← two_mul, mul_one]
    exact this
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [PF, h2]

section Herm

variable {ι : Type} [DecidableEq ι]

def hvec (p : Fin 6 → ι) (i : Fin 3) : ι → K :=
  Pi.single (p ⟨2 * i.1, by omega⟩) 1 + Pi.single (p ⟨2 * i.1 + 1, by omega⟩) 1

def hP (p : Fin 6 → ι) (i j : Fin 3) : Matrix ι ι K := Matrix.vecMulVec (hvec p j) (hvec p i)

def hX (p : Fin 6 → ι) : Fin 5 → Matrix ι ι K :=
  ![hP p 0 0, hP p 1 1, hP p 2 2, hP p 1 0 + hP p 0 1, hP p 2 0 + hP p 0 2]

theorem hvec_dot [Fintype ι] [CharP K 2] (p : Fin 6 → ι) (hp : Function.Injective p) (i j : Fin 3) :
    hvec p i ⬝ᵥ hvec p j = (0 : K) := by
  simp only [hvec, dotProduct_add, dotProduct_single, Pi.add_apply, Pi.single_apply, hp.eq_iff,
    Fin.mk.injEq]
  have h2 : (1 : K) + 1 = 0 := by
    have := CharP.cast_eq_zero K 2
    rw [Nat.cast_ofNat] at this
    rw [← two_mul, mul_one]
    exact this
  fin_cases i <;> fin_cases j <;> simp [h2]

theorem hP_mul [Fintype ι] [CharP K 2] (p : Fin 6 → ι) (hp : Function.Injective p)
    (i j k l : Fin 3) : hP p i j * hP p k l = (0 : Matrix ι ι K) := by
  rw [hP, hP, Matrix.vecMulVec_mul_vecMulVec, hvec_dot p hp, zero_smul, Matrix.vecMulVec_zero]

theorem hX_mul [Fintype ι] [CharP K 2] (p : Fin 6 → ι) (hp : Function.Injective p) (k l : Fin 5) :
    hX p k * hX p l = (0 : Matrix ι ι K) := by
  fin_cases k <;> fin_cases l <;> simp [hX, add_mul, mul_add, hP_mul p hp]

theorem hX_symm (p : Fin 6 → ι) (k : Fin 5) : (hX p k : Matrix ι ι K)ᵀ = hX p k := by
  fin_cases k <;> simp [hX, hP, Matrix.transpose_add, add_comm]

theorem hvec_pf [CharP K 2] (p : Fin 6 → ι) (i : Fin 3) (a : ι) : PF (hvec p i a : K) := by
  simp only [hvec, Pi.add_apply, Pi.single_apply]
  refine PF.add ?_ ?_ <;> split_ifs <;> simp [PF]

theorem hX_pf [CharP K 2] (p : Fin 6 → ι) (k : Fin 5) (a b : ι) : PF (hX p k a b : K) := by
  have h : ∀ i j, PF (hP p i j a b : K) := fun i j =>
    PF.mul (hvec_pf p j a) (hvec_pf p i b)
  fin_cases k <;> simp only [hX] <;> first | exact h _ _ | exact PF.add (h _ _) (h _ _)

theorem hP_apply (p : Fin 6 → ι) (i j : Fin 3) (a b : ι) :
    hP p i j a b = (hvec p j a : K) * hvec p i b := Matrix.vecMulVec_apply _ _ _ _

theorem hvec_p (p : Fin 6 → ι) (hp : Function.Injective p) (i : Fin 3) (j : Fin 6) :
    (hvec p i (p j) : K) = if j.1 / 2 = i.1 then 1 else 0 := by
  simp only [hvec, Pi.add_apply, Pi.single_apply, hp.eq_iff, Fin.ext_iff]
  have hi := i.2
  have hj := j.2
  split_ifs <;> first | (exfalso; omega) | simp

theorem hX_ind [Fintype ι] [CharP K 2] (p : Fin 6 → ι) (hp : Function.Injective p) (v : V2 5)
    (h : ∃ c : K, Xsum (hX (K := K) p) v = Matrix.scalar ι c) : v = 1 := by
  obtain ⟨c, hc⟩ := h
  have key : ∀ a b : ι, a ≠ b → (Xsum (hX (K := K) p) v : Matrix ι ι K) a b = 0 := fun a b hab => by
    rw [hc, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hab]
  have e0 := key (p 0) (p 1) (by simp [hp.eq_iff])
  have e1 := key (p 2) (p 3) (by simp [hp.eq_iff])
  have e2 := key (p 4) (p 5) (by simp [hp.eq_iff])
  have e3 := key (p 0) (p 2) (by simp [hp.eq_iff])
  have e4 := key (p 0) (p 4) (by simp [hp.eq_iff])
  simp [Xsum, Matrix.sum_apply, Fin.sum_univ_five, hX, hP_apply, hvec_p p hp] at e0 e1 e2 e3 e4
  have one_ne : (1 : K) ≠ 0 := one_ne_zero
  funext k
  fin_cases k
  · exact cC2_eq_zero _ e0 one_ne
  · exact cC2_eq_zero _ e1 one_ne
  · exact cC2_eq_zero _ e2 one_ne
  · exact cC2_eq_zero _ e3 one_ne
  · exact cC2_eq_zero _ e4 one_ne

end Herm

theorem exists_two_pow_five_psu_even [CharP K 2] {q : ℕ} (hq : 0 < q) (n : ℕ) (hn : 6 ≤ n) :
    ∃ U : Subgroup (StatedProj (StatedSU n q K)), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  let p : Fin 6 → Fin n := fun j => ⟨j.1, by omega⟩
  have hp : Function.Injective p := fun i j h => Fin.ext (by simpa [p] using congrArg Fin.val h)
  have hXm := hX_mul (K := K) p hp
  refine exists_two_pow_five_unip hXm (fun v h => hX_ind (K := K) p hp v h) _ ?_
  intro k
  refine Subgroup.subset_closure ⟨det_uniMat _ _, ?_⟩
  rw [coe_uniMat, Xsum_mulSingle]
  have hmap : (1 + hX (K := K) p k : Matrix (Fin n) (Fin n) K).map (· ^ q) = 1 + hX p k := by
    ext a b
    simp only [Matrix.map_apply, Matrix.add_apply]
    have h1 : PF ((1 : Matrix (Fin n) (Fin n) K) a b) := by
      rw [Matrix.one_apply]
      split_ifs
      · exact PF.one
      · exact PF.zero
    exact (PF.add h1 (hX_pf p k a b)).pow hq
  rw [hmap, Matrix.transpose_add, Matrix.transpose_one, hX_symm]
  have := one_add_Xsum_mul hXm (Pi.mulSingle k c2gen)
  rwa [Xsum_mulSingle] at this

end CFSG.RankThree.PartOne.SLB4A
