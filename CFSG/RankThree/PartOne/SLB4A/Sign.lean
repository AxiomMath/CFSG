module

public import CFSG.RankThree.PartOne.SLB4A.Basic

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank Matrix

section Sign

variable {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]

@[expose] def eps (x : C2) : K := (-1 : K) ^ (Multiplicative.toAdd x).val

theorem eps_one : eps K 1 = 1 := by simp [eps]

theorem eps_gen : eps K c2gen = -1 := by
  simp only [eps, c2gen, toAdd_ofAdd]
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem eps_mul (x y : C2) : eps K (x * y) = eps K x * eps K y := by
  rcases c2_eq_one_or_gen x with rfl | rfl <;> rcases c2_eq_one_or_gen y with rfl | rfl <;>
    simp [c2_mul_self, eps_one, eps_gen]

theorem eps_mul_self (x : C2) : eps K x * eps K x = 1 := by
  rw [← eps_mul, c2_mul_self, eps_one]

variable {K} in
theorem eps_inj (h2 : (-1 : K) ≠ 1) {x y : C2} (h : eps K x = eps K y) : x = y := by
  rcases c2_eq_one_or_gen x with rfl | rfl <;> rcases c2_eq_one_or_gen y with rfl | rfl
  · rfl
  · rw [eps_one, eps_gen] at h
    exact absurd h.symm h2
  · rw [eps_one, eps_gen] at h
    exact absurd h h2
  · rfl

@[expose] def signMat (d : ι → K) (hd : ∀ a, d a * d a = 1) : GL ι K where
  val := diagonal d
  inv := diagonal d
  val_inv := by
    rw [diagonal_mul_diagonal]
    simp only [hd]
    exact diagonal_one
  inv_val := by
    rw [diagonal_mul_diagonal]
    simp only [hd]
    exact diagonal_one

@[expose] def signD (v : ι → C2) : GL ι K := signMat K (fun a => eps K (v a)) (fun a => eps_mul_self K (v a))

theorem coe_signD (v : ι → C2) :
    ((signD K v : GL ι K) : Matrix ι ι K) = diagonal fun a => eps K (v a) := rfl

@[expose] def signDHom : (ι → C2) →* GL ι K where
  toFun := signD K
  map_one' := Units.ext (by simp [coe_signD, eps_one])
  map_mul' v w := Units.ext (by
    simp [coe_signD, diagonal_mul_diagonal, eps_mul])

theorem signDHom_apply (v : ι → C2) : signDHom K v = signD K v := rfl

variable {K}

theorem signD_scalar {v : ι → C2} (hv : signD K v ∈ StatedScalars ι K) (a b : ι) :
    eps K (v a) = eps K (v b) := by
  obtain ⟨c, hc⟩ := mem_statedScalars_iff.1 hv
  rw [coe_signD] at hc
  have h1 := congrFun (congrFun hc a) a
  have h2 := congrFun (congrFun hc b) b
  simp only [diagonal_apply_eq, Matrix.scalar_apply] at h1 h2
  rw [h1, ← h2]

theorem det_signD (v : ι → C2) : ((signD K v : GL ι K) : Matrix ι ι K).det = eps K (∏ a, v a) := by
  rw [coe_signD, det_diagonal]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [eps_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, eps_mul, ih]

end Sign

section Edge

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def edgeVec (a b : Fin 5 → ι) : V2 5 →* (ι → C2) where
  toFun v x := ∏ k, if x = a k ∨ x = b k then v k else 1
  map_one' := by
    funext x
    simp
  map_mul' v w := by
    funext x
    simp only [Pi.mul_apply, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp

omit [Fintype ι] in
theorem edgeVec_apply (a b : Fin 5 → ι) (v : V2 5) (x : ι) :
    edgeVec a b v x = ∏ k, if x = a k ∨ x = b k then v k else 1 := rfl

theorem prod_edgeVec (a b : Fin 5 → ι) (hab : ∀ k, a k ≠ b k) (v : V2 5) :
    ∏ x, edgeVec a b v x = 1 := by
  simp only [edgeVec_apply]
  rw [Finset.prod_comm]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have : (Finset.univ.filter fun x : ι => x = a k ∨ x = b k) = {a k, b k} := by
    ext x
    simp
  rw [this, Finset.card_pair (hab k)]
  exact c2_sq (v k)

variable {K : Type} [Field K]

theorem exists_two_pow_five_sign (h2 : (-1 : K) ≠ 1) (a b : Fin 5 → ι) (hab : ∀ k, a k ≠ b k)
    (hind : ∀ v : V2 5, (∀ x y, edgeVec a b v x = edgeVec a b v y) → v = 1)
    (H : Subgroup (GL ι K)) (hH : ∀ v : ι → C2, ∏ x, v x = 1 → signD K v ∈ H) :
    ∃ U : Subgroup (StatedProj H), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_statedProj H (fun v => signD K (edgeVec a b v)) ?_ ?_ ?_
  · intro v
    exact hH _ (prod_edgeVec a b hab v)
  · intro v w
    have : signD K (edgeVec a b (v * w)) = signD K (edgeVec a b v) * signD K (edgeVec a b w) := by
      rw [map_mul, ← signDHom_apply, ← signDHom_apply, ← signDHom_apply, map_mul]
    rw [this, inv_mul_cancel]
    exact one_mem _
  · intro v hv
    exact hind v fun x y => eps_inj h2 (signD_scalar hv x y)

omit [Fintype ι] in
theorem edgeVec_path (p : Fin 7 → ι) (hp : Function.Injective p) (v : V2 5) (j : Fin 7) :
    edgeVec (fun k : Fin 5 => p ⟨k.1, by omega⟩) (fun k : Fin 5 => p ⟨k.1 + 1, by omega⟩) v (p j) =
      ∏ k : Fin 5, if j.1 = k.1 ∨ j.1 = k.1 + 1 then v k else 1 := by
  rw [edgeVec_apply]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [hp.eq_iff, Fin.ext_iff]

theorem exists_two_pow_five_sign_seven (h2 : (-1 : K) ≠ 1) (p : Fin 7 → ι)
    (hp : Function.Injective p) (H : Subgroup (GL ι K))
    (hH : ∀ v : ι → C2, ∏ x, v x = 1 → signD K v ∈ H) :
    ∃ U : Subgroup (StatedProj H), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_sign h2 (fun k => p ⟨k.1, by omega⟩) (fun k => p ⟨k.1 + 1, by omega⟩)
    ?_ ?_ H hH
  · intro k h
    have := hp h
    simp [Fin.ext_iff] at this
  · intro v hv
    have h0 := hv (p 0) (p 6)
    have h1 := hv (p 1) (p 6)
    have h2' := hv (p 2) (p 6)
    have h3 := hv (p 3) (p 6)
    have h4 := hv (p 4) (p 6)
    have h5 := hv (p 5) (p 6)
    rw [edgeVec_path p hp, edgeVec_path p hp] at h0 h1 h2' h3 h4 h5
    simp only [Fin.prod_univ_five] at h0 h1 h2' h3 h4 h5
    simp at h0 h1 h2' h3 h4 h5
    have e1 : v 1 = 1 := by rw [h0, one_mul] at h1; exact h1
    have e3 : v 3 = 1 := by rw [h5, mul_one] at h4; exact h4
    have e2 : v 2 = 1 := by rw [e3, mul_one] at h3; exact h3
    funext k
    fin_cases k
    · exact h0
    · exact e1
    · exact e2
    · exact e3
    · exact h5

@[expose] def uPow (u : Kˣ) (x : C2) : Kˣ := u ^ (Multiplicative.toAdd x).val

theorem uPow_gen (u : Kˣ) : uPow u c2gen = u := by
  simp only [uPow, c2gen, toAdd_ofAdd]
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem uPow_one (u : Kˣ) : uPow u 1 = 1 := by
  simp [uPow]

@[expose] def edgeVec6 (a b : Fin 4 → ι) (c : ι) : V2 5 →* (ι → C2) where
  toFun v x := (∏ k : Fin 4, if x = a k ∨ x = b k then v k.castSucc else 1) *
    (if x = c then v 4 else 1)
  map_one' := by
    funext x
    simp
  map_mul' v w := by
    funext x
    have h1 : (if x = c then (v * w) 4 else (1 : C2)) =
        (if x = c then v 4 else 1) * (if x = c then w 4 else 1) := by
      split_ifs <;> simp
    have h2 : ∀ k : Fin 4, (if x = a k ∨ x = b k then (v * w) k.castSucc else (1 : C2)) =
        (if x = a k ∨ x = b k then v k.castSucc else 1) *
          (if x = a k ∨ x = b k then w k.castSucc else 1) := fun k => by
      split_ifs <;> simp
    show ((∏ k : Fin 4, if x = a k ∨ x = b k then (v * w) k.castSucc else 1) *
        (if x = c then (v * w) 4 else 1)) =
      ((∏ k : Fin 4, if x = a k ∨ x = b k then v k.castSucc else 1) *
        (if x = c then v 4 else 1)) *
      ((∏ k : Fin 4, if x = a k ∨ x = b k then w k.castSucc else 1) *
        (if x = c then w 4 else 1))
    rw [h1]
    simp only [h2]
    rw [Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _

omit [Fintype ι] in
theorem edgeVec6_apply (a b : Fin 4 → ι) (c : ι) (v : V2 5) (x : ι) :
    edgeVec6 a b c v x = (∏ k : Fin 4, if x = a k ∨ x = b k then v k.castSucc else 1) *
      (if x = c then v 4 else 1) := rfl

omit [Fintype ι] in
theorem edgeVec6_path (p : Fin 6 → ι) (hp : Function.Injective p) (v : V2 5) (j : Fin 6) :
    edgeVec6 (fun k : Fin 4 => p ⟨k.1, by omega⟩) (fun k : Fin 4 => p ⟨k.1 + 1, by omega⟩) (p 0) v
      (p j) = (∏ k : Fin 4, if j.1 = k.1 ∨ j.1 = k.1 + 1 then v k.castSucc else 1) *
        (if j.1 = 0 then v 4 else 1) := by
  rw [edgeVec6_apply]
  congr 1
  · refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hp.eq_iff, Fin.ext_iff]
  · simp only [hp.eq_iff, Fin.ext_iff, Fin.val_zero]

theorem prod_edgeVec6 (a b : Fin 4 → ι) (hab : ∀ k, a k ≠ b k) (c : ι) (v : V2 5) :
    ∏ x, edgeVec6 a b c v x = v 4 := by
  simp only [edgeVec6_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  have h1 : ∏ k : Fin 4, ∏ x : ι, (if x = a k ∨ x = b k then v k.castSucc else 1) = 1 := by
    refine Finset.prod_eq_one fun k _ => ?_
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have : (Finset.univ.filter fun x : ι => x = a k ∨ x = b k) = {a k, b k} := by
      ext x
      simp
    rw [this, Finset.card_pair (hab k)]
    exact c2_sq _
  rw [h1, one_mul]
  simp

theorem hmul_scalar_mul {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (α β : Kˣ)
    (D : GL ι K) :
    (Matrix.GeneralLinearGroup.scalar ι α * D)⁻¹ * (Matrix.GeneralLinearGroup.scalar ι β * D) ∈
      StatedScalars ι K := by
  have h : (Matrix.GeneralLinearGroup.scalar ι α * D)⁻¹ * (Matrix.GeneralLinearGroup.scalar ι β * D) =
      D⁻¹ * (Matrix.GeneralLinearGroup.scalar ι (α⁻¹ * β)) * D := by
    rw [map_mul, map_inv]
    group
  rw [h]
  have hz : Matrix.GeneralLinearGroup.scalar ι (α⁻¹ * β) ∈ StatedScalars ι K := ⟨_, rfl⟩
  have := (StatedScalars.normal ι K).conj_mem _ hz D⁻¹
  simpa using this

theorem exists_two_pow_five_sign_six (h2 : (-1 : K) ≠ 1) (u : Kˣ) (p : Fin 6 → ι)
    (hp : Function.Injective p) (H : Subgroup (GL ι K))
    (hH0 : ∀ v : ι → C2, ∏ x, v x = 1 → signD K v ∈ H)
    (hH1 : ∀ v : ι → C2, ∏ x, v x = c2gen →
      Matrix.GeneralLinearGroup.scalar ι u * signD K v ∈ H) :
    ∃ U : Subgroup (StatedProj H), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  let a : Fin 4 → ι := fun k => p ⟨k.1, by omega⟩
  let b : Fin 4 → ι := fun k => p ⟨k.1 + 1, by omega⟩
  let c : ι := p 0
  have hab : ∀ k, a k ≠ b k := fun k h => by
    have := hp h
    simp [Fin.ext_iff] at this
  let S : V2 5 → GL ι K := fun v =>
    Matrix.GeneralLinearGroup.scalar ι (uPow u (v 4)) * signD K (edgeVec6 a b c v)
  refine exists_two_pow_five_statedProj H S ?_ ?_ ?_
  · intro v
    rcases c2_eq_one_or_gen (v 4) with h | h
    · have := hH0 _ (by rw [prod_edgeVec6 a b hab c v, h])
      simpa only [S, h, uPow_one, map_one, one_mul] using this
    · have := hH1 _ (by rw [prod_edgeVec6 a b hab c v, h])
      simpa only [S, h, uPow_gen] using this
  · intro v w
    have hD : signD K (edgeVec6 a b c (v * w)) =
        signD K (edgeVec6 a b c v) * signD K (edgeVec6 a b c w) := by
      rw [map_mul, ← signDHom_apply, ← signDHom_apply, ← signDHom_apply, map_mul]
    have hS : S v * S w = Matrix.GeneralLinearGroup.scalar ι (uPow u (v 4) * uPow u (w 4)) *
        signD K (edgeVec6 a b c (v * w)) := by
      simp only [S]
      rw [hD, map_mul]
      have hc : signD K (edgeVec6 a b c v) * Matrix.GeneralLinearGroup.scalar ι (uPow u (w 4)) =
          Matrix.GeneralLinearGroup.scalar ι (uPow u (w 4)) * signD K (edgeVec6 a b c v) :=
        (Matrix.GeneralLinearGroup.scalar_commute _ _).symm
      calc _ = Matrix.GeneralLinearGroup.scalar ι (uPow u (v 4)) *
            (signD K (edgeVec6 a b c v) * Matrix.GeneralLinearGroup.scalar ι (uPow u (w 4))) *
            signD K (edgeVec6 a b c w) := by simp only [mul_assoc]
        _ = _ := by rw [hc]; simp only [mul_assoc]
    rw [hS]
    exact hmul_scalar_mul _ _ _
  · intro v hv
    have hv' : signD K (edgeVec6 a b c v) ∈ StatedScalars ι K := by
      have hz : Matrix.GeneralLinearGroup.scalar ι (uPow u (v 4))⁻¹ ∈ StatedScalars ι K := ⟨_, rfl⟩
      have e : signD K (edgeVec6 a b c v) =
          Matrix.GeneralLinearGroup.scalar ι (uPow u (v 4))⁻¹ * S v := by
        simp only [S, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      rw [e]
      exact mul_mem hz hv
    have hconst : ∀ x y, edgeVec6 a b c v x = edgeVec6 a b c v y := fun x y =>
      eps_inj h2 (signD_scalar hv' x y)
    have h0 := hconst (p 0) (p 5)
    have h1 := hconst (p 1) (p 5)
    have h2' := hconst (p 2) (p 5)
    have h3 := hconst (p 3) (p 5)
    have h4 := hconst (p 4) (p 5)
    rw [edgeVec6_path p hp, edgeVec6_path p hp] at h0 h1 h2' h3 h4
    simp only [Fin.prod_univ_four] at h0 h1 h2' h3 h4
    simp at h0 h1 h2' h3 h4
    have e2 : v 2 = 1 := by rw [h4, mul_one] at h3; exact h3
    have e1 : v 1 = 1 := by rw [e2, mul_one] at h2'; exact h2'
    have e0 : v 0 = 1 := by rw [e1, mul_one] at h1; exact h1
    have e4 : v 4 = 1 := by rw [e0, one_mul] at h0; exact h0
    funext k
    fin_cases k
    · exact e0
    · exact e1
    · exact e2
    · exact h4
    · exact e4

end Edge

end CFSG.RankThree.PartOne.SLB4A
