module

public import CFSG.Monster.Griess.Space

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix

@[expose] noncomputable def uQ (c : ShortIdx) : Fin 24 → ℚ := fun i => (uvec c i : ℚ)

@[expose] noncomputable def Umat (c : ShortIdx) : Matrix (Fin 24) (Fin 24) ℚ := vecMulVec (uQ c) (uQ c)

@[expose] noncomputable def Rmat (c : ShortIdx) : Matrix SpinIdx SpinIdx ℚ := qmatR ℚ 0 c.1.1 c.1.2

@[expose] noncomputable def qf (c : ShortIdx) (M : Matrix (Fin 24) (Fin 24) ℚ) : ℚ :=
  uQ c ⬝ᵥ (M *ᵥ uQ c)

@[expose] noncomputable def tau (d e c : ShortIdx) : ℚ :=
  open Classical in if c.1 = d.1 + e.1 then sgn (pair e.1.1 d.1.2) else 0

theorem Umat_symm (c : ShortIdx) : (Umat c)ᵀ = Umat c := by
  ext i j
  simp [Umat, vecMulVec_apply, mul_comm]

theorem Rmat_symm (c : ShortIdx) : (Rmat c)ᵀ = Rmat c := by
  rw [Rmat, qmatR_transpose, zero_add, pair_eq_zero_of_isShortCoord c.2]

abbrev Am (u : SpaceB) : Matrix (Fin 24) (Fin 24) ℚ := (u.1 : Matrix (Fin 24) (Fin 24) ℚ)

abbrev xs (u : SpaceB) : SpaceX := u.2.1

abbrev Nm (u : SpaceB) : SpaceW := u.2.2

theorem Am_symm (u : SpaceB) : (Am u)ᵀ = Am u := u.1.2

@[expose] noncomputable def gmulA (u v : SpaceB) : Matrix (Fin 24) (Fin 24) ℚ :=
  (2 : ℚ) • (Am u * Am v + Am v * Am u) + (8 : ℚ)⁻¹ • ∑ c, (xs u c * xs v c) • Umat c +
    (trace ((Nm u)ᵀ * Nm v) / 8) • (1 : Matrix (Fin 24) (Fin 24) ℚ) +
    (2 : ℚ)⁻¹ • ((Nm u)ᵀ * Nm v + (Nm v)ᵀ * Nm u)

theorem gmulA_symm (u v : SpaceB) : (gmulA u v)ᵀ = gmulA u v := by
  simp only [gmulA, transpose_add, transpose_smul, transpose_mul, Am_symm, transpose_sum,
    Umat_symm, transpose_one, transpose_transpose]
  rw [add_comm (Am v * Am u), add_comm ((Nm v)ᵀ * Nm u)]

@[expose] noncomputable def gmulX (u v : SpaceB) (c : ShortIdx) : ℚ :=
  (xs v c * qf c (Am u) + xs u c * qf c (Am v)) / 8 +
    ∑ d, ∑ e, xs u d * xs v e * tau d e c +
    (trace ((Nm u)ᵀ * Rmat c * Nm v) - qf c ((Nm u)ᵀ * Rmat c * Nm v) / 4) / 8

@[expose] noncomputable def gmulWHalf (u v : SpaceB) : SpaceW :=
  (trace (Am u) / 8) • Nm v + Nm v * Am u +
    (8 : ℚ)⁻¹ • ∑ c, xs u c • (Rmat c * Nm v - (4 : ℚ)⁻¹ • (Rmat c * Nm v * Umat c))

@[expose] noncomputable def gmulW (u v : SpaceB) : SpaceW := gmulWHalf u v + gmulWHalf v u

@[expose] noncomputable def gmulFun (u v : SpaceB) : SpaceB :=
  (⟨gmulA u v, gmulA_symm u v⟩, gmulX u v, gmulW u v)

theorem pair_symm_of_short (d e c : ShortIdx) (h : c.1 = d.1 + e.1) :
    pair e.1.1 d.1.2 = pair d.1.1 e.1.2 := by
  have hc := pair_eq_zero_of_isShortCoord c.2
  have hd := pair_eq_zero_of_isShortCoord d.2
  have he := pair_eq_zero_of_isShortCoord e.2
  rw [h, Prod.fst_add, Prod.snd_add, pair_add_left, pair_add_right, pair_add_right, hd, he,
    zero_add, add_zero] at hc
  have h2 : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
  exact h2 _ _ hc

theorem tau_comm (d e c : ShortIdx) : tau d e c = tau e d c := by
  unfold tau
  by_cases h : c.1 = d.1 + e.1
  · rw [ite_eq_left h, ite_eq_left (h.trans (add_comm _ _)), pair_symm_of_short d e c h]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (h'.trans (add_comm _ _)))]

theorem trace_transpose_mul_comm (N N' : SpaceW) : trace (Nᵀ * N') = trace (N'ᵀ * N) := by
  rw [← trace_transpose, transpose_mul, transpose_transpose]

theorem trace_transpose_R_mul_comm (c : ShortIdx) (N N' : SpaceW) :
    trace (Nᵀ * Rmat c * N') = trace (N'ᵀ * Rmat c * N) := by
  rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose, Rmat_symm,
    Matrix.mul_assoc]

theorem qf_transpose_R_mul_comm (c : ShortIdx) (N N' : SpaceW) :
    qf c (Nᵀ * Rmat c * N') = qf c (N'ᵀ * Rmat c * N) := by
  unfold qf
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_mul, transpose_mul, transpose_transpose,
    Rmat_symm, Matrix.mul_assoc, dotProduct_comm]

theorem gmulFun_comm (u v : SpaceB) : gmulFun u v = gmulFun v u := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · show gmulA u v = gmulA v u
    simp only [gmulA]
    rw [add_comm (Am u * Am v), trace_transpose_mul_comm (Nm u), add_comm ((Nm u)ᵀ * Nm v)]
    simp only [mul_comm (xs u _)]
  · funext c
    show gmulX u v c = gmulX v u c
    simp only [gmulX]
    rw [add_comm (xs v c * _), trace_transpose_R_mul_comm c (Nm u),
      qf_transpose_R_mul_comm c (Nm u), Finset.sum_comm]
    congr 2
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    rw [tau_comm, mul_comm (xs u e)]
  · exact add_comm _ _

theorem gmulWHalf_add_left (u u' v : SpaceB) :
    gmulWHalf (u + u') v = gmulWHalf u v + gmulWHalf u' v := by
  simp only [gmulWHalf, Am, xs, Nm, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply,
    trace_add, add_div, add_smul, Matrix.mul_add, Finset.sum_add_distrib, smul_add]
  abel

theorem gmulWHalf_add_right (u v v' : SpaceB) :
    gmulWHalf u (v + v') = gmulWHalf u v + gmulWHalf u v' := by
  simp only [gmulWHalf, Am, xs, Nm, Prod.snd_add, smul_add, Matrix.add_mul, Matrix.mul_add,
    add_sub_add_comm, Finset.sum_add_distrib]
  abel

theorem gmulFun_add_left (u u' v : SpaceB) :
    gmulFun (u + u') v = gmulFun u v + gmulFun u' v := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · show gmulA (u + u') v = gmulA u v + gmulA u' v
    simp only [gmulA, Am, xs, Nm, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply,
      Matrix.add_mul, Matrix.mul_add, transpose_add, trace_add, add_mul, add_smul, add_div,
      Finset.sum_add_distrib, smul_add]
    abel
  · funext c
    show gmulX (u + u') v c = gmulX u v c + gmulX u' v c
    simp only [gmulX, Am, xs, Nm, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply,
      Matrix.add_mul, transpose_add, trace_add, add_mul, mul_add,
      Finset.sum_add_distrib, add_mulVec, dotProduct_add, qf]
    ring
  · show gmulWHalf (u + u') v + gmulWHalf v (u + u') =
      gmulWHalf u v + gmulWHalf v u + (gmulWHalf u' v + gmulWHalf v u')
    rw [gmulWHalf_add_left, gmulWHalf_add_right, add_add_add_comm]

theorem gmulFun_zero_left (v : SpaceB) : gmulFun 0 v = 0 := by
  have h := gmulFun_add_left 0 0 v
  rw [add_zero] at h
  exact left_eq_add.1 h

@[expose] noncomputable def gmulAdd (v : SpaceB) : SpaceB →+ SpaceB where
  toFun u := gmulFun u v
  map_zero' := gmulFun_zero_left v
  map_add' u u' := gmulFun_add_left u u' v

theorem gmulFun_smul_left (t : ℚ) (u v : SpaceB) : gmulFun (t • u) v = t • gmulFun u v :=
  map_rat_smul (gmulAdd v) t u

@[expose] noncomputable def gmul : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB :=
  LinearMap.mk₂ ℚ gmulFun gmulFun_add_left gmulFun_smul_left
    (fun u v v' => by rw [gmulFun_comm, gmulFun_add_left, gmulFun_comm v, gmulFun_comm v'])
    (fun t u v => by rw [gmulFun_comm, gmulFun_smul_left, gmulFun_comm v])

theorem gmul_apply (u v : SpaceB) : gmul u v = gmulFun u v := rfl

theorem gmul_comm (u v : SpaceB) : gmul u v = gmul v u := gmulFun_comm u v

@[expose] noncomputable def T : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ := gmul.compr₂ bform

theorem T_apply (u v w : SpaceB) : T u v w = bform (gmulFun u v) w := rfl

@[expose] noncomputable def fAWW (A : Matrix (Fin 24) (Fin 24) ℚ) (N N' : SpaceW) : ℚ :=
  trace A * trace (Nᵀ * N') / 8 + trace (A * (Nᵀ * N'))

@[expose] noncomputable def gWWX (c : ShortIdx) (N N' : SpaceW) : ℚ :=
  (trace (Nᵀ * Rmat c * N') - qf c (Nᵀ * Rmat c * N') / 4) / 8

@[expose] noncomputable def Tex (u v w : SpaceB) : ℚ :=
  4 * trace (Am u * Am v * Am w) +
    (8 : ℚ)⁻¹ * ∑ c, xs u c * xs v c * qf c (Am w) +
    (8 : ℚ)⁻¹ * ∑ c, xs v c * xs w c * qf c (Am u) +
    (8 : ℚ)⁻¹ * ∑ c, xs u c * xs w c * qf c (Am v) +
    ∑ c, ∑ d, ∑ e, xs u d * xs v e * xs w c * tau d e c +
    fAWW (Am w) (Nm u) (Nm v) + fAWW (Am u) (Nm v) (Nm w) + fAWW (Am v) (Nm u) (Nm w) +
    ∑ c, xs w c * gWWX c (Nm u) (Nm v) + ∑ c, xs u c * gWWX c (Nm v) (Nm w) +
    ∑ c, xs v c * gWWX c (Nm u) (Nm w)

theorem trace_mul_mul_symm {A B D : Matrix (Fin 24) (Fin 24) ℚ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hD : Dᵀ = D) : trace (B * A * D) = trace (A * B * D) := by
  rw [← trace_transpose, transpose_mul, transpose_mul, hA, hB, hD, ← Matrix.mul_assoc,
    ← trace_mul_cycle]

theorem trace_Umat_mul (c : ShortIdx) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    trace (Umat c * M) = qf c M := by
  rw [Umat, vecMulVec_mul, trace_vecMulVec, qf, dotProduct_mulVec, dotProduct_comm]

theorem trace_transpose_mul_mul_symm {A : Matrix (Fin 24) (Fin 24) ℚ} (hA : Aᵀ = A)
    (N N' : SpaceW) : trace (N'ᵀ * N * A) = trace (A * (Nᵀ * N')) := by
  rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose, hA]

theorem sum_sum_mul_eq_trace (N N' : SpaceW) : ∑ j, ∑ i, N j i * N' j i = trace (Nᵀ * N') := by
  simp only [trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem fAWW_comm (A : Matrix (Fin 24) (Fin 24) ℚ) (hA : Aᵀ = A) (N N' : SpaceW) :
    fAWW A N N' = fAWW A N' N := by
  unfold fAWW
  rw [trace_transpose_mul_comm N, ← trace_transpose_mul_mul_symm hA N N',
    trace_mul_comm (N'ᵀ * N) A]

theorem gWWX_comm (c : ShortIdx) (N N' : SpaceW) : gWWX c N N' = gWWX c N' N := by
  unfold gWWX
  rw [trace_transpose_R_mul_comm, qf_transpose_R_mul_comm]

theorem trace_gmulA_mul (u v w : SpaceB) :
    trace (gmulA u v * Am w) = 4 * trace (Am u * Am v * Am w) +
      (8 : ℚ)⁻¹ * ∑ c, xs u c * xs v c * qf c (Am w) + fAWW (Am w) (Nm u) (Nm v) := by
  have h1 : trace (Am v * Am u * Am w) = trace (Am u * Am v * Am w) :=
    trace_mul_mul_symm (Am_symm u) (Am_symm v) (Am_symm w)
  have h2 : trace ((Nm v)ᵀ * Nm u * Am w) = trace (Am w * ((Nm u)ᵀ * Nm v)) :=
    trace_transpose_mul_mul_symm (Am_symm w) _ _
  have h3 : trace ((Nm u)ᵀ * Nm v * Am w) = trace (Am w * ((Nm u)ᵀ * Nm v)) := trace_mul_comm _ _
  have h4 : trace ((∑ c, (xs u c * xs v c) • Umat c) * Am w) =
      ∑ c, xs u c * xs v c * qf c (Am w) := by
    rw [Matrix.sum_mul, trace_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.smul_mul, trace_smul, trace_Umat_mul, smul_eq_mul]
  simp only [gmulA, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, trace_add, trace_smul,
    smul_eq_mul, h1, h2, h3, h4, fAWW]
  ring

theorem sum_gmulX_mul (u v w : SpaceB) :
    ∑ c, gmulX u v c * xs w c = (8 : ℚ)⁻¹ * ∑ c, xs v c * xs w c * qf c (Am u) +
      (8 : ℚ)⁻¹ * ∑ c, xs u c * xs w c * qf c (Am v) +
      ∑ c, ∑ d, ∑ e, xs u d * xs v e * xs w c * tau d e c +
      ∑ c, xs w c * gWWX c (Nm u) (Nm v) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h : (∑ d, ∑ e, xs u d * xs v e * tau d e c) * xs w c =
      ∑ d, ∑ e, xs u d * xs v e * xs w c * tau d e c := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [gmulX, add_mul, add_mul, h, gWWX]
  ring

theorem trace_gmulWHalf_mul (u v : SpaceB) (N' : SpaceW) :
    trace ((gmulWHalf u v)ᵀ * N') = trace (Am u) * trace ((Nm v)ᵀ * N') / 8 +
      trace (Am u * ((Nm v)ᵀ * N')) + ∑ c, xs u c * gWWX c (Nm v) N' := by
  have h : ∀ c, trace ((Rmat c * Nm v - (4 : ℚ)⁻¹ • (Rmat c * Nm v * Umat c))ᵀ * N') =
      8 * gWWX c (Nm v) N' := by
    intro c
    rw [transpose_sub, transpose_smul, transpose_mul, transpose_mul, transpose_mul, Rmat_symm,
      Umat_symm, Matrix.sub_mul, Matrix.smul_mul, trace_sub, trace_smul, smul_eq_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, trace_Umat_mul, gWWX, ← Matrix.mul_assoc]
    ring
  rw [gmulWHalf, transpose_add, transpose_add, transpose_smul, transpose_smul, transpose_mul,
    Am_symm, transpose_sum, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.sum_mul, trace_add, trace_add, trace_smul, trace_smul, trace_sum, smul_eq_mul,
    smul_eq_mul, Matrix.mul_assoc, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [transpose_smul, Matrix.smul_mul, trace_smul, smul_eq_mul, h]
    ring

theorem T_eq_Tex (u v w : SpaceB) : T u v w = Tex u v w := by
  rw [T_apply, bform_apply, sum_sum_mul_eq_trace]
  have hA : ((gmulFun u v).1 : Matrix (Fin 24) (Fin 24) ℚ) = gmulA u v := rfl
  have hX : (gmulFun u v).2.1 = gmulX u v := rfl
  have hW : (gmulFun u v).2.2 = gmulWHalf u v + gmulWHalf v u := rfl
  rw [hA, hX, hW, transpose_add, Matrix.add_mul, trace_add, trace_gmulA_mul, sum_gmulX_mul,
    trace_gmulWHalf_mul, trace_gmulWHalf_mul]
  unfold Tex fAWW
  ring

theorem add_self_coord (x : C × Cocode) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem tau_cycle (d e c : ShortIdx) : tau d e c = tau c d e := by
  unfold tau
  by_cases h : c.1 = d.1 + e.1
  · have h' : e.1 = c.1 + d.1 := by rw [h, add_comm d.1 e.1, add_assoc, add_self_coord, add_zero]
    rw [ite_eq_left h, ite_eq_left h', pair_symm_of_short d e c h, h, Prod.snd_add, pair_add_right,
      pair_eq_zero_of_isShortCoord d.2, zero_add]
  · have h' : ¬ e.1 = c.1 + d.1 := fun h' =>
      h (by rw [h', add_comm c.1 d.1, ← add_assoc, add_self_coord, zero_add])
    rw [ite_eq_right h, ite_eq_right h']

theorem sum3_tau_swap (x y z : SpaceX) :
    ∑ c, ∑ d, ∑ e, y d * x e * z c * tau d e c = ∑ c, ∑ d, ∑ e, x d * y e * z c * tau d e c := by
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  rw [tau_comm e d c]
  ring

theorem sum3_tau_cycle (x y z : SpaceX) :
    ∑ c, ∑ d, ∑ e, y d * z e * x c * tau d e c = ∑ c, ∑ d, ∑ e, x d * y e * z c * tau d e c := by
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
  rw [tau_cycle e c d]
  ring

theorem Tex_swap (u v w : SpaceB) : Tex v u w = Tex u v w := by
  have e1 : ∑ c, xs v c * xs u c * qf c (Am w) = ∑ c, xs u c * xs v c * qf c (Am w) :=
    Finset.sum_congr rfl fun c _ => by ring
  have e2 : ∑ c, xs w c * gWWX c (Nm v) (Nm u) = ∑ c, xs w c * gWWX c (Nm u) (Nm v) :=
    Finset.sum_congr rfl fun c _ => by rw [gWWX_comm]
  unfold Tex
  rw [trace_mul_mul_symm (Am_symm u) (Am_symm v) (Am_symm w), e1, e2,
    sum3_tau_swap (xs u) (xs v) (xs w), fAWW_comm (Am w) (Am_symm w) (Nm v)]
  ring

theorem Tex_cycle (u v w : SpaceB) : Tex v w u = Tex u v w := by
  have e1 : ∑ c, xs w c * xs u c * qf c (Am v) = ∑ c, xs u c * xs w c * qf c (Am v) :=
    Finset.sum_congr rfl fun c _ => by ring
  have e2 : ∑ c, xs v c * xs u c * qf c (Am w) = ∑ c, xs u c * xs v c * qf c (Am w) :=
    Finset.sum_congr rfl fun c _ => by ring
  have e3 : ∑ c, xs v c * gWWX c (Nm w) (Nm u) = ∑ c, xs v c * gWWX c (Nm u) (Nm w) :=
    Finset.sum_congr rfl fun c _ => by rw [gWWX_comm]
  have e4 : ∑ c, xs w c * gWWX c (Nm v) (Nm u) = ∑ c, xs w c * gWWX c (Nm u) (Nm v) :=
    Finset.sum_congr rfl fun c _ => by rw [gWWX_comm]
  unfold Tex
  rw [trace_mul_cycle (Am v), e1, e2, e3, e4, sum3_tau_cycle (xs u) (xs v) (xs w),
    fAWW_comm (Am v) (Am_symm v) (Nm w), fAWW_comm (Am w) (Am_symm w) (Nm v)]
  ring

theorem T_swap12 (u v w : SpaceB) : T u v w = T v u w := by
  rw [T_eq_Tex, T_eq_Tex, Tex_swap u v w]

theorem T_cycle (u v w : SpaceB) : T u v w = T v w u := by
  rw [T_eq_Tex, T_eq_Tex, Tex_cycle u v w]

theorem T_swap23 (u v w : SpaceB) : T u v w = T u w v := by
  rw [T_cycle u w v, T_swap12 w v u, ← T_cycle u v w]

theorem bform_comm (u v : SpaceB) : bform u v = bform v u := by
  rw [bform_apply, bform_apply, trace_mul_comm]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem bform_gmul_assoc (u v w : SpaceB) : bform (gmul u v) w = bform u (gmul v w) := by
  rw [bform_comm u, gmul_apply, gmul_apply]
  exact T_cycle u v w

theorem fAWW_zero_left (N N' : SpaceW) : fAWW 0 N N' = 0 := by simp [fAWW]

theorem fAWW_zero_mid (A : Matrix (Fin 24) (Fin 24) ℚ) (N' : SpaceW) : fAWW A 0 N' = 0 := by
  simp [fAWW]

theorem fAWW_zero_right (A : Matrix (Fin 24) (Fin 24) ℚ) (N : SpaceW) : fAWW A N 0 = 0 := by
  simp [fAWW]

theorem qf_zero (c : ShortIdx) : qf c 0 = 0 := by simp [qf]

theorem gWWX_zero_left (c : ShortIdx) (N' : SpaceW) : gWWX c 0 N' = 0 := by
  simp [gWWX, qf_zero]

theorem gWWX_zero_right (c : ShortIdx) (N : SpaceW) : gWWX c N 0 = 0 := by
  simp [gWWX, qf_zero]

abbrev inA (A : symMat) : SpaceB := (A, 0, 0)

abbrev inX (x : SpaceX) : SpaceB := (0, x, 0)

abbrev inW (N : SpaceW) : SpaceB := (0, 0, N)

@[simp] theorem Am_inA (A : symMat) : Am (inA A) = A := rfl
@[simp] theorem xs_inA (A : symMat) : xs (inA A) = 0 := rfl
@[simp] theorem Nm_inA (A : symMat) : Nm (inA A) = 0 := rfl
@[simp] theorem Am_inX (x : SpaceX) : Am (inX x) = 0 := rfl
@[simp] theorem xs_inX (x : SpaceX) : xs (inX x) = x := rfl
@[simp] theorem Nm_inX (x : SpaceX) : Nm (inX x) = 0 := rfl
@[simp] theorem Am_inW (N : SpaceW) : Am (inW N) = 0 := rfl
@[simp] theorem xs_inW (N : SpaceW) : xs (inW N) = 0 := rfl
@[simp] theorem Nm_inW (N : SpaceW) : Nm (inW N) = N := rfl

theorem T_AAA (A A' A'' : symMat) :
    T (inA A) (inA A') (inA A'') = 4 * trace ((A : Matrix (Fin 24) (Fin 24) ℚ) *
      (A' : Matrix (Fin 24) (Fin 24) ℚ) * (A'' : Matrix (Fin 24) (Fin 24) ℚ)) := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_right]

theorem T_XXA (x x' : SpaceX) (A : symMat) :
    T (inX x) (inX x') (inA A) = (8 : ℚ)⁻¹ * ∑ c, x c * x' c * qf c A := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_right, qf_zero, gWWX_zero_left]

theorem T_XXX (x x' x'' : SpaceX) :
    T (inX x) (inX x') (inX x'') = ∑ c, ∑ d, ∑ e, x d * x' e * x'' c * tau d e c := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_left, qf_zero, gWWX_zero_left]

theorem T_WWA (N N' : SpaceW) (A : symMat) : T (inW N) (inW N') (inA A) = fAWW A N N' := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_right, qf_zero]

theorem T_WWX (N N' : SpaceW) (x : SpaceX) :
    T (inW N) (inW N') (inX x) = ∑ c, x c * gWWX c N N' := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_left, qf_zero, gWWX_zero_right]

theorem T_AAX (A A' : symMat) (x : SpaceX) : T (inA A) (inA A') (inX x) = 0 := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_right, gWWX_zero_left]

theorem T_AAW (A A' : symMat) (N : SpaceW) : T (inA A) (inA A') (inW N) = 0 := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_mid, gWWX_zero_left]

theorem T_AXW (A : symMat) (x : SpaceX) (N : SpaceW) : T (inA A) (inX x) (inW N) = 0 := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_mid, fAWW_zero_right, qf_zero, gWWX_zero_left]

theorem T_XXW (x x' : SpaceX) (N : SpaceW) : T (inX x) (inX x') (inW N) = 0 := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_mid, qf_zero, gWWX_zero_left]

theorem T_WWW (N N' N'' : SpaceW) : T (inW N) (inW N') (inW N'') = 0 := by
  rw [T_eq_Tex]
  simp [Tex, fAWW_zero_left, qf_zero]

end CFSG.Monster.Griess
