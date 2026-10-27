module

public import CFSG.Monster.Griess.Trilinear
public import CFSG.Monster.Griess.DyadicCoords
public import CFSG.Monster.Spin.DyadicNormalizer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix Subgroup

theorem coordOf_mul (r s : Q) : coordOf (r * s) = coordOf r + coordOf s := by
  simp only [coordOf, map_mul, SpinCoord.mul_a, SpinCoord.mul_δ, Prod.mk_add_mk]

theorem centralCoord_mul (r s : Q) :
    centralCoord (r * s) = centralCoord r + centralCoord s + pair (coordOf s).1 (coordOf r).2 := by
  simp only [centralCoord, coordOf, map_mul, SpinCoord.mul_s]

theorem mem_zpowers_zQ_iff (g : Q) : g ∈ zpowers zQ ↔ coordOf g = 0 := by
  rw [← center_Q, ← ker_projQ, MonoidHom.mem_ker]
  show Multiplicative.ofAdd (coordOf g) = 1 ↔ _
  exact ofAdd_eq_one

theorem eq_zQ_pow_iff (g : Q) (e : ZMod 2) : g = zQ ^ e.val ↔ coordOf g = 0 ∧ centralCoord g = e := by
  constructor
  · intro h
    have h' : spinEquiv.symm g = ⟨e, 0, 0⟩ :=
      (congrArg spinEquiv.symm (h.trans (zQ_pow_val e))).trans (spinEquiv.symm_apply_apply _)
    exact ⟨Prod.ext (congrArg SpinCoord.a h') (congrArg SpinCoord.δ h'), congrArg SpinCoord.s h'⟩
  · rintro ⟨h1, h2⟩
    have h' : spinEquiv.symm g = ⟨e, 0, 0⟩ :=
      SpinCoord.ext h2 (congrArg Prod.fst h1) (congrArg Prod.snd h1)
    exact (spinEquiv.apply_symm_apply g).symm.trans
      ((congrArg spinEquiv h').trans (zQ_pow_val e).symm)

theorem exists_eq_zQ_pow {g : Q} (h : g ∈ zpowers zQ) : ∃ e : ZMod 2, g = zQ ^ e.val :=
  ⟨centralCoord g, (eq_zQ_pow_iff g _).2 ⟨(mem_zpowers_zQ_iff g).1 h, rfl⟩⟩

theorem eq_of_add_eq_zero' {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M}
    (h : x + y = 0) : y = x := by
  have hx : x + x = 0 := by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  calc y = (x + x) + y := by rw [hx, zero_add]
    _ = x + (x + y) := add_assoc _ _ _
    _ = x := by rw [h, add_zero]

theorem add_eq_zero_iff' {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M} :
    x + y = 0 ↔ y = x := by
  refine ⟨eq_of_add_eq_zero', fun h => ?_⟩
  rw [h, ← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem coe_Q_eq (r : Q) :
    ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      qmatR ℚ (centralCoord r) (coordOf r).1 (coordOf r).2 :=
  congrArg (fun g : Q => ((g : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ))
    (spinEquiv.apply_symm_apply r).symm

theorem qmatR_eq_sgn_smul (s : ZMod 2) (a : C) (δ : Cocode) :
    qmatR ℚ s a δ = sgn s • qmatR ℚ 0 a δ := by
  have h := sgnR_smul_qmatR (R := ℚ) s 0 a δ
  rw [add_zero] at h
  exact h.symm

theorem coe_Q_eq_sgn_smul_Rmat {r : Q} (hr : IsShortCoord (coordOf r)) :
    ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      sgn (centralCoord r) • Rmat ⟨coordOf r, hr⟩ := by
  rw [coe_Q_eq, qmatR_eq_sgn_smul]
  rfl

theorem sum_single_mul_single (cr cs : ShortIdx) (a b : ℚ) (f : ShortIdx → ℚ) :
    ∑ c, (a • (Pi.single cr 1 : SpaceX)) c * (b • (Pi.single cs 1 : SpaceX)) c * f c =
      if cs = cr then a * b * f cr else 0 := by
  rw [Finset.sum_eq_single cr]
  · by_cases h : cs = cr
    · subst h
      simp
    · simp [h, Ne.symm h]
  · intro c _ hc
    simp [hc]
  · simp

theorem sum_single_mul (cr : ShortIdx) (a : ℚ) (f : ShortIdx → ℚ) :
    ∑ c, (a • (Pi.single cr 1 : SpaceX)) c * f c = a * f cr := by
  rw [Finset.sum_eq_single cr]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

theorem sum3_single (cr cs ct : ShortIdx) (a b e : ℚ) :
    ∑ c, ∑ d, ∑ f, (a • (Pi.single cr 1 : SpaceX)) d * (b • (Pi.single cs 1 : SpaceX)) f *
      (e • (Pi.single ct 1 : SpaceX)) c * tau d f c = a * b * e * tau cr cs ct := by
  rw [Finset.sum_eq_single ct]
  · rw [Finset.sum_eq_single cr]
    · rw [Finset.sum_eq_single cs]
      · simp
      · intro f _ hf
        simp [hf]
      · simp
    · intro d _ hd
      simp [hd]
    · simp
  · intro c _ hc
    simp [hc]
  · simp

theorem T_Xlift_Xlift_A {r s : Q} (hr : IsShortCoord (coordOf r)) (hs : IsShortCoord (coordOf s))
    (A : symMat) :
    (∀ e : ZMod 2, r * s = zQ ^ e.val →
      T (inX (Xlift r)) (inX (Xlift s)) (inA A) = sgn e * qf ⟨coordOf r, hr⟩ A / 8) ∧
    (r * s ∉ zpowers zQ → T (inX (Xlift r)) (inX (Xlift s)) (inA A) = 0) := by
  simp only [T_XXA, Xlift_eq hr, Xlift_eq hs, sum_single_mul_single]
  constructor
  · intro e he
    obtain ⟨h1, h2⟩ := (eq_zQ_pow_iff _ e).1 he
    have hcs : coordOf s = coordOf r := eq_of_add_eq_zero' ((coordOf_mul r s).symm.trans h1)
    have hcs' : (⟨coordOf s, hs⟩ : ShortIdx) = ⟨coordOf r, hr⟩ := Subtype.ext hcs
    have he' : e = centralCoord r + centralCoord s := by
      have h3 := (centralCoord_mul r s).symm.trans h2
      simp only [hcs, pair_eq_zero_of_isShortCoord hr, add_zero] at h3
      exact h3.symm
    simp only [ite_eq_left hcs', he', sgn_add]
    ring
  · intro hn
    have hne : (⟨coordOf s, hs⟩ : ShortIdx) ≠ ⟨coordOf r, hr⟩ := fun h => hn
      ((mem_zpowers_zQ_iff _).2 ((coordOf_mul r s).trans
        (add_eq_zero_iff'.2 (congrArg Subtype.val h))))
    simp only [ite_eq_right hne, mul_zero]

theorem T_Xlift3 {r s t : Q} (hr : IsShortCoord (coordOf r)) (hs : IsShortCoord (coordOf s))
    (ht : IsShortCoord (coordOf t)) :
    (∀ e : ZMod 2, r * s * t = zQ ^ e.val →
      T (inX (Xlift r)) (inX (Xlift s)) (inX (Xlift t)) = sgn e) ∧
    (r * s * t ∉ zpowers zQ → T (inX (Xlift r)) (inX (Xlift s)) (inX (Xlift t)) = 0) := by
  simp only [T_XXX, Xlift_eq hr, Xlift_eq hs, Xlift_eq ht, sum3_single]
  constructor
  · intro e he
    obtain ⟨h1, h2⟩ := (eq_zQ_pow_iff _ e).1 he
    have h1' : coordOf r + coordOf s + coordOf t = 0 := by
      have := h1
      simp only [coordOf_mul] at this
      exact this
    have hct : coordOf t = coordOf r + coordOf s := eq_of_add_eq_zero' h1'
    have he' : e = centralCoord r + centralCoord s + centralCoord t +
        pair (coordOf s).1 (coordOf r).2 := by
      have h3 := h2
      simp only [centralCoord_mul, coordOf_mul] at h3
      rw [← hct, pair_eq_zero_of_isShortCoord ht, add_zero] at h3
      rw [← h3]
      ring
    have htau : tau ⟨coordOf r, hr⟩ ⟨coordOf s, hs⟩ ⟨coordOf t, ht⟩ =
        sgn (pair (coordOf s).1 (coordOf r).2) := by
      unfold tau
      exact ite_eq_left hct
    rw [htau, he', sgn_add, sgn_add, sgn_add]
  · intro hn
    have hne : ¬ coordOf t = coordOf r + coordOf s := fun h => hn
      ((mem_zpowers_zQ_iff _).2 (((coordOf_mul _ _).trans
        (congrArg (· + coordOf t) (coordOf_mul r s))).trans (add_eq_zero_iff'.2 h)))
    have htau : tau ⟨coordOf r, hr⟩ ⟨coordOf s, hs⟩ ⟨coordOf t, ht⟩ = 0 := by
      unfold tau
      exact ite_eq_right hne
    rw [htau, mul_zero]

theorem transpose_tensor (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    (tensor q v)ᵀ = vecMulVec v q := transpose_vecMulVec q v

theorem tensor_transpose_mul_tensor (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) :
    (tensor q v)ᵀ * tensor q' w = (q ⬝ᵥ q') • vecMulVec v w := by
  rw [transpose_tensor, tensor, vecMulVec_mul_vecMulVec, vecMulVec_smul]

theorem tensor_transpose_mul_R_mul_tensor (c : ShortIdx) (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) :
    (tensor q v)ᵀ * Rmat c * tensor q' w = ((q ᵥ* Rmat c) ⬝ᵥ q') • vecMulVec v w := by
  rw [transpose_tensor, vecMulVec_mul, tensor, vecMulVec_mul_vecMulVec, vecMulVec_smul]

theorem qf_vecMulVec (c : ShortIdx) (v w : Fin 24 → ℚ) :
    qf c (vecMulVec v w) = (v ⬝ᵥ uQ c) * (w ⬝ᵥ uQ c) := by
  rw [qf, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul,
    dotProduct_comm (uQ c) v]
  ring

theorem qf_smul (c : ShortIdx) (k : ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    qf c (k • M) = k * qf c M := by
  simp only [qf, smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem mulVec_dotProduct_symm {A : Matrix (Fin 24) (Fin 24) ℚ} (hA : Aᵀ = A) (v w : Fin 24 → ℚ) :
    (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (A *ᵥ w) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA]

theorem T_tensor_tensor_A (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) (A : symMat) :
    T (inW (tensor q v)) (inW (tensor q' w)) (inA A) =
      (q ⬝ᵥ q') * ((v ⬝ᵥ w) * trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8 +
        v ⬝ᵥ ((A : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ w)) := by
  have hA : (A : Matrix (Fin 24) (Fin 24) ℚ)ᵀ = A := A.2
  rw [T_WWA, fAWW, tensor_transpose_mul_tensor, trace_smul, trace_vecMulVec, Matrix.mul_smul,
    trace_smul, mul_vecMulVec, trace_vecMulVec, smul_eq_mul, smul_eq_mul,
    mulVec_dotProduct_symm hA]
  ring

theorem gWWX_tensor (c : ShortIdx) (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) :
    gWWX c (tensor q v) (tensor q' w) =
      ((q ᵥ* Rmat c) ⬝ᵥ q') * ((v ⬝ᵥ w) - (v ⬝ᵥ uQ c) * (w ⬝ᵥ uQ c) / 4) / 8 := by
  rw [gWWX, tensor_transpose_mul_R_mul_tensor, trace_smul, trace_vecMulVec, qf_smul, qf_vecMulVec,
    smul_eq_mul]
  ring

theorem T_tensor_tensor_Xlift (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) {r : Q}
    (hr : IsShortCoord (coordOf r)) :
    T (inW (tensor q v)) (inW (tensor q' w)) (inX (Xlift r)) =
      ((q ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) ⬝ᵥ q') *
        ((v ⬝ᵥ w) - (v ⬝ᵥ uQ ⟨coordOf r, hr⟩) * (w ⬝ᵥ uQ ⟨coordOf r, hr⟩) / 4) / 8 := by
  rw [T_WWX, Xlift_eq hr, sum_single_mul, gWWX_tensor, coe_Q_eq_sgn_smul_Rmat hr, vecMul_smul,
    smul_dotProduct, smul_eq_mul]
  ring

@[expose] def IsDyM {m n : Type*} (M : Matrix m n ℚ) : Prop := ∀ i j, M i j ∈ dyadic

theorem IsDyM.mul {l m n : Type*} [Fintype m] {M : Matrix l m ℚ} {N : Matrix m n ℚ}
    (hM : IsDyM M) (hN : IsDyM N) : IsDyM (M * N) :=
  fun i j => sum_mem fun k _ => mul_mem (hM i k) (hN k j)

theorem IsDyM.transpose {m n : Type*} {M : Matrix m n ℚ} (hM : IsDyM M) : IsDyM Mᵀ :=
  fun i j => hM j i

theorem IsDyM.trace_mem {n : Type*} [Fintype n] {M : Matrix n n ℚ} (hM : IsDyM M) :
    trace M ∈ dyadic :=
  sum_mem fun i _ => hM i i

theorem dotProduct_mem_dyadic {n : Type*} [Fintype n] {v w : n → ℚ} (hv : ∀ i, v i ∈ dyadic)
    (hw : ∀ i, w i ∈ dyadic) : v ⬝ᵥ w ∈ dyadic :=
  sum_mem fun i _ => mul_mem (hv i) (hw i)

theorem IsDyM.mulVec_mem {m n : Type*} [Fintype n] {M : Matrix m n ℚ} (hM : IsDyM M)
    {v : n → ℚ} (hv : ∀ i, v i ∈ dyadic) (i : m) : (M *ᵥ v) i ∈ dyadic :=
  dotProduct_mem_dyadic (hM i) hv

theorem inv_eight_mem_dyadic : (8 : ℚ)⁻¹ ∈ dyadic := by
  have h := inv_two_pow_mem_dyadic 3
  rwa [show ((2 : ℚ) ^ 3) = 8 by norm_num] at h

theorem inv_four_mem_dyadic : (4 : ℚ)⁻¹ ∈ dyadic := by
  have h := inv_two_pow_mem_dyadic 2
  rwa [show ((2 : ℚ) ^ 2) = 4 by norm_num] at h

theorem div_eight_mem_dyadic {x : ℚ} (hx : x ∈ dyadic) : x / 8 ∈ dyadic := by
  rw [div_eq_mul_inv]
  exact mul_mem hx inv_eight_mem_dyadic

theorem div_four_mem_dyadic {x : ℚ} (hx : x ∈ dyadic) : x / 4 ∈ dyadic := by
  rw [div_eq_mul_inv]
  exact mul_mem hx inv_four_mem_dyadic

theorem uQ_mem_dyadic (c : ShortIdx) (i : Fin 24) : uQ c i ∈ dyadic := intCast_mem dyadic _

theorem Rmat_isDyM (c : ShortIdx) : IsDyM (Rmat c) := fun i j => qmatR_mem_dyadic 0 _ _ i j

theorem qf_mem_dyadic (c : ShortIdx) {M : Matrix (Fin 24) (Fin 24) ℚ} (hM : IsDyM M) :
    qf c M ∈ dyadic :=
  dotProduct_mem_dyadic (uQ_mem_dyadic c) (hM.mulVec_mem (uQ_mem_dyadic c))

theorem tau_mem_dyadic (d e c : ShortIdx) : tau d e c ∈ dyadic := by
  unfold tau
  split_ifs
  · exact sgn_mem_dyadic _
  · exact zero_mem _

theorem fAWW_mem_dyadic {A : Matrix (Fin 24) (Fin 24) ℚ} {N N' : SpaceW} (hA : IsDyM A)
    (hN : IsDyM N) (hN' : IsDyM N') : fAWW A N N' ∈ dyadic :=
  add_mem (div_eight_mem_dyadic (mul_mem hA.trace_mem (hN.transpose.mul hN').trace_mem))
    (hA.mul (hN.transpose.mul hN')).trace_mem

theorem gWWX_mem_dyadic (c : ShortIdx) {N N' : SpaceW} (hN : IsDyM N) (hN' : IsDyM N') :
    gWWX c N N' ∈ dyadic := by
  have hM : IsDyM (Nᵀ * Rmat c * N') := (hN.transpose.mul (Rmat_isDyM c)).mul hN'
  exact div_eight_mem_dyadic (sub_mem hM.trace_mem (div_four_mem_dyadic (qf_mem_dyadic c hM)))

theorem Tex_mem_dyadic {u v w : SpaceB} (hu : IsDyadicVec u) (hv : IsDyadicVec v)
    (hw : IsDyadicVec w) : Tex u v w ∈ dyadic := by
  have hAu : IsDyM (Am u) := hu.1
  have hAv : IsDyM (Am v) := hv.1
  have hAw : IsDyM (Am w) := hw.1
  have hNu : IsDyM (Nm u) := hu.2.2
  have hNv : IsDyM (Nm v) := hv.2.2
  have hNw : IsDyM (Nm w) := hw.2.2
  have hxu : ∀ c, xs u c ∈ dyadic := hu.2.1
  have hxv : ∀ c, xs v c ∈ dyadic := hv.2.1
  have hxw : ∀ c, xs w c ∈ dyadic := hw.2.1
  have h4 : (4 : ℚ) ∈ dyadic := natCast_mem dyadic 4
  unfold Tex
  refine add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem
    (add_mem (mul_mem h4 ((hAu.mul hAv).mul hAw).trace_mem) ?_) ?_) ?_) ?_)
    (fAWW_mem_dyadic hAw hNu hNv)) (fAWW_mem_dyadic hAu hNv hNw)) (fAWW_mem_dyadic hAv hNu hNw))
    ?_) ?_) ?_
  · exact mul_mem inv_eight_mem_dyadic (sum_mem fun c _ =>
      mul_mem (mul_mem (hxu c) (hxv c)) (qf_mem_dyadic c hAw))
  · exact mul_mem inv_eight_mem_dyadic (sum_mem fun c _ =>
      mul_mem (mul_mem (hxv c) (hxw c)) (qf_mem_dyadic c hAu))
  · exact mul_mem inv_eight_mem_dyadic (sum_mem fun c _ =>
      mul_mem (mul_mem (hxu c) (hxw c)) (qf_mem_dyadic c hAv))
  · exact sum_mem fun c _ => sum_mem fun d _ => sum_mem fun e _ =>
      mul_mem (mul_mem (mul_mem (hxu d) (hxv e)) (hxw c)) (tau_mem_dyadic d e c)
  · exact sum_mem fun c _ => mul_mem (hxw c) (gWWX_mem_dyadic c hNu hNv)
  · exact sum_mem fun c _ => mul_mem (hxu c) (gWWX_mem_dyadic c hNv hNw)
  · exact sum_mem fun c _ => mul_mem (hxv c) (gWWX_mem_dyadic c hNu hNw)

theorem T_mem_dyadic {u v w : SpaceB} (hu : u ∈ BR) (hv : v ∈ BR) (hw : w ∈ BR) :
    T u v w ∈ dyadic := by
  rw [T_eq_Tex]
  exact Tex_mem_dyadic (mem_BR_iff.1 hu) (mem_BR_iff.1 hv) (mem_BR_iff.1 hw)

theorem isShortCoord_rep (c : ShortIdx) : IsShortCoord (coordOf (rep c.1)) :=
  (coordOf_rep c.1).symm ▸ c.2

theorem Xlift_rep_eq (c : ShortIdx) : Xlift (rep c.1) = Pi.single c 1 := by
  rw [Xlift_eq (isShortCoord_rep c), centralCoord_rep, sgn_zero, one_smul]
  congr 1
  exact Subtype.ext (coordOf_rep c.1)

@[expose] def IsGriessForm (T' : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ) : Prop :=
  (∀ A A' A'' : symMat, T' (inA A) (inA A') (inA A'') =
    4 * trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (A' : Matrix (Fin 24) (Fin 24) ℚ) *
      (A'' : Matrix (Fin 24) (Fin 24) ℚ))) ∧
  (∀ (r s : Q) (hr : IsShortCoord (coordOf r)) (_ : IsShortCoord (coordOf s)) (A : symMat),
    (∀ e : ZMod 2, r * s = zQ ^ e.val →
      T' (inX (Xlift r)) (inX (Xlift s)) (inA A) = sgn e * qf ⟨coordOf r, hr⟩ A / 8) ∧
    (r * s ∉ zpowers zQ → T' (inX (Xlift r)) (inX (Xlift s)) (inA A) = 0)) ∧
  (∀ r s t : Q, IsShortCoord (coordOf r) → IsShortCoord (coordOf s) →
    IsShortCoord (coordOf t) →
    (∀ e : ZMod 2, r * s * t = zQ ^ e.val →
      T' (inX (Xlift r)) (inX (Xlift s)) (inX (Xlift t)) = sgn e) ∧
    (r * s * t ∉ zpowers zQ → T' (inX (Xlift r)) (inX (Xlift s)) (inX (Xlift t)) = 0)) ∧
  (∀ (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) (A : symMat),
    T' (inW (tensor q v)) (inW (tensor q' w)) (inA A) =
      (q ⬝ᵥ q') * ((v ⬝ᵥ w) * trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8 +
        v ⬝ᵥ ((A : Matrix (Fin 24) (Fin 24) ℚ) *ᵥ w))) ∧
  (∀ (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) (r : Q) (hr : IsShortCoord (coordOf r)),
    T' (inW (tensor q v)) (inW (tensor q' w)) (inX (Xlift r)) =
      ((q ᵥ* ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) ⬝ᵥ q') *
        ((v ⬝ᵥ w) - (v ⬝ᵥ uQ ⟨coordOf r, hr⟩) * (w ⬝ᵥ uQ ⟨coordOf r, hr⟩) / 4) / 8) ∧
  (∀ (A A' : symMat) (x : SpaceX), T' (inA A) (inA A') (inX x) = 0) ∧
  (∀ (A A' : symMat) (N : SpaceW), T' (inA A) (inA A') (inW N) = 0) ∧
  (∀ (A : symMat) (x : SpaceX) (N : SpaceW), T' (inA A) (inX x) (inW N) = 0) ∧
  (∀ (x x' : SpaceX) (N : SpaceW), T' (inX x) (inX x') (inW N) = 0) ∧
  (∀ N N' N'' : SpaceW, T' (inW N) (inW N') (inW N'') = 0)

theorem isGriessForm_T : IsGriessForm T :=
  ⟨T_AAA, fun _ _ hr hs A => T_Xlift_Xlift_A hr hs A, fun _ _ _ hr hs ht => T_Xlift3 hr hs ht,
    T_tensor_tensor_A, fun q q' v w _ hr => T_tensor_tensor_Xlift q q' v w hr, T_AAX, T_AAW,
    T_AXW, T_XXW, T_WWW⟩

@[expose] def IsKA (u : SpaceB) : Prop := ∃ A, u = inA A

@[expose] def IsKX (u : SpaceB) : Prop := ∃ r : Q, IsShortCoord (coordOf r) ∧ u = inX (Xlift r)

@[expose] def IsKW (u : SpaceB) : Prop := ∃ q v, u = inW (tensor q v)

theorem eq_zero_of_kinds (D : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ)
    (h12 : ∀ u v w, D u v w = D v u w) (h23 : ∀ u v w, D u v w = D u w v)
    (hAAA : ∀ u v w, IsKA u → IsKA v → IsKA w → D u v w = 0)
    (hXXA : ∀ u v w, IsKX u → IsKX v → IsKA w → D u v w = 0)
    (hXXX : ∀ u v w, IsKX u → IsKX v → IsKX w → D u v w = 0)
    (hWWA : ∀ u v w, IsKW u → IsKW v → IsKA w → D u v w = 0)
    (hWWX : ∀ u v w, IsKW u → IsKW v → IsKX w → D u v w = 0)
    (hAAX : ∀ u v w, IsKA u → IsKA v → IsKX w → D u v w = 0)
    (hAAW : ∀ u v w, IsKA u → IsKA v → IsKW w → D u v w = 0)
    (hAXW : ∀ u v w, IsKA u → IsKX v → IsKW w → D u v w = 0)
    (hXXW : ∀ u v w, IsKX u → IsKX v → IsKW w → D u v w = 0)
    (hWWW : ∀ u v w, IsKW u → IsKW v → IsKW w → D u v w = 0)
    (u v w : SpaceB) (hu : IsKA u ∨ IsKX u ∨ IsKW u) (hv : IsKA v ∨ IsKX v ∨ IsKW v)
    (hw : IsKA w ∨ IsKX w ∨ IsKW w) : D u v w = 0 := by
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rcases hw with hw | hw | hw
  · exact hAAA u v w hu hv hw
  · exact hAAX u v w hu hv hw
  · exact hAAW u v w hu hv hw
  · rw [h23]; exact hAAX u w v hu hw hv
  · rw [h12, h23]; exact hXXA v w u hv hw hu
  · exact hAXW u v w hu hv hw
  · rw [h23]; exact hAAW u w v hu hw hv
  · rw [h23]; exact hAXW u w v hu hw hv
  · rw [h12, h23]; exact hWWA v w u hv hw hu
  · rw [h12, h23]; exact hAAX v w u hv hw hu
  · rw [h23]; exact hXXA u w v hu hw hv
  · rw [h12]; exact hAXW v u w hv hu hw
  · exact hXXA u v w hu hv hw
  · exact hXXX u v w hu hv hw
  · exact hXXW u v w hu hv hw
  · rw [h23, h12]; exact hAXW w u v hw hu hv
  · rw [h23]; exact hXXW u w v hu hw hv
  · rw [h12, h23]; exact hWWX v w u hv hw hu
  · rw [h12, h23]; exact hAAW v w u hv hw hu
  · rw [h12, h23]; exact hAXW v w u hv hw hu
  · rw [h23]; exact hWWA u w v hu hw hv
  · rw [h23, h12, h23]; exact hAXW w v u hw hv hu
  · rw [h12, h23]; exact hXXW v w u hv hw hu
  · rw [h23]; exact hWWX u w v hu hw hv
  · exact hWWA u v w hu hv hw
  · exact hWWX u v w hu hv hw
  · exact hWWW u v w hu hv hw

theorem kind_basisB (k : BIdx) : IsKA (basisB k) ∨ IsKX (basisB k) ∨ IsKW (basisB k) := by
  rcases k with z | c | k
  · exact Or.inl ⟨basisA z, basisB_inl z⟩
  · refine Or.inr (Or.inl ⟨rep c.1, isShortCoord_rep c, ?_⟩)
    rw [basisB_inr_inl, Xlift_rep_eq]
  · exact Or.inr (Or.inr ⟨Pi.single k.1 1, Pi.single k.2 1, basisB_inr_inr k⟩)

theorem T_unique (T' : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ)
    (h12 : ∀ u v w, T' u v w = T' v u w) (h23 : ∀ u v w, T' u v w = T' u w v)
    (hT' : IsGriessForm T') : T' = T := by
  have hDapp : ∀ u v w, (T' - T) u v w = T' u v w - T u v w := fun _ _ _ => rfl
  obtain ⟨tA, tXXA, tXXX, tWWA, tWWX, tAAX, tAAW, tAXW, tXXW, tWWW⟩ := hT'
  obtain ⟨sA, sXXA, sXXX, sWWA, sWWX, sAAX, sAAW, sAXW, sXXW, sWWW⟩ := isGriessForm_T
  have key := eq_zero_of_kinds (T' - T)
    (fun u v w => by rw [hDapp, hDapp, h12, T_swap12])
    (fun u v w => by rw [hDapp, hDapp, h23, T_swap23])
    (by
      rintro _ _ _ ⟨A, rfl⟩ ⟨A', rfl⟩ ⟨A'', rfl⟩
      rw [hDapp, tA, sA, sub_self])
    (by
      rintro _ _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩ ⟨A, rfl⟩
      rw [hDapp]
      by_cases h : r * s ∈ zpowers zQ
      · obtain ⟨e, he⟩ := exists_eq_zQ_pow h
        rw [(tXXA r s hr hs A).1 e he, (sXXA r s hr hs A).1 e he, sub_self]
      · rw [(tXXA r s hr hs A).2 h, (sXXA r s hr hs A).2 h, sub_self])
    (by
      rintro _ _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
      rw [hDapp]
      by_cases h : r * s * t ∈ zpowers zQ
      · obtain ⟨e, he⟩ := exists_eq_zQ_pow h
        rw [(tXXX r s t hr hs ht).1 e he, (sXXX r s t hr hs ht).1 e he, sub_self]
      · rw [(tXXX r s t hr hs ht).2 h, (sXXX r s t hr hs ht).2 h, sub_self])
    (by
      rintro _ _ _ ⟨q, v, rfl⟩ ⟨q', w, rfl⟩ ⟨A, rfl⟩
      rw [hDapp, tWWA, sWWA, sub_self])
    (by
      rintro _ _ _ ⟨q, v, rfl⟩ ⟨q', w, rfl⟩ ⟨r, hr, rfl⟩
      rw [hDapp, tWWX q q' v w r hr, sWWX q q' v w r hr, sub_self])
    (by
      rintro _ _ _ ⟨A, rfl⟩ ⟨A', rfl⟩ ⟨r, hr, rfl⟩
      rw [hDapp, tAAX, sAAX, sub_self])
    (by
      rintro _ _ _ ⟨A, rfl⟩ ⟨A', rfl⟩ ⟨q, v, rfl⟩
      rw [hDapp, tAAW, sAAW, sub_self])
    (by
      rintro _ _ _ ⟨A, rfl⟩ ⟨r, hr, rfl⟩ ⟨q, v, rfl⟩
      rw [hDapp, tAXW, sAXW, sub_self])
    (by
      rintro _ _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩ ⟨q, v, rfl⟩
      rw [hDapp, tXXW, sXXW, sub_self])
    (by
      rintro _ _ _ ⟨q, v, rfl⟩ ⟨q', w, rfl⟩ ⟨q'', w', rfl⟩
      rw [hDapp, tWWW, sWWW, sub_self])
  have hD : T' - T = 0 := basisB.ext fun i => basisB.ext fun j => basisB.ext fun k => by
    simp only [LinearMap.zero_apply]
    exact key _ _ _ (kind_basisB i) (kind_basisB j) (kind_basisB k)
  exact sub_eq_zero.1 hD

theorem rational_Griess_trilinear_data :
    IsGriessForm T ∧ (∀ u v w, T u v w = T v u w) ∧ (∀ u v w, T u v w = T u w v) ∧
    (∀ T' : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] ℚ, (∀ u v w, T' u v w = T' v u w) →
      (∀ u v w, T' u v w = T' u w v) → IsGriessForm T' → T' = T) ∧
    (∀ u v w, u ∈ BR → v ∈ BR → w ∈ BR → T u v w ∈ dyadic) :=
  ⟨isGriessForm_T, T_swap12, T_swap23, T_unique, fun _ _ _ hu hv hw => T_mem_dyadic hu hv hw⟩

end CFSG.Monster.Griess
