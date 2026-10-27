module

public import CFSG.Monster.Griess.Short
public import CFSG.Monster.FourierTriality
public import Mathlib.Data.Sym.Card

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin Matrix Module

@[expose] def symMat : Submodule ℚ (Matrix (Fin 24) (Fin 24) ℚ) where
  carrier := {A | Aᵀ = A}
  add_mem' {A B} hA hB := by
    change (A + B)ᵀ = A + B
    rw [transpose_add, hA, hB]
  zero_mem' := transpose_zero
  smul_mem' c A hA := by
    change (c • A)ᵀ = c • A
    rw [transpose_smul, hA]

theorem mem_symMat {A : Matrix (Fin 24) (Fin 24) ℚ} : A ∈ symMat ↔ Aᵀ = A := Iff.rfl

abbrev PairIdx : Type := Sym2 (Fin 24)

theorem card_pairIdx : Fintype.card PairIdx = 300 := by
  rw [Sym2.card, Fintype.card_fin]
  rfl

@[expose] def symEntry (A : symMat) : PairIdx → ℚ :=
  Sym2.lift ⟨fun i j => (A : Matrix (Fin 24) (Fin 24) ℚ) i j,
    fun i j => (congrFun (congrFun A.2 i) j).symm⟩

theorem symEntry_mk (A : symMat) (i j : Fin 24) :
    symEntry A s(i, j) = (A : Matrix (Fin 24) (Fin 24) ℚ) i j := Sym2.lift_mk _ _ _

@[expose] def symCoord : symMat ≃ₗ[ℚ] (PairIdx → ℚ) where
  toFun := symEntry
  map_add' A B := by
    funext z
    induction z using Sym2.ind with | h i j => simp [symEntry_mk]
  map_smul' c A := by
    funext z
    induction z using Sym2.ind with | h i j => simp [symEntry_mk]
  invFun f := ⟨Matrix.of fun i j => f s(i, j), by
      ext i j
      simp only [transpose_apply, of_apply, Sym2.eq_swap]⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp only [of_apply, symEntry_mk]
  right_inv f := by
    funext z
    induction z using Sym2.ind with | h i j => simp only [symEntry_mk, of_apply]

@[expose] noncomputable def basisA : Basis PairIdx ℚ symMat := Basis.ofEquivFun symCoord

theorem basisA_apply (z : PairIdx) (k l : Fin 24) :
    (basisA z : Matrix (Fin 24) (Fin 24) ℚ) k l = if s(k, l) = z then 1 else 0 := by
  rw [basisA, Basis.coe_ofEquivFun]
  change (Pi.single z 1 : PairIdx → ℚ) s(k, l) = _
  rw [Pi.single_apply]

theorem coe_basisA (i j : Fin 24) :
    (basisA s(i, j) : Matrix (Fin 24) (Fin 24) ℚ) =
      if i = j then Matrix.single i i 1 else Matrix.single i j 1 + Matrix.single j i 1 := by
  ext k l
  rw [basisA_apply]
  by_cases h : s(k, l) = s(i, j)
  · rw [if_pos h]
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · split_ifs with hkl
      · subst hkl; simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hkl]
    · split_ifs with hkl
      · subst hkl; simp [Matrix.single_apply]
      · simp [Matrix.single_apply, Ne.symm hkl]
  · rw [if_neg h]
    have h' : ¬ ((k = i ∧ l = j) ∨ (k = j ∧ l = i)) := fun h'' => h (Sym2.eq_iff.2 h'')
    split_ifs with hij
    · subst hij
      simp only [Matrix.single_apply]
      split_ifs with h3
      · exact absurd (Or.inl ⟨h3.1.symm, h3.2.symm⟩) h'
      · rfl
    · simp only [Matrix.add_apply, Matrix.single_apply]
      split_ifs with h3 h4 h4
      · exact absurd (Or.inl ⟨h3.1.symm, h3.2.symm⟩) h'
      · exact absurd (Or.inl ⟨h3.1.symm, h3.2.symm⟩) h'
      · exact absurd (Or.inr ⟨h4.1.symm, h4.2.symm⟩) h'
      · exact (add_zero 0).symm

abbrev SpaceX : Type := ShortIdx → ℚ

abbrev SpaceW : Type := Matrix SpinIdx (Fin 24) ℚ

abbrev SpaceB : Type := symMat × SpaceX × SpaceW

@[expose] def tensor (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) : SpaceW := vecMulVec q v

@[expose] noncomputable def Xlift (r : Q) : SpaceX :=
  open Classical in
  if h : IsShortCoord (coordOf r) then sgn (centralCoord r) • Pi.single ⟨coordOf r, h⟩ 1 else 0

@[expose] noncomputable def bform : LinearMap.BilinForm ℚ SpaceB :=
  LinearMap.mk₂ ℚ (fun u v => trace ((u.1 : Matrix (Fin 24) (Fin 24) ℚ) *
      (v.1 : Matrix (Fin 24) (Fin 24) ℚ)) +
      ∑ c, u.2.1 c * v.2.1 c + ∑ j, ∑ i, u.2.2 j i * v.2.2 j i)
    (fun u u' v => by
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_mul, trace_add,
        Pi.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      ring)
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Matrix.smul_mul, trace_smul,
        Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_assoc])
    (fun u v v' => by
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.mul_add, trace_add,
        Pi.add_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
      ring)
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Matrix.mul_smul, trace_smul,
        Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_left_comm])

theorem bform_apply (u v : SpaceB) :
    bform u v = trace ((u.1 : Matrix (Fin 24) (Fin 24) ℚ) * (v.1 : Matrix (Fin 24) (Fin 24) ℚ)) +
      ∑ c, u.2.1 c * v.2.1 c + ∑ j, ∑ i, u.2.2 j i * v.2.2 j i := rfl

theorem bform_tensor (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ) :
    bform (0, 0, tensor q v) (0, 0, tensor q' w) = (q ⬝ᵥ q') * (v ⬝ᵥ w) := by
  rw [bform_apply, dotProduct, dotProduct, Finset.sum_mul_sum]
  simp only [Submodule.coe_zero, Matrix.zero_mul, trace_zero, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, tensor, vecMulVec_apply]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

abbrev BIdx : Type := PairIdx ⊕ ShortIdx ⊕ (SpinIdx × Fin 24)

@[expose] noncomputable def basisB : Basis BIdx ℚ SpaceB :=
  basisA.prod ((Pi.basisFun ℚ ShortIdx).prod (Matrix.stdBasis ℚ SpinIdx (Fin 24)))

theorem basisB_inl (z : PairIdx) : basisB (Sum.inl z) = (basisA z, 0, 0) := by
  rw [basisB, Basis.prod_apply]
  rfl

theorem basisB_inr_inl (c : ShortIdx) : basisB (Sum.inr (Sum.inl c)) = (0, Pi.single c 1, 0) := by
  rw [basisB, Basis.prod_apply]
  simp [Basis.prod_apply]

theorem basisB_inr_inr (k : SpinIdx × Fin 24) :
    basisB (Sum.inr (Sum.inr k)) = (0, 0, tensor (Pi.single k.1 1) (Pi.single k.2 1)) := by
  obtain ⟨k₁, k₂⟩ := k
  rw [basisB, Basis.prod_apply]
  simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply, Basis.prod_apply, tensor]
  rw [Matrix.stdBasis_eq_single]
  congr 2
  ext i j
  simp only [Matrix.single_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

@[expose] noncomputable def BR : Submodule dyadic SpaceB := Submodule.span dyadic (Set.range basisB)

@[expose] def gramDiag : BIdx → ℚ
  | Sum.inl z => if z.IsDiag then 1 else 2
  | Sum.inr _ => 1

theorem sum_sym2_indicator (i j : Fin 24) :
    (∑ k : Fin 24, ∑ l : Fin 24, if s(k, l) = s(i, j) then (1 : ℚ) else 0) =
      if i = j then 1 else 2 := by
  rw [← Finset.sum_product', Finset.univ_product_univ, Finset.sum_boole]
  have hf : (Finset.univ.filter fun p : Fin 24 × Fin 24 => s(p.1, p.2) = s(i, j)) =
      {(i, j), (j, i)} := by
    ext ⟨k, l⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, Sym2.eq_iff]
  rw [hf]
  split_ifs with h
  · subst h
    simp
  · rw [Finset.card_pair (by simp [Prod.ext_iff, h])]
    norm_num

theorem trace_basisA_mul (z z' : PairIdx) :
    trace ((basisA z : Matrix (Fin 24) (Fin 24) ℚ) * (basisA z' : Matrix (Fin 24) (Fin 24) ℚ)) =
      if z = z' then gramDiag (Sum.inl z) else 0 := by
  simp only [trace, diag, Matrix.mul_apply, basisA_apply]
  have hswap : ∀ k l : Fin 24, s(l, k) = s(k, l) := fun k l => Sym2.eq_swap
  simp only [hswap]
  split_ifs with h
  · subst h
    have e : ∀ k l : Fin 24, ((if s(k, l) = z then (1 : ℚ) else 0) *
        (if s(k, l) = z then (1 : ℚ) else 0)) = if s(k, l) = z then 1 else 0 := by
      intro k l
      split_ifs <;> norm_num
    simp only [e]
    induction z using Sym2.ind with
    | h i j =>
      rw [sum_sym2_indicator]
      simp only [gramDiag, Sym2.mk_isDiag_iff]
  · refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    · simp
    · simp
    · simp

theorem single_dotProduct_single {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    (Pi.single i (1 : ℚ) : ι → ℚ) ⬝ᵥ Pi.single j 1 = if i = j then 1 else 0 := by
  rw [single_dotProduct, one_mul, Pi.single_apply]

open Classical in
theorem bform_basisB (k l : BIdx) :
    bform (basisB k) (basisB l) = if k = l then gramDiag k else 0 := by
  rcases k with z | c | t <;> rcases l with z' | c' | t'
  · rw [basisB_inl, basisB_inl, bform_apply, trace_basisA_mul]
    simp only [Pi.zero_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
      Sum.inl.injEq]
  · rw [basisB_inl, basisB_inr_inl, bform_apply]
    simp [Sum.inl_ne_inr]
  · rw [basisB_inl, basisB_inr_inr, bform_apply]
    simp [Sum.inl_ne_inr]
  · rw [basisB_inr_inl, basisB_inl, bform_apply]
    simp [Sum.inr_ne_inl]
  · rw [basisB_inr_inl, basisB_inr_inl, bform_apply]
    simp only [Submodule.coe_zero, Matrix.zero_mul, trace_zero, Matrix.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, Sum.inr.injEq, Sum.inl.injEq, gramDiag]
    rw [← dotProduct, single_dotProduct_single]
  · rw [basisB_inr_inl, basisB_inr_inr, bform_apply]
    simp
  · rw [basisB_inr_inr, basisB_inl, bform_apply]
    simp [Sum.inr_ne_inl]
  · rw [basisB_inr_inr, basisB_inr_inl, bform_apply]
    simp
  · rw [basisB_inr_inr, basisB_inr_inr]
    have h0 : ((0 : symMat), (0 : SpaceX), tensor (Pi.single t.1 1) (Pi.single t.2 1)) =
        (0, 0, tensor (Pi.single t.1 1) (Pi.single t.2 1)) := rfl
    rw [bform_tensor, single_dotProduct_single, single_dotProduct_single]
    simp only [Sum.inr.injEq, gramDiag, Prod.ext_iff]
    split_ifs <;> simp_all

theorem card_shortIdx' : Fintype.card ShortIdx = 98280 := by
  rw [← Nat.card_eq_fintype_card, card_shortIdx]

theorem finrank_S : finrank ℚ (SpinIdx → ℚ) = 4096 := by
  rw [Module.finrank_fintype_fun_eq_card, card_spinIdx]

theorem finrank_A : finrank ℚ symMat = 300 := by
  rw [finrank_eq_card_basis basisA, card_pairIdx]

theorem finrank_X : finrank ℚ SpaceX = 98280 := by
  rw [Module.finrank_fintype_fun_eq_card, card_shortIdx']

theorem finrank_W : finrank ℚ SpaceW = 98304 := by
  rw [Module.finrank_matrix, card_spinIdx, Fintype.card_fin, Module.finrank_self]

theorem finrank_B : finrank ℚ SpaceB = 196884 := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_A, finrank_X, finrank_W]

theorem bform_self (v : SpaceB) :
    bform v v = ∑ k, ∑ l, (v.1 : Matrix (Fin 24) (Fin 24) ℚ) k l ^ 2 + ∑ c, v.2.1 c ^ 2 +
      ∑ j, ∑ i, v.2.2 j i ^ 2 := by
  rw [bform_apply]
  congr 1
  · congr 1
    · simp only [trace, diag, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [show (v.1 : Matrix (Fin 24) (Fin 24) ℚ) l k = (v.1 : Matrix (Fin 24) (Fin 24) ℚ) k l from
        congrFun (congrFun v.1.2 k) l]
      ring
    · exact Finset.sum_congr rfl fun c _ => by ring
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem bform_self_pos {v : SpaceB} (hv : v ≠ 0) : 0 < bform v v := by
  rw [bform_self]
  have h1 : 0 ≤ ∑ k, ∑ l, (v.1 : Matrix (Fin 24) (Fin 24) ℚ) k l ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ c, v.2.1 c ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : 0 ≤ ∑ j, ∑ i, v.2.2 j i ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_contra hle
  have hsum : ∑ k, ∑ l, (v.1 : Matrix (Fin 24) (Fin 24) ℚ) k l ^ 2 + ∑ c, v.2.1 c ^ 2 +
      ∑ j, ∑ i, v.2.2 j i ^ 2 = 0 := by linarith
  have e1 : ∑ k, ∑ l, (v.1 : Matrix (Fin 24) (Fin 24) ℚ) k l ^ 2 = 0 := by linarith
  have e2 : ∑ c, v.2.1 c ^ 2 = 0 := by linarith
  have e3 : ∑ j, ∑ i, v.2.2 j i ^ 2 = 0 := by linarith
  apply hv
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · ext k l
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _).1 e1 k (Finset.mem_univ _)
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 this l (Finset.mem_univ _)
    simpa using this
  · funext c
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 e2 c (Finset.mem_univ _)
    simpa using this
  · ext j i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _).1 e3 j (Finset.mem_univ _)
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 this i (Finset.mem_univ _)
    simpa using this

theorem gramDiag_mem (k : BIdx) : gramDiag k = 1 ∨ gramDiag k = 2 := by
  rcases k with z | _
  · simp only [gramDiag]
    split_ifs <;> simp
  · exact .inl rfl

theorem gramDiag_inl_eq_two_iff (z : PairIdx) : gramDiag (Sum.inl z) = 2 ↔ ¬ z.IsDiag := by
  simp only [gramDiag]
  split_ifs with h <;> simp [h]

theorem card_offDiag : Fintype.card {z : PairIdx // ¬ z.IsDiag} = 276 := by
  rw [Sym2.card_subtype_not_diag, Fintype.card_fin]
  rfl

theorem two_mem_dyadic_inv : ((2 : ℚ))⁻¹ ∈ dyadic := by
  have := inv_two_pow_mem_dyadic 1
  simpa using this

open Classical in
theorem gram_invertible_dyadic :
    (Matrix.of fun k l => bform (basisB k) (basisB l)) * Matrix.diagonal (fun k => (gramDiag k)⁻¹) = 1 ∧
      (∀ k l, (Matrix.of fun k l => bform (basisB k) (basisB l)) k l ∈ dyadic) ∧
      ∀ k l, Matrix.diagonal (fun k => (gramDiag k)⁻¹) k l ∈ dyadic := by
  have hG : (Matrix.of fun k l => bform (basisB k) (basisB l)) = Matrix.diagonal gramDiag := by
    ext k l
    rw [of_apply, bform_basisB, Matrix.diagonal_apply]
  refine ⟨?_, fun k l => ?_, fun k l => ?_⟩
  · rw [hG, Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one with k
    rcases gramDiag_mem k with h | h <;> rw [h] <;> norm_num
  · rw [hG, Matrix.diagonal_apply]
    split_ifs
    · rcases gramDiag_mem k with h | h <;> rw [h]
      · exact dyadic.one_mem
      · have h2 : (2 : ℚ) = 1 + 1 := by norm_num
        rw [h2]
        exact dyadic.add_mem dyadic.one_mem dyadic.one_mem
    · exact dyadic.zero_mem
  · rw [Matrix.diagonal_apply]
    split_ifs
    · rcases gramDiag_mem k with h | h <;> rw [h]
      · simpa using dyadic.one_mem
      · exact two_mem_dyadic_inv
    · exact dyadic.zero_mem

theorem Xlift_eq {r : Q} (h : IsShortCoord (coordOf r)) :
    Xlift r = sgn (centralCoord r) • Pi.single ⟨coordOf r, h⟩ 1 := by
  unfold Xlift
  exact dif_pos h

theorem gramDiag_inr (k : ShortIdx ⊕ (SpinIdx × Fin 24)) : gramDiag (Sum.inr k) = 1 := rfl

open Classical in
theorem rational_algebra_space_data :
    (∀ r : Q, IsShort (QuotientGroup.mk r) ↔ IsShortCoord (coordOf r)) ∧
    Nat.card ShortIdx = 98280 ∧
    (∀ p : C × Cocode, coordOf (rep p) = p ∧ centralCoord (rep p) = 0 ∧
      ((rep p : Q) : GL SpinIdx ℚ) = TU p.1 * DU p.2) ∧
    (∀ r : Q, r = zQ ^ (centralCoord r).val * rep (coordOf r)) ∧
    (∀ r : Q, IsShortCoord (coordOf r) → r ^ 2 = 1) ∧
    (∀ c : ShortIdx, uvec c ∈ minVecs ∧ classOf (uvec c) = SpinLattice.phi0 c.1 ∧
      LexLE (uvec c) (-uvec c) ∧
      ∀ v ∈ minVecs, classOf v = SpinLattice.phi0 c.1 → LexLE v (-v) → v = uvec c) ∧
    (∀ (r : Q) (h : IsShortCoord (coordOf r)),
      Xlift r = sgn (centralCoord r) • Pi.single ⟨coordOf r, h⟩ 1) ∧
    finrank ℚ (SpinIdx → ℚ) = 4096 ∧ finrank ℚ symMat = 300 ∧ finrank ℚ SpaceX = 98280 ∧
    finrank ℚ SpaceW = 98304 ∧ finrank ℚ SpaceB = 196884 ∧
    (∀ (q q' : SpinIdx → ℚ) (v w : Fin 24 → ℚ),
      bform (0, 0, tensor q v) (0, 0, tensor q' w) = (q ⬝ᵥ q') * (v ⬝ᵥ w)) ∧
    (∀ z, basisB (Sum.inl z) = (basisA z, 0, 0)) ∧
    (∀ i j : Fin 24, (basisA s(i, j) : Matrix (Fin 24) (Fin 24) ℚ) =
      if i = j then Matrix.single i i 1 else Matrix.single i j 1 + Matrix.single j i 1) ∧
    (∀ c, basisB (Sum.inr (Sum.inl c)) = (0, Pi.single c 1, 0)) ∧
    (∀ k : SpinIdx × Fin 24,
      basisB (Sum.inr (Sum.inr k)) = (0, 0, tensor (Pi.single k.1 1) (Pi.single k.2 1))) ∧
    BR = Submodule.span dyadic (Set.range basisB) ∧
    (∀ k l, bform (basisB k) (basisB l) = if k = l then gramDiag k else 0) ∧
    (∀ z, gramDiag (Sum.inl z) = 2 ↔ ¬ z.IsDiag) ∧ (∀ k, gramDiag (Sum.inr k) = 1) ∧
    (∀ z, z.IsDiag → gramDiag (Sum.inl z) = 1) ∧
    Fintype.card {z : PairIdx // ¬ z.IsDiag} = 276 ∧
    (∀ v : SpaceB, v ≠ 0 → 0 < bform v v) ∧
    ((Matrix.of fun k l => bform (basisB k) (basisB l)) *
        Matrix.diagonal (fun k => (gramDiag k)⁻¹) = 1 ∧
      (∀ k l, (Matrix.of fun k l => bform (basisB k) (basisB l)) k l ∈ dyadic) ∧
      ∀ k l, Matrix.diagonal (fun k => (gramDiag k)⁻¹) k l ∈ dyadic) :=
  ⟨isShort_mk_iff, card_shortIdx,
    fun p => ⟨coordOf_rep p, centralCoord_rep p, coe_rep p⟩, eq_zQ_pow_mul_rep,
    fun _ h => sq_eq_one_of_isShort h,
    fun c => ⟨uvec_mem c, classOf_uvec c, (uvec_spec c).2.2, fun _ hv hcl hle => eq_uvec hv hcl hle⟩,
    fun _ h => Xlift_eq h, finrank_S, finrank_A, finrank_X, finrank_W, finrank_B, bform_tensor,
    basisB_inl, coe_basisA, basisB_inr_inl, basisB_inr_inr, rfl, bform_basisB,
    gramDiag_inl_eq_two_iff, gramDiag_inr,
    fun z hz => by simp only [gramDiag]; exact if_pos hz, card_offDiag,
    fun _ hv => bform_self_pos hv, gram_invertible_dyadic⟩

end CFSG.Monster.Griess
