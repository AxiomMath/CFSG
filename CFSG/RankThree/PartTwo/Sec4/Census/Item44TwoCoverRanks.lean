module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
import CFSG.LieType.SteinbergBRTwoRankBound

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp sympForm)

theorem sl2_coe_eq_one_or_eq_neg_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {A : SpecialLinearGroup (Fin 2) F} (hA : A * A = 1) :
    (A : Matrix (Fin 2) (Fin 2) F) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.prop
  rw [det_fin_two] at hdet
  have hAA : (A : Matrix (Fin 2) (Fin 2) F) * A = 1 := congrArg Subtype.val hA
  have e00 := congrFun (congrFun hAA 0) 0
  have e01 := congrFun (congrFun hAA 0) 1
  have e10 := congrFun (congrFun hAA 1) 0
  have e11 := congrFun (congrFun hAA 1) 1
  simp only [mul_apply, Fin.sum_univ_two, one_apply_eq, one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e00 e01 e10 e11
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1
  by_cases had : a + d = 0
  · exfalso
    apply h2
    have hd : d = -a := by linear_combination had
    rw [hd] at hdet
    linear_combination -e00 - hdet
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right had
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right had
    rw [hb, hc] at hdet
    rw [hb, hc] at e00 e11
    have hda : (a - d) ^ 2 = 0 := by linear_combination e00 + e11 - 2 * hdet
    have had' : d = a := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hda
      linear_combination -this
    have ha : (a - 1) * (a + 1) = 0 := by linear_combination e00
    rcases mul_eq_zero.mp ha with h | h
    · left
      ext i j
      fin_cases i <;> fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, one_apply_eq]
        change a = 1
        linear_combination h
      · simpa using hb
      · simpa using hc
      · simp only [Fin.mk_one, Fin.isValue, one_apply_eq]
        change d = 1
        linear_combination had' + h
    · right
      ext i j
      fin_cases i <;> fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.neg_apply, one_apply_eq]
        change a = -1
        linear_combination h
      · simpa using hb
      · simpa using hc
      · simp only [Fin.mk_one, Fin.isValue, Matrix.neg_apply, one_apply_eq]
        change d = -1
        linear_combination had' + h

theorem pRank_two_SL2_le {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) :
    CFSG.pRank 2 (SpecialLinearGroup (Fin 2) F) ≤ 1 := by
  classical
  refine CFSG.LieType.SteinbergBR.pRank_le_of_card_le one_lt_two fun E hE => ?_
  have hsq : ∀ x : E, (x : SpecialLinearGroup (Fin 2) F) * x = 1 := fun x => by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x x.2
    rwa [sq] at this
  have hval : ∀ x y : E, ((x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((y : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) → x = y :=
    fun x y h => Subtype.ext (Subtype.ext h)
  have hne : (-1 : Matrix (Fin 2) (Fin 2) F) ≠ 1 := fun h => by
    have h' := congrFun (congrFun h 0) 0
    simp only [Matrix.neg_apply, one_apply_eq] at h'
    exact h2 (by linear_combination -h')
  let f : E → Bool := fun x =>
    decide (((x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1)
  have hf : Function.Injective f := by
    intro x y hxy
    apply hval
    rcases sl2_coe_eq_one_or_eq_neg_one h2 (hsq x) with hx | hx <;>
      rcases sl2_coe_eq_one_or_eq_neg_one h2 (hsq y) with hy | hy
    · rw [hx, hy]
    · simp only [f, hx, hy, decide_true, hne, decide_false] at hxy
      exact absurd hxy (by decide)
    · simp only [f, hx, hy, decide_true, hne, decide_false] at hxy
      exact absurd hxy (by decide)
    · rw [hx, hy]
  calc Nat.card E ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
    _ = 2 ^ 1 := by simp

section SqZero

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {V : Type} [AddCommGroup V]

@[expose] noncomputable def sqZeroUnit (N : V →+ Matrix ι ι K) (h0 : ∀ x y, N x * N y = 0)
    (x : V) : GL ι K :=
  ⟨1 + N x, 1 - N x, by rw [add_mul, one_mul, mul_sub, mul_one, h0, sub_zero, sub_add_cancel],
    by rw [sub_mul, one_mul, mul_add, mul_one, h0, add_zero, add_sub_cancel_right]⟩

@[expose] noncomputable def sqZeroHom (N : V →+ Matrix ι ι K) (h0 : ∀ x y, N x * N y = 0) :
    Multiplicative V →* GL ι K where
  toFun x := sqZeroUnit N h0 (Multiplicative.toAdd x)
  map_one' := Units.ext (by
    change 1 + N (Multiplicative.toAdd 1) = 1
    rw [toAdd_one, map_zero, add_zero])
  map_mul' x y := Units.ext (by
    change 1 + N (Multiplicative.toAdd x + Multiplicative.toAdd y) =
      (1 + N (Multiplicative.toAdd x)) * (1 + N (Multiplicative.toAdd y))
    rw [map_add, add_mul, one_mul, mul_add, mul_one, h0, add_zero]
    abel)

theorem le_pRank_of_sqZero [Nonempty ι] [Finite K] [Finite V] {p : ℕ} [Fact p.Prime]
    (N : V →+ Matrix ι ι K) (hN : Function.Injective N) (h0 : ∀ x y, N x * N y = 0)
    (hp : ∀ x : V, p • x = 0) (H : Subgroup (ProjGenLinGroup ι K))
    (hH : ∀ x, ProjGenLinGroup.mk (sqZeroUnit N h0 x) ∈ H) {k : ℕ} (hk : Nat.card V = p ^ k) :
    k ≤ CFSG.pRank p H := by
  have : Finite (GL ι K) := Finite.of_injective _ Units.val_injective
  have : Finite (ProjGenLinGroup ι K) :=
    Finite.of_surjective _ (ProjGenLinGroup.mk_surjective (n := ι) (R := K))
  let φ : Multiplicative V →* H :=
    (ProjGenLinGroup.mk.comp (sqZeroHom N h0)).codRestrict H fun x => hH _
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ProjGenLinGroup.mk (sqZeroUnit N h0 (Multiplicative.toAdd x)) = 1 :=
      congrArg Subtype.val hx
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h1
    obtain ⟨a, ha⟩ := h1
    have ha' : scalar ι a = 1 + N (Multiplicative.toAdd x) := ha
    have hNx : N (Multiplicative.toAdd x) = scalar ι (a - 1) := by
      rw [map_sub, map_one, ha', add_sub_cancel_left]
    have hsq := h0 (Multiplicative.toAdd x) (Multiplicative.toAdd x)
    rw [hNx, ← map_mul, ← map_zero (scalar ι), scalar_inj] at hsq
    have hN0 : N (Multiplicative.toAdd x) = 0 := by
      rw [hNx, mul_self_eq_zero.mp hsq, map_zero]
    exact hN (hN0.trans (map_zero N).symm)
  have hcard : Nat.card φ.range = p ^ k := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφ, Subgroup.card_top]
    exact hk
  have hEA : IsElementaryAbelian p φ.range := by
    refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul,
        mul_comm])
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun ⟨_, a, rfl⟩ => Subtype.ext ?_
      rw [Subgroup.coe_pow, ← map_pow, Subgroup.coe_one]
      have : a ^ p = 1 := by
        change Multiplicative.ofAdd (p • Multiplicative.toAdd a) = 1
        rw [hp, ofAdd_zero]
      rw [this, map_one]
  exact CFSG.LieType.SteinbergBR.le_pRank_of_card (Fact.out : p.Prime).one_lt _ hEA hcard

end SqZero

section Linear

variable (K : Type) [Field K]

@[expose] def radL4 : (Fin 4 → K) →+ Matrix (Fin 4) (Fin 4) K where
  toFun v := !![0, 0, v 0, v 1; 0, 0, v 2, v 3; 0, 0, 0, 0; 0, 0, 0, 0]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem radL4_injective : Function.Injective (radL4 K) := by
  intro v w h
  funext i
  have h02 := congrFun (congrFun h 0) 2
  have h03 := congrFun (congrFun h 0) 3
  have h12 := congrFun (congrFun h 1) 2
  have h13 := congrFun (congrFun h 1) 3
  simp [radL4] at h02 h03 h12 h13
  fin_cases i <;> assumption

theorem radL4_mul (v w : Fin 4 → K) : radL4 K v * radL4 K w = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radL4, mul_apply, Fin.sum_univ_four]

theorem le_pRank_projSL_four [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {k : ℕ}
    (hk : Nat.card K = p ^ k) : 4 * k ≤ CFSG.pRank p (projSL 4 K) := by
  refine le_pRank_of_sqZero (radL4 K) (radL4_injective K) (radL4_mul K)
    (fun v => funext fun i => by simp [nsmul_eq_mul]) (projSL 4 K) (fun v => ?_) ?_
  · refine ⟨sqZeroUnit (radL4 K) (radL4_mul K) v, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    change (1 + radL4 K v).det = 1
    rw [det_of_isUpperTriangular]
    · simp [Fin.prod_univ_four, radL4]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [radL4]
  · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin, hk, ← pow_mul,
      mul_comm]

end Linear

section Symplectic

variable (K : Type) [Field K]

@[expose] def symMat (v : Fin 3 → K) : Matrix (Fin 2) (Fin 2) K := !![v 0, v 1; v 1, v 2]

omit [Field K] in
theorem symMat_transpose (v : Fin 3 → K) : (symMat K v)ᵀ = symMat K v := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def radSp4 : (Fin 3 → K) →+ Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun v := fromBlocks 0 (symMat K v) 0 0
  map_zero' := by
    rw [← fromBlocks_zero]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_add' v w := by
    simp only [fromBlocks_add, add_zero]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symMat]

theorem radSp4_injective : Function.Injective (radSp4 K) := by
  intro v w h
  have h00 := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
  have h01 := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 1)
  have h11 := congrFun (congrFun h (Sum.inl 1)) (Sum.inr 1)
  simp only [radSp4, AddMonoidHom.coe_mk, ZeroHom.coe_mk, fromBlocks_apply₁₂, symMat] at h00 h01 h11
  funext i
  fin_cases i
  · simpa using h00
  · simpa using h01
  · simpa using h11

theorem radSp4_mul (v w : Fin 3 → K) : radSp4 K v * radSp4 K w = 0 := by
  simp only [radSp4, AddMonoidHom.coe_mk, ZeroHom.coe_mk, fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, fromBlocks_zero]

theorem le_pRank_projSp_two [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {k : ℕ}
    (hk : Nat.card K = p ^ k) : 3 * k ≤ CFSG.pRank p (projSp 2 K) := by
  refine le_pRank_of_sqZero (radSp4 K) (radSp4_injective K) (radSp4_mul K)
    (fun v => funext fun i => by simp [nsmul_eq_mul]) (projSp 2 K) (fun v => ?_) ?_
  · refine ⟨sqZeroUnit (radSp4 K) (radSp4_mul K) v, Subgroup.subset_closure ?_, rfl⟩
    change (1 + radSp4 K v)ᵀ * sympForm 2 K * (1 + radSp4 K v) = sympForm 2 K
    rw [← fromBlocks_one]
    simp only [radSp4, AddMonoidHom.coe_mk, ZeroHom.coe_mk, sympForm, fromBlocks_add,
      fromBlocks_transpose, fromBlocks_multiply]
    simp [symMat_transpose]
  · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, hk, ← pow_mul,
      mul_comm]

end Symplectic

section Unitary

variable {p : ℕ} [Fact p.Prime] {f : ℕ}

theorem exists_pow_eq_neg (hf : 1 ≤ f) :
    ∃ δ : GaloisField p (2 * f), δ ≠ 0 ∧ δ ^ p ^ f = -δ := by
  have hp := (Fact.out : p.Prime)
  have := Fintype.ofFinite (GaloisField p (2 * f))
  have hK : Fintype.card (GaloisField p (2 * f)) = p ^ f * p ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p (2 * f) (by omega), ← pow_add, two_mul]
  have hsq : ∀ x : GaloisField p (2 * f), (x ^ p ^ f) ^ p ^ f = x := fun x => by
    rw [← pow_mul, ← hK, FiniteField.pow_card]
  have hq : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  obtain ⟨x, hx⟩ : ∃ x : GaloisField p (2 * f), x ^ p ^ f ≠ x := by
    by_contra h
    have h' : ∀ x : GaloisField p (2 * f), x ^ p ^ f = x := fun x =>
      not_not.mp fun hne => h ⟨x, hne⟩
    have h1 : ∀ u : (GaloisField p (2 * f))ˣ, u ^ (p ^ f - 1) = 1 := fun u => by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      apply mul_right_cancel₀ u.ne_zero
      rw [← pow_succ, Nat.sub_add_cancel (by omega), h' u, one_mul]
    have h2 := (FiniteField.forall_pow_eq_one_iff (GaloisField p (2 * f)) (p ^ f - 1)).mp h1
    rw [hK] at h2
    have h3 := Nat.le_of_dvd (by omega) h2
    have h4 : p ^ f * 2 ≤ p ^ f * p ^ f := Nat.mul_le_mul_left _ hq
    generalize p ^ f * p ^ f = Q at h3 h4
    omega
  refine ⟨x - x ^ p ^ f, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [sub_pow_char_pow, hsq, neg_sub]

variable (p f) in
@[expose] noncomputable def frobQ : GaloisField p (2 * f) →+* GaloisField p (2 * f) :=
  iterateFrobenius (GaloisField p (2 * f)) p f

theorem frobQ_apply (x : GaloisField p (2 * f)) : frobQ p f x = x ^ p ^ f := rfl

theorem frobQ_frobQ (hf : 1 ≤ f) (x : GaloisField p (2 * f)) : frobQ p f (frobQ p f x) = x := by
  have := Fintype.ofFinite (GaloisField p (2 * f))
  have hK : Fintype.card (GaloisField p (2 * f)) = p ^ f * p ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p (2 * f) (by omega), ← pow_add, two_mul]
  rw [frobQ_apply, frobQ_apply, ← pow_mul, ← hK, FiniteField.pow_card]

theorem frobQ_algebraMap (t : ZMod p) :
    frobQ p f (algebraMap (ZMod p) (GaloisField p (2 * f)) t) =
      algebraMap (ZMod p) (GaloisField p (2 * f)) t := by
  rw [frobQ_apply, ← map_pow, ZMod.pow_card_pow]

@[expose] def isoFrame (a b : ZMod p) : Matrix (Fin 4) (Fin 2) (ZMod p) :=
  !![1, 0; 0, 1; a, b; b, -a]

theorem isoFrame_transpose_mul {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1) :
    (isoFrame a b)ᵀ * isoFrame a b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [isoFrame, Matrix.mul_apply, Fin.sum_univ_four]
    linear_combination hab
  · simp [isoFrame, Matrix.mul_apply, Fin.sum_univ_four]
    ring
  · simp [isoFrame, Matrix.mul_apply, Fin.sum_univ_four]
    ring
  · simp [isoFrame, Matrix.mul_apply, Fin.sum_univ_four]
    linear_combination hab

variable (f) in
@[expose] noncomputable def isoFrameK (a b : ZMod p) :
    Matrix (Fin 4) (Fin 2) (GaloisField p (2 * f)) :=
  (isoFrame a b).map (algebraMap (ZMod p) (GaloisField p (2 * f)))

theorem isoFrameK_transpose_mul {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1) :
    (isoFrameK f a b)ᵀ * isoFrameK f a b = 0 := by
  rw [isoFrameK, ← Matrix.transpose_map, ← Matrix.map_mul, isoFrame_transpose_mul hab,
    Matrix.map_zero _ (map_zero _)]

theorem isoFrameK_map_frobQ (a b : ZMod p) :
    (isoFrameK f a b).map (frobQ p f) = isoFrameK f a b := by
  rw [isoFrameK, Matrix.map_map]
  congr 1
  funext t
  exact frobQ_algebraMap t

variable (f) in
@[expose] noncomputable def skewMat (δ : GaloisField p (2 * f)) :
    GaloisField p (2 * f) × ZMod p × ZMod p →+ Matrix (Fin 2) (Fin 2) (GaloisField p (2 * f)) where
  toFun v := !![δ * algebraMap (ZMod p) _ v.2.1, v.1;
    -frobQ p f v.1, δ * algebraMap (ZMod p) _ v.2.2]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_add, add_comm]

theorem skewMat_conj (hf : 1 ≤ f) {δ : GaloisField p (2 * f)} (hδ : frobQ p f δ = -δ)
    (v : GaloisField p (2 * f) × ZMod p × ZMod p) :
    ((skewMat f δ v).map (frobQ p f))ᵀ = -skewMat f δ v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMat, hδ, frobQ_algebraMap, frobQ_frobQ hf]

variable (f) in
@[expose] noncomputable def radU4 (a b : ZMod p) (δ : GaloisField p (2 * f)) :
    GaloisField p (2 * f) × ZMod p × ZMod p →+ Matrix (Fin 4) (Fin 4) (GaloisField p (2 * f)) where
  toFun v := isoFrameK f a b * skewMat f δ v * (isoFrameK f a b)ᵀ
  map_zero' := by rw [map_zero, Matrix.mul_zero, Matrix.zero_mul]
  map_add' v w := by rw [map_add, Matrix.mul_add, Matrix.add_mul]

theorem radU4_apply (a b : ZMod p) (δ : GaloisField p (2 * f)) (v) :
    radU4 f a b δ v = isoFrameK f a b * skewMat f δ v * (isoFrameK f a b)ᵀ := rfl

theorem radU4_mul {a b : ZMod p} (hab : a ^ 2 + b ^ 2 = -1) (δ : GaloisField p (2 * f)) (v w) :
    radU4 f a b δ v * radU4 f a b δ w = 0 := by
  rw [radU4_apply, radU4_apply]
  calc isoFrameK f a b * skewMat f δ v * (isoFrameK f a b)ᵀ *
        (isoFrameK f a b * skewMat f δ w * (isoFrameK f a b)ᵀ) =
      isoFrameK f a b * skewMat f δ v * ((isoFrameK f a b)ᵀ * isoFrameK f a b) *
        skewMat f δ w * (isoFrameK f a b)ᵀ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [isoFrameK_transpose_mul hab]; simp

theorem radU4_injective (a b : ZMod p) {δ : GaloisField p (2 * f)} (hδ : δ ≠ 0) :
    Function.Injective (radU4 f a b δ) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  have h00 := congrFun (congrFun hv 0) 0
  have h01 := congrFun (congrFun hv 0) 1
  have h11 := congrFun (congrFun hv 1) 1
  simp [radU4_apply, isoFrameK, isoFrame, skewMat, Matrix.mul_apply, Fin.sum_univ_two, hδ]
    at h00 h01 h11
  exact Prod.ext h01 (Prod.ext h00 h11)

theorem radU4_conj (hf : 1 ≤ f) (a b : ZMod p) {δ : GaloisField p (2 * f)}
    (hδ : frobQ p f δ = -δ) (v) :
    ((radU4 f a b δ v).map (frobQ p f))ᵀ = -radU4 f a b δ v := by
  rw [radU4_apply, Matrix.map_mul, Matrix.map_mul, isoFrameK_map_frobQ, Matrix.transpose_map,
    isoFrameK_map_frobQ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    skewMat_conj hf hδ, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem le_pRank_projSU_four (hf : 1 ≤ f) : 2 * f + 2 ≤ CFSG.pRank p (projSU 4 p f) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  obtain ⟨δ, hδ0, hδ⟩ := exists_pow_eq_neg (p := p) hf
  have hδ' : frobQ p f δ = -δ := hδ
  have h0 := radU4_mul (f := f) hab δ
  refine le_pRank_of_sqZero (radU4 f a b δ) (radU4_injective a b hδ0) h0
    (fun v => by
      simp only [Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero]
      simp only [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, and_self])
    (projSU 4 p f) (fun v => ⟨sqZeroUnit _ h0 v, Subgroup.subset_closure ⟨?_, ?_⟩, rfl⟩) ?_
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    change (1 + radU4 f a b δ v).det = 1
    rw [radU4_apply, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc,
      isoFrameK_transpose_mul hab, Matrix.mul_zero, add_zero, det_one]
  · change ((1 + radU4 f a b δ v).map (frobQ p f))ᵀ * (1 + radU4 f a b δ v) = 1
    rw [← RingHom.mapMatrix_apply, map_add, map_one, RingHom.mapMatrix_apply, transpose_add,
      transpose_one, radU4_conj hf a b hδ', ← sub_eq_add_neg, sub_mul, one_mul, mul_add, mul_one,
      h0, add_zero, add_sub_cancel_right]
  · rw [Nat.card_prod, Nat.card_prod, GaloisField.card p (2 * f) (by omega), Nat.card_zmod,
      ← pow_two, ← pow_add]

end Unitary

section UnitarySix

@[expose] def suSet (n : ℕ) (K : Type) [Field K] (q : ℕ) : Set (GL (Fin n) K) :=
  {A | GeneralLinearGroup.det A = 1 ∧
    ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1}

@[expose] noncomputable def diagHom {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] :
    (ι → Kˣ) →* GL ι K :=
  (Units.map (diagonalRingHom ι K).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem coe_diagHom {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → Kˣ) :
    (diagHom d : Matrix ι ι K) = diagonal fun i => (d i : K) := rfl

@[expose] noncomputable def torus6 {K : Type} [Field K] : (Fin 4 → Kˣ) →* (Fin 6 → Kˣ) where
  toFun x := ![x 0, x 1, x 2, x 3, (x 0 * x 1 * x 2 * x 3)⁻¹, 1]
  map_one' := by funext i; fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem three_lt_pRank_unitary_six {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 4) :
    3 < CFSG.pRank 3 (projImage (Subgroup.closure (suSet 6 K (2 ^ 1)))) := by
  classical
  have : Finite (GL (Fin 6) K) := Finite.of_injective _ Units.val_injective
  have : Finite (ProjGenLinGroup (Fin 6) K) :=
    Finite.of_surjective _ (ProjGenLinGroup.mk_surjective (n := Fin 6) (R := K))
  have hu3 : ∀ u : Kˣ, (u : K) ^ 3 = 1 := fun u => by
    have := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
    rwa [hK] at this
  have hmem : ∀ x : Fin 4 → Kˣ, diagHom (torus6 x) ∈ suSet 6 K (2 ^ 1) := fun x => by
    refine ⟨Units.ext ?_, ?_⟩
    · rw [GeneralLinearGroup.val_det_apply, coe_diagHom, det_diagonal, Fin.prod_univ_six,
        Units.val_one]
      simp only [torus6, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val]
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul,
        mul_one, mul_inv_cancel, Units.val_one]
    · rw [coe_diagHom, Matrix.diagonal_map (by simp), diagonal_transpose, diagonal_mul_diagonal,
        ← diagonal_one]
      congr 1
      funext i
      rw [← pow_succ]
      exact hu3 _
  let φ : (Fin 4 → Kˣ) →* projImage (Subgroup.closure (suSet 6 K (2 ^ 1))) :=
    (ProjGenLinGroup.mk.comp (diagHom.comp torus6)).codRestrict _ fun x =>
      ⟨_, Subgroup.subset_closure (hmem x), rfl⟩
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ProjGenLinGroup.mk (diagHom (torus6 x)) = 1 := congrArg Subtype.val hx
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h1
    obtain ⟨c, hc⟩ := h1
    have hent : ∀ j : Fin 6, ((torus6 x j : Kˣ) : K) = c := fun j => by
      have := congrFun (congrFun hc j) j
      rw [coe_diagHom, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at this
      exact this.symm
    have hc1 : c = 1 := by
      have := hent 5
      simp [torus6] at this
      exact this.symm
    funext i
    apply Units.ext
    have := hent (Fin.castLE (by norm_num) i)
    fin_cases i <;> simpa [torus6, hc1] using this
  have hcard : Nat.card φ.range = 3 ^ 4 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφ, Subgroup.card_top,
      Nat.card_fun, Nat.card_eq_fintype_card (α := Kˣ), Fintype.card_units, hK,
      Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
  have hEA : IsElementaryAbelian 3 φ.range := by
    refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul,
        mul_comm])
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun ⟨_, a, rfl⟩ => Subtype.ext ?_
      rw [Subgroup.coe_pow, ← map_pow, Subgroup.coe_one]
      have : a ^ 3 = 1 := funext fun i => Units.ext (by
        rw [Pi.pow_apply, Units.val_pow_eq_pow_val, hu3, Pi.one_apply, Units.val_one])
      rw [this, map_one]
  have := CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num : 1 < 3) _ hEA hcard
  omega

theorem three_lt_pRank_projSU_six_two : 3 < CFSG.pRank 3 (projSU 6 2 1) := by
  have := Fintype.ofFinite (GaloisField 2 (2 * 1))
  have hK : Fintype.card (GaloisField 2 (2 * 1)) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  exact three_lt_pRank_unitary_six hK

end UnitarySix

end CFSG.RankThree.PartTwo.Sec4.Census
