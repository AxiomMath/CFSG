module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.Timmesfeld.ARS.CaseMSp
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

@[expose] public section

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal

open CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem Matrix

open CFSG.SeitzReduction.F4Pilot

open CFSG.Timmesfeld.ARS.CaseM

namespace CFSG.StandardType.F4ExplicitPos.Sp6PairDescent

theorem vecMul_spGram_eq_mulVec {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) :
    v ᵥ* spGram n F = Matrix.mulVec (spGram n F) v := by
  have hJ : (spGram n F)ᵀ = spGram n F := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [spGram, Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]
  rw [← hJ, Matrix.vecMul_transpose, hJ]

theorem spTrans_eq {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) (c : F) :
    spTrans v c = 1 + c • Matrix.vecMulVec v (Matrix.mulVec (spGram n F) v) := by
  rw [spTrans, spNil, vecMul_spGram_eq_mulVec]

theorem spTrans_zero {n : ℕ} {F : Type} [Field F] [CharP F 2] (v : Fin n ⊕ Fin n → F) :
    spTrans v 0 = 1 := by
  rw [spTrans, zero_smul, add_zero]

theorem spTrans_mul {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) (c d : F) :
    spTrans v c * spTrans v d = spTrans v (c + d) := by
  have hsq : spNil v * spNil v = 0 := by rw [spNil_mul_spNil, spForm_self, zero_smul]
  rw [spTrans, spTrans, spTrans, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hsq, smul_zero, add_zero,
    Matrix.one_mul]
  rw [add_smul]
  abel

theorem spTrans_mul_self {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) (c : F) :
    spTrans v c * spTrans v c = 1 := by
  rw [spTrans_mul, CharTwo.add_self_eq_zero, spTrans_zero]

def transvSub {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) : Subgroup (GL (Fin n ⊕ Fin n) F) where
  carrier := {g | ∃ c : F, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = spTrans v c}
  mul_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [Units.val_mul, hc, hd, spTrans_mul]⟩
  one_mem' := ⟨0, (spTrans_zero v).symm⟩
  inv_mem' := by
    rintro x ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hxx : x * x = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one, hc, spTrans_mul_self]
    rw [inv_eq_of_mul_eq_one_right hxx, hc]

theorem matTransvGroup_eq_transvSub {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) :
    matTransvGroup v (Matrix.mulVec (spGram n F) v) = transvSub v := by
  rw [matTransvGroup]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g ⟨c, hc⟩
    exact ⟨c, hc.trans (spTrans_eq v c).symm⟩
  · intro g hg
    obtain ⟨c, hc⟩ := hg
    exact Subgroup.subset_closure ⟨c, hc.trans (spTrans_eq v c)⟩

theorem isTransGroup_of_map_subtype_eq_matTransvGroup {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {v : Fin n ⊕ Fin n → F} {X : Subgroup (StatedSp n F)}
    (h : X.map (StatedSp n F).subtype =
      matTransvGroup v (Matrix.mulVec (spGram n F) v)) :
    IsTransGroup v X := by
  have hT := matTransvGroup_eq_transvSub v
  constructor
  · intro x
    have hx : (StatedSp n F).subtype x ∈ X.map (StatedSp n F).subtype ↔ x ∈ X := by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [Subgroup.subtype_injective (StatedSp n F) hyx] at hy
      · intro hx; exact ⟨x, hx, rfl⟩
    rw [← hx, h, hT]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc⟩
  · intro c
    let g : GL (Fin n ⊕ Fin n) F :=
      ⟨spTrans v c, spTrans v c, spTrans_mul_self v c, spTrans_mul_self v c⟩
    have hg : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = spTrans v c := rfl
    have hc : g ∈ matTransvGroup v (Matrix.mulVec (spGram n F) v) := by
      rw [hT]
      exact ⟨c, hg⟩
    rw [← h] at hc
    obtain ⟨x, -, hxg⟩ := hc
    exact ⟨x, (congrArg (fun u : GL (Fin n ⊕ Fin n) F =>
      (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) hxg).trans hg⟩

theorem spNil_eq_vecMulVec {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) :
    spNil v = Matrix.vecMulVec v (Matrix.mulVec (spGram n F) v) := by
  rw [spNil, vecMul_spGram_eq_mulVec]

theorem map_spNil {n : ℕ} {k Ω : Type} [Field k] [Field Ω] (φ : k →+* Ω)
    (v : Fin n ⊕ Fin n → k) :
    (spNil v).map φ = spNil (fun i => φ (v i)) := by
  ext i j
  simp only [Matrix.map_apply, spNil, Matrix.vecMulVec_apply, RingHom.map_mul,
    RingHom.map_vecMul, map_symplecticGram]
  rfl

theorem spNil_smul {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (c : F) (v : Fin n ⊕ Fin n → F) :
    spNil (c • v) = (c * c) • spNil v := by
  rw [spNil_eq_vecMulVec, spNil_eq_vecMulVec, Matrix.mulVec_smul]
  rw [Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_smul]

theorem spGram_mul_self_eq_one {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    spGram n F * spGram n F = 1 := by
  rw [spGram_mul_self]
  ext i j
  simp only [Matrix.neg_apply, Matrix.one_apply]
  split_ifs with h
  · rw [CharTwo.neg_eq]
  · simp

theorem spGram_mulVec_ne_zero {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {v : Fin n ⊕ Fin n → F} (hv : v ≠ 0) :
    Matrix.mulVec (spGram n F) v ≠ 0 := by
  intro h0
  apply hv
  calc v = 1 *ᵥ v := (Matrix.one_mulVec v).symm
    _ = (spGram n F * spGram n F) *ᵥ v := by rw [spGram_mul_self_eq_one]
    _ = spGram n F *ᵥ (spGram n F *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h0, Matrix.mulVec_zero]

theorem spNil_ne_zero {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {v : Fin n ⊕ Fin n → F} (hv : v ≠ 0) : spNil v ≠ 0 := by
  intro h
  obtain ⟨b, hb⟩ := Function.ne_iff.mp (spGram_mulVec_ne_zero hv)
  apply hv
  funext a
  have hab : Matrix.vecMulVec v (Matrix.mulVec (spGram n F) v) a b = 0 := by
    rw [← spNil_eq_vecMulVec, h]
    rfl
  rw [Matrix.vecMulVec_apply] at hab
  exact (mul_eq_zero.mp hab).resolve_right hb

theorem long_support_descent {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [CharP k 2] [CharP Ω 2]
    {v : Fin 3 ⊕ Fin 3 → Ω} (hv : v ≠ 0)
    {N₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k}
    {t : Ω} (ht : t ≠ 0)
    (hN : N₀.map (algebraMap k Ω) = t • spNil v) :
    ∃ (v₀ : Fin 3 ⊕ Fin 3 → k) (_ : v₀ ≠ 0) (c : k) (_ : c ≠ 0),
      N₀ = c • spNil v₀ := by
  classical
  have hJv : Matrix.mulVec (spGram 3 Ω) v ≠ 0 := spGram_mulVec_ne_zero hv
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hJv
  let v₀ : Fin 3 ⊕ Fin 3 → k := fun a => N₀ a b
  have hv₀map : (fun i => algebraMap k Ω (v₀ i)) =
      (t * (Matrix.mulVec (spGram 3 Ω) v) b) • v := by
    ext a
    have h1 : (N₀.map (algebraMap k Ω)) a b = algebraMap k Ω (N₀ a b) := rfl
    change algebraMap k Ω (N₀ a b) =
      (t * (Matrix.mulVec (spGram 3 Ω) v) b) * v a
    rw [← h1, hN]
    simp only [Matrix.smul_apply, spNil_eq_vecMulVec, Matrix.vecMulVec_apply]
    ring
  let μ : Ω := t * (Matrix.mulVec (spGram 3 Ω) v) b
  have hμ : μ ≠ 0 := mul_ne_zero ht hb
  have hv₀ : v₀ ≠ 0 := by
    intro h0
    have hμv : μ • v = 0 := by
      rw [← hv₀map, h0]
      funext i
      simp
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
    have := congrFun hμv a
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
    exact hμ ((mul_eq_zero.mp this).resolve_right ha)
  have hμ2 : μ * μ ≠ 0 := mul_ne_zero hμ hμ
  have hmap : (spNil v₀).map (algebraMap k Ω) = spNil (fun i => algebraMap k Ω (v₀ i)) :=
    map_spNil (algebraMap k Ω) v₀
  have hsp : spNil (fun i => algebraMap k Ω (v₀ i)) = (μ * μ) • spNil v := by
    conv_lhs => rw [hv₀map]
    rw [spNil_smul]
  have hNmap : N₀.map (algebraMap k Ω) =
      (t * (μ * μ)⁻¹) • (spNil v₀).map (algebraMap k Ω) := by
    rw [hN, hmap, hsp, smul_smul, mul_assoc, inv_mul_cancel₀ hμ2, mul_one]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (spNil_ne_zero hv₀)
  obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
  have hentry : algebraMap k Ω (N₀ i j) = (t * (μ * μ)⁻¹) * algebraMap k Ω (spNil v₀ i j) := by
    have := congrFun (congrFun hNmap i) j
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using this
  have hb0 : algebraMap k Ω (spNil v₀ i j) ≠ 0 :=
    fun h => hij ((algebraMap k Ω).injective (by simpa using h))
  let c0 : k := N₀ i j / spNil v₀ i j
  have hlam : algebraMap k Ω c0 = t * (μ * μ)⁻¹ := by
    change algebraMap k Ω (N₀ i j / spNil v₀ i j) = t * (μ * μ)⁻¹
    rw [map_div₀, hentry, mul_div_cancel_right₀ _ hb0]
  refine ⟨v₀, hv₀, c0, ?_, ?_⟩
  · intro h0
    have hzero : t * (μ * μ)⁻¹ = 0 := by rw [← hlam, h0, map_zero]
    exact (mul_ne_zero ht (inv_ne_zero hμ2)) hzero
  · have hmapinj : Function.Injective
        (fun M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k => M.map (algebraMap k Ω)) :=
      Matrix.map_injective (algebraMap k Ω).injective
    apply hmapinj
    ext p q
    change (algebraMap k Ω) (N₀ p q) = (algebraMap k Ω) (c0 • spNil v₀ p q)
    rw [smul_eq_mul, map_mul, hlam]
    have h := congrFun (congrFun hNmap p) q
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using h

end CFSG.StandardType.F4ExplicitPos.Sp6PairDescent

end

end
