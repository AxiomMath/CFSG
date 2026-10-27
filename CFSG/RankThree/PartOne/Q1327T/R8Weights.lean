module

public import CFSG.RankThree.PartOne.N143X.Weights

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

open Matrix Module CFSG.RankThree.PartOne.N143X

section Basic

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (L : Type) [Field L] [Algebra K L] (E : Subgroup (GL ι K))

theorem weight_mul {χ : E → L} (h : joint L E χ ≠ ⊥) (e e' : E) : χ (e * e') = χ e * χ e' := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  have h1 := (mem_joint L E).1 hv
  have h2 : χ (e * e') • v = (χ e' * χ e) • v := by
    rw [← h1 (e * e')]
    have : mapL L ((e * e' : E) : GL ι K) = mapL L (e : GL ι K) * mapL L (e' : GL ι K) := by
      rw [Subgroup.coe_mul, mapL_mul]
    rw [this, ← Matrix.mulVec_mulVec, h1 e', Matrix.mulVec_smul, h1 e, smul_smul]
  have h3 := smul_left_injective L hv0 h2
  rw [h3, mul_comm]

theorem weight_one {χ : E → L} (h : joint L E χ ≠ ⊥) : χ 1 = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  have h1 := (mem_joint L E).1 hv 1
  have h2 : χ 1 • v = (1 : L) • v := by
    rw [← h1, one_smul]
    have : mapL L (((1 : E) : GL ι K)) = 1 := by rw [Subgroup.coe_one, mapL_one]
    rw [this, Matrix.one_mulVec]
  exact smul_left_injective L hv0 h2

theorem weight_ne_zero {χ : E → L} (h : joint L E χ ≠ ⊥) (e : E) : χ e ≠ 0 := by
  intro h0
  have h1 : χ (e * e⁻¹) = χ e * χ e⁻¹ := weight_mul L E h e e⁻¹
  rw [mul_inv_cancel, weight_one L E h, h0, zero_mul] at h1
  exact one_ne_zero h1

@[expose] def wtUnits {χ : E → L} (h : joint L E χ ≠ ⊥) : E →* Lˣ where
  toFun e := Units.mk0 (χ e) (weight_ne_zero L E h e)
  map_one' := Units.ext (weight_one L E h)
  map_mul' e e' := Units.ext (weight_mul L E h e e')

theorem wtUnits_apply {χ : E → L} (h : joint L E χ ≠ ⊥) (e : E) :
    ((wtUnits L E h e : Lˣ) : L) = χ e := rfl

variable {L E}

@[expose] def wtRoots {p : ℕ} (hexp : ∀ e : E, (e : GL ι K) ^ p = 1) (w : Wts L E) :
    E →* rootsOfUnity p L :=
  (wtUnits L E w.2).codRestrict (rootsOfUnity p L) fun e => by
    rw [mem_rootsOfUnity]
    exact Units.ext (by
      rw [Units.val_pow_eq_pow_val, wtUnits_apply]
      exact weight_pow_eq_one L E hexp w.2 e)

theorem wtRoots_apply {p : ℕ} (hexp : ∀ e : E, (e : GL ι K) ^ p = 1) (w : Wts L E) (e : E) :
    (((wtRoots hexp w e : rootsOfUnity p L) : Lˣ) : L) = w.1 e := rfl

theorem wtRoots_eq_one_iff {p : ℕ} (hexp : ∀ e : E, (e : GL ι K) ^ p = 1) (w : Wts L E) :
    wtRoots hexp w = 1 ↔ ∀ e : E, w.1 e = 1 := by
  constructor
  · intro h e
    have := DFunLike.congr_fun h e
    have h1 := congrArg (fun z : rootsOfUnity p L => ((z : Lˣ) : L)) this
    simpa [wtRoots_apply] using h1
  · intro h
    ext e
    simp [wtRoots_apply, h e]

end Basic

section Frob

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {L : Type} [Field L] [Algebra K L] {E : Subgroup (GL ι K)}

theorem joint_comp_ne_bot (σ : L →+* L) (hσ : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    {χ : E → L} (h : joint L E χ ≠ ⊥) : joint L E (fun e => σ (χ e)) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨fun i => σ (v i), ?_, ?_⟩
  · rw [mem_joint]
    intro e
    funext i
    have h1 := congrFun ((mem_joint L E).1 hv e) i
    simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
    have h2 : ((mapL L (e : GL ι K)) *ᵥ fun i => σ (v i)) i =
        σ ((mapL L (e : GL ι K) *ᵥ v) i) := by
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mapL, Matrix.map_apply, hσ]
    rw [h2, h1, map_mul]
  · intro h0
    apply hv0
    funext i
    have := congrFun h0 i
    simp only [Pi.zero_apply] at this
    simpa using (map_eq_zero σ).1 this

@[expose] def frobWt (σ : L →+* L) (hσ : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (w : Wts L E) : Wts L E :=
  ⟨fun e => σ (w.1 e), joint_comp_ne_bot σ hσ w.2⟩

theorem frobWt_apply (σ : L →+* L) (hσ : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (w : Wts L E) (e : E) : (frobWt σ hσ w).1 e = σ (w.1 e) := rfl

end Frob

end CFSG.RankThree.PartOne.Q1327T.R8
