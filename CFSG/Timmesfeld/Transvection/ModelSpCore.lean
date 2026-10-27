module

public import CFSG.Timmesfeld.Transvection.ModelRadical
public import CFSG.Timmesfeld.Transvection.ModelPoints

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM

namespace ModelRank

variable {n : ℕ} {F : Type} [Field F]

theorem mat_pow_mulVec_of_mulVec_eq_smul {g : StatedSp n F} {a : Fin n ⊕ Fin n → F} {μ : F}
    (h : SpExtras.mat n F g *ᵥ a = μ • a) (m : ℕ) :
    SpExtras.mat n F (g ^ m) *ᵥ a = μ ^ m • a := by
  induction m with
  | zero => rw [pow_zero, pow_zero, map_one, one_mulVec, one_smul]
  | succ m ih =>
    rw [pow_succ, map_mul, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

theorem mat_mulVec_eq_of_isPGroup [CharP F 2] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {R : Subgroup (StatedSp n F)} (hRle : R ≤ spLine a) (hR : IsPGroup 2 R)
    {x : StatedSp n F} (hx : x ∈ R) : SpExtras.mat n F x *ᵥ a = a := by
  obtain ⟨μ, -, hμ⟩ := hRle hx
  obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have h1 : μ ^ 2 ^ k • a = a := by
    rw [← mat_pow_mulVec_of_mulVec_eq_smul hμ, hk', map_one, one_mulVec]
  have h2 : μ ^ 2 ^ k = 1 := by
    by_contra hne
    apply ha
    have h3 : (μ ^ 2 ^ k - 1) • a = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)
  have hμ1 : μ = 1 := iterateFrobenius_inj F 2 k (by rw [map_one, iterateFrobenius_def, h2])
  rw [hμ, hμ1, one_smul]

theorem inv_eq_of_mat_eq_spTrans [CharP F 2] {k : StatedSp n F} {w : Fin n ⊕ Fin n → F}
    (hk : SpExtras.mat n F k = spTrans w 1) : k⁻¹ = k := by
  have hkk : k * k = 1 := by
    apply SpExtras.mat_injective
    rw [map_mul, hk, spTrans_mul_spTrans, CharTwo.add_self_eq_zero, spTrans_zero, map_one]
  exact (mul_eq_one_iff_eq_inv.1 hkk).symm

theorem exists_mem_mat_eq_spTrans_mul [CharP F 2] {R : Subgroup (StatedSp n F)}
    {z : StatedSp n F} (hz : z ∈ R) {k : StatedSp n F} {w : Fin n ⊕ Fin n → F}
    (hk : SpExtras.mat n F k = spTrans w 1)
    (hkR : k ∈ Subgroup.normalizer (R : Set (StatedSp n F))) :
    ∃ y ∈ R, SpExtras.mat n F y = spTrans w 1 * spTrans (SpExtras.mat n F z *ᵥ w) 1 := by
  have hkinv := inv_eq_of_mat_eq_spTrans hk
  refine ⟨k * z * k⁻¹ * z⁻¹, mul_mem ((Subgroup.mem_normalizer_iff.1 hkR z).1 hz) (inv_mem hz),
    ?_⟩
  rw [show k * z * k⁻¹ * z⁻¹ = k * (z * k * z⁻¹) by rw [hkinv]; group, map_mul, hk,
    mat_conj_of_mat_eq hk z]

theorem mem_spLine_of_mat_eq_spTrans {a w : Fin n ⊕ Fin n → F} (hw : spForm a w = 0)
    {k : StatedSp n F} {c : F} (hk : SpExtras.mat n F k = spTrans w c) : k ∈ spLine a :=
  ⟨1, one_ne_zero, by rw [hk, spTrans_mulVec, spForm_eq_zero_comm hw, mul_zero, zero_smul,
    add_zero, one_smul]⟩

theorem spForm_mat_mulVec_self_eq_zero [CharP F 2] (hB1 : NoTwoPowerStmt n F)
    {a : Fin n ⊕ Fin n → F} {R : Subgroup (StatedSp n F)}
    (hRnorm : spLine a ≤ Subgroup.normalizer (R : Set (StatedSp n F))) (hR : IsPGroup 2 R)
    {z : StatedSp n F} (hz : z ∈ R) {w : Fin n ⊕ Fin n → F} (hw : spForm a w = 0) :
    spForm w (SpExtras.mat n F z *ᵥ w) = 0 := by
  by_contra hne
  obtain ⟨k, hk⟩ := exists_mat_eq_spTrans w (1 : F)
  obtain ⟨y, hyR, hy⟩ :=
    exists_mem_mat_eq_spTrans_mul hz hk (hRnorm (mem_spLine_of_mat_eq_spTrans hw hk))
  obtain ⟨m, hm⟩ := hR ⟨y, hyR⟩
  apply hB1 hne one_ne_zero one_ne_zero hy m
  have := congrArg Subtype.val hm
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at this

theorem le_spRad_of_isPGroup [CharP F 2] (hB1 : NoTwoPowerStmt n F) {a : Fin n ⊕ Fin n → F}
    (ha : a ≠ 0) {R : Subgroup (StatedSp n F)} (hRle : R ≤ spLine a)
    (hRnorm : spLine a ≤ Subgroup.normalizer (R : Set (StatedSp n F))) (hR : IsPGroup 2 R) :
    R ≤ spRad a := by
  intro x hx
  refine ⟨mat_mulVec_eq_of_isPGroup ha hRle hR hx, fun u hu => ?_⟩
  set xu := SpExtras.mat n F x *ᵥ u with hxu
  have hA : spForm u xu = 0 := spForm_mat_mulVec_self_eq_zero hB1 hRnorm hR hx hu
  obtain ⟨k, hk⟩ := exists_mat_eq_spTrans u (1 : F)
  obtain ⟨y, hyR, hy⟩ :=
    exists_mem_mat_eq_spTrans_mul hx hk (hRnorm (mem_spLine_of_mat_eq_spTrans hu hk))
  have hyw : ∀ w, SpExtras.mat n F y *ᵥ w = w + spForm xu w • xu + spForm u w • u := by
    intro w
    rw [hy, ← mulVec_mulVec, spTrans_mulVec, spTrans_mulVec, spForm_add_right,
      spForm_smul_right', hA, mul_zero, add_zero, one_mul, one_mul]
  have hB : ∀ w, spForm a w = 0 → spForm (u + xu) w = 0 := by
    intro w hw
    have h0 := spForm_mat_mulVec_self_eq_zero hB1 hRnorm hR hyR hw
    rw [hyw, spForm_add_right, spForm_add_right, spForm_smul_right', spForm_smul_right',
      spForm_self, zero_add, spForm_comm xu w, spForm_comm u w, CharTwo.neg_eq,
      CharTwo.neg_eq] at h0
    rw [spForm_add_left]
    have h1 : (spForm u w + spForm xu w) ^ 2 = 0 := by
      rw [CharTwo.add_sq, ← h0]
      ring
    exact pow_eq_zero_iff two_ne_zero |>.1 h1
  obtain ⟨l, hl⟩ := exists_eq_smul_of_spForm_imp hB
  refine ⟨l, ?_⟩
  rw [← hl, ← add_assoc, vec_add_self, zero_add]

theorem pCoreOf_le_spRad {n : ℕ} {F : Type} [Field F] [CharP F 2] [Finite F]
    (hB1 : NoTwoPowerStmt n F) {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) :
    CFSG.Open.pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n F))) ≤ spRad a := by
  rw [normalizer_eq_spLine ha hT]
  exact le_spRad_of_isPGroup hB1 ha (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem spCoreStmt_of_noTwoPower [CharP F 2] [Finite F] (hB1 : NoTwoPowerStmt n F) :
    SpCoreStmt n F :=
  fun ha _ hT => le_antisymm (pCoreOf_le_spRad hB1 ha hT) (spRad_le_pCoreOf ha hT)

end ModelRank

end CFSG.Timmesfeld.Transvection
