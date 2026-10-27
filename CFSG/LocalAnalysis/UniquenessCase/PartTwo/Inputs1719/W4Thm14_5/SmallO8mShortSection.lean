module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinMinus
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringsAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mShortSection

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem CFSG.Quasithin.SmithCurtis Module
open CFSG.QuasithinUnique.Setup.SL2Modules (uElt dElt)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

section Realization

variable [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)]

omit [CharP K 2] in
private theorem exists_shortSL2 (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ Λ : SL(2, ShortField b c) →* spinGroup (quadMinus 4 K b c),
      (∀ x, Λ (uElt x) = shortX 4 hirrQ 2 x) ∧
      (∀ x, Λ (lowerSL2 x) = shortY 4 hirrQ 2 x) ∧
      (∀ t, Λ (dElt t) = shortTorusHom 4 hirrQ 2 t) ∧
      Λ.range = (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range := by
  have := finite_shortField (b := b) (c := c)
  let R := shortRels 4 hirrQ 2
  obtain ⟨Λ, hU, hL⟩ := CFSG.AGLEmbeddingD2.HeisSpinMinus.exists_hom_of_rankOneRels' R
  have hupper : ∀ x, Λ (upperSL2 x) = R.x x := hU
  have hlower : ∀ x, Λ (lowerSL2 x) = R.y x := hL
  have hw : ∀ t : (ShortField b c)ˣ, Λ (weylSL2 t) = R.w (t : ShortField b c) := by
    intro t
    rw [weylSL2_eq, map_mul, map_mul]
    simp only [hupper, hlower]
    rw [RankOneRels.w_def, Units.val_inv_eq_inv_val]
  refine ⟨Λ, hU, hL, ?_, ?_⟩
  · intro t
    rw [show dElt t = diagSL2 t from rfl, diagSL2_eq, ← weylSL2_one_inv, map_mul,
      map_inv, hw, hw]
    change R.h (t : ShortField b c) = shortTorusHom 4 hirrQ 2 t
    exact shortRels_h 4 hirrQ 2 t
  · rw [← shortRels_sub 4 hirrQ 2]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨g, rfl⟩
      refine (Subgroup.closure_le _).mpr ?_ (mem_closure_upperSL2_lowerSL2 Λ g)
      rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · change Λ (upperSL2 x) ∈ R.sub
        rw [hupper]
        exact R.x_mem_sub x
      · change Λ (lowerSL2 x) ∈ R.sub
        rw [hlower]
        exact R.y_mem_sub x
    · rw [RankOneRels.sub, Subgroup.closure_le]
      rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact ⟨sl2Upper x, hU x⟩
      · exact ⟨sl2Lower x, hL x⟩

end Realization

theorem exists_shortString_weights (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    [Finite (spinGroup (quadMinus 4 K b c))] {e : ℕ} (hKe : Nat.card K = 2 ^ e)
    (_he : 2 ≤ e) {k V : Type} [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (φ : ShortField b c →+* k)
    (hsplit : SplitOver k (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H)
    {σ : Representation k (spinGroup (quadMinus 4 K b c)) V} (hσ : IsSimpleRep σ)
    {y₀ : V} {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType σ y₀ χ μ) :
    ∃ J : Finset ℕ, J ⊆ Finset.range (2 * e) ∧
      (∀ t : (ShortField b c)ˣ,
        χ (shortTorusHom 4 hirrQ 2 t) = φ (t : ShortField b c) ^ (∑ j ∈ J, 2 ^ j)) ∧
      finrank k (fixSub σ ((SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Us 2)) =
        2 ^ J.card ∧
      (J = ∅ → ∀ g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range,
        σ g y₀ = y₀) ∧
      ∀ j ∈ J, ∃ v ∈ fixSub σ ((SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Us 2),
        v ≠ 0 ∧ ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
          ∀ t : (ShortField b c)ˣ,
            h * (shortTorusHom 4 hirrQ 2 t)⁻¹ ∈ Subgroup.centralizer
                ((((shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range) :
                  Subgroup (spinGroup (quadMinus 4 K b c))) : Set _) →
            σ h v = (χ h * (φ (t : ShortField b c) ^ (-(2 ^ (j + 1) : ℤ)))) • v := by
  classical
  have := fact_shortField hirrQ
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap K (ShortField b c)).injective 2
  let : Algebra (ShortField b c) k := φ.toAlgebra
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (coxeterMatrix (isFiniteType_cartanB 3)).Group :=
    finite_group (isFiniteType_cartanB 3)
  have hE : Nat.card (ShortField b c) = 2 ^ (2 * e) := by
    rw [CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.card_shortField, hKe, ← pow_mul,
      mul_comm]
  obtain ⟨Λ, hΛU, hΛL, hΛT, hΛrange⟩ := exists_shortSL2 hirrQ
  set D := SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ
  let S := (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range
  set Fix := fixSub σ (D.Us 2)
  have hΛS : Λ.range = S := hΛrange
  let σ' : Representation k SL(2, ShortField b c) V := σ.comp Λ
  obtain ⟨hyU, hy0, hχ, hμ⟩ := ht
  have hrank : D.X 2 ⊔ D.Y 2 = S :=
    rankOne_minusRootGroup_of_not_lt 4 hirrQ (by norm_num)
  have hXi : ∀ g, g ∈ D.X 2 ↔ ∃ x : ShortField b c, g = shortX 4 hirrQ 2 x := by
    intro g
    change g ∈ minusRootGroup 4 hirrQ (Pi.single 2 1) ↔ _
    rw [minusRootGroup_single_of_not_lt 4 hirrQ (by norm_num), MonoidHom.mem_range]
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, hx⟩ := exists_fieldCoord_eq (b := b) (c := c) p.toAdd
      exact ⟨x, by rw [shortX, hx, ofAdd_toAdd]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨.ofAdd (fieldCoord x), rfl⟩
  have hSΛ : ∀ g, Λ g ∈ D.X 2 ⊔ D.Y 2 := fun g => by
    rw [hrank, ← hΛS]
    exact ⟨g, rfl⟩
  have hFixst : ∀ g : SL(2, ShortField b c), ∀ w ∈ Fix, σ' g w ∈ Fix := by
    intro g w hw
    refine act_mem_fixSub σ (fun u hu => ?_) hw
    have h := conj_mem_of_sup (D.X_normUs 2)
      (fun y hy v hv => curtisDatum_Y_normUs D 2 hy hv) (inv_mem (hSΛ g)) hu
    simpa only [inv_inv] using h
  have hfix : ∀ f ∈ Fix, (∀ x : ShortField b c, σ' (uElt x) f = f) →
      ∃ a : k, f = a • y₀ := by
    intro f hf hfu
    refine D.fixU_eq_smul hσ ⟨hyU, hy0, hχ, hμ⟩ ?_
    intro u hu
    obtain ⟨x, hx, v, hv, rfl⟩ := D.U_eq 2 u hu
    rw [map_mul, Module.End.mul_apply, hf v hv]
    obtain ⟨a, rfl⟩ := (hXi x).mp hx
    have h := hfu a
    change σ (Λ (uElt a)) f = f at h
    rwa [hΛU] at h
  have hyFix : y₀ ∈ Fix := fun u hu => hyU u (D.Us_le 2 hu)
  have hvu : ∀ x : ShortField b c, σ' (uElt x) y₀ = y₀ := by
    intro x
    change σ (Λ (uElt x)) y₀ = y₀
    rw [hΛU]
    exact hyU _ (D.X_le 2 ((hXi _).mpr ⟨x, rfl⟩))
  have htorH : ∀ t : (ShortField b c)ˣ, shortTorusHom 4 hirrQ 2 t ∈ D.H := by
    intro t
    change shortTorusHom 4 hirrQ 2 t ∈ ⨆ i : Fin 3, minusTorus 4 hirrQ i
    refine Subgroup.mem_iSup_of_mem (2 : Fin 3) ?_
    rw [minusTorus_of_not_lt 4 hirrQ (k := (2 : Fin 3)) (by norm_num),
      ← range_shortTorusHom]
    exact ⟨t, rfl⟩
  obtain ⟨J, hJlt, hεJ, hdimJ, hJ0, hlow⟩ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.string_data hE σ' hy0 Fix hyFix
      hFixst hfix hvu (fun t => χ (shortTorusHom 4 hirrQ 2 t))
      (fun t => by change σ (Λ (dElt t)) y₀ = _; rw [hΛT]; exact hχ _ (htorH t))
  have horbFix : orbitSpan σ' y₀ ≤ Fix :=
    Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hFixst g y₀ hyFix)
  have horb : orbitSpan σ' y₀ = Fix := by
    rcases fixSub_Us_eq_bot_or_eq D hsplit hσ 2 horbFix (fun m hm w hw => by
        rw [hrank, ← hΛS] at hm
        obtain ⟨g, rfl⟩ := hm
        exact orbitSpan_stable σ' y₀ g hw) with h0 | h1
    · exfalso
      have hmem := mem_orbitSpan_self σ' y₀
      rw [h0, Submodule.mem_bot] at hmem
      exact hy0 hmem
    · exact h1
  refine ⟨J, fun j hj => Finset.mem_range.mpr (hJlt j hj), hεJ,
    by rw [← horb]; exact hdimJ, ?_, ?_⟩
  · intro hJ g hg
    rw [← hΛrange] at hg
    obtain ⟨g, rfl⟩ := hg
    exact hJ0 hJ g
  · intro j hj
    obtain ⟨v, hvorb, hv0, hvw⟩ := hlow j hj
    refine ⟨v, horb ▸ hvorb, hv0, ?_⟩
    intro h hh t hcentral
    let c₀ := h * (shortTorusHom 4 hirrQ 2 t)⁻¹
    have hcH : c₀ ∈ D.H := D.H.mul_mem hh (D.H.inv_mem (htorH t))
    have hcact : ∀ w ∈ orbitSpan σ' y₀, σ c₀ w = χ c₀ • w := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨g, rfl⟩ := hw
        have hcomm : c₀ * Λ g = Λ g * c₀ := by
          have hg : Λ g ∈ S := hΛS ▸ (show Λ g ∈ Λ.range from ⟨g, rfl⟩)
          exact (Subgroup.mem_centralizer_iff.mp hcentral _ hg).symm
        change σ c₀ (σ (Λ g) y₀) = _
        rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply,
          hχ _ hcH, map_smul]
        rfl
      | zero => rw [map_zero, smul_zero]
      | add a a' _ _ ha ha' => rw [map_add, ha, ha', smul_add]
      | smul r a _ ha => rw [map_smul, ha, smul_comm]
    have hcc : χ c₀ = χ h * χ (shortTorusHom 4 hirrQ 2 t⁻¹) := by
      apply smul_left_injective k hy0
      change χ c₀ • y₀ = (χ h * χ (shortTorusHom 4 hirrQ 2 t⁻¹)) • y₀
      rw [← hχ c₀ hcH]
      change σ (h * (shortTorusHom 4 hirrQ 2 t)⁻¹) y₀ = _
      rw [← map_inv, map_mul, Module.End.mul_apply, hχ _ (htorH t⁻¹), map_smul, hχ h hh,
        smul_smul, mul_comm]
    have hvT : σ (shortTorusHom 4 hirrQ 2 t) v =
        φ (t : ShortField b c) ^ (((∑ i ∈ J, 2 ^ i : ℕ) : ℤ) - 2 ^ (j + 1)) • v := by
      have hv := hvw t
      change σ (Λ (dElt t)) v = φ (t : ShortField b c) ^ _ • v at hv
      rwa [hΛT] at hv
    calc
      σ h v = σ c₀ (σ (shortTorusHom 4 hirrQ 2 t) v) := by
        rw [← Module.End.mul_apply, ← map_mul]
        congr 1
        dsimp [c₀]
        group
      _ = (χ h * (φ (t : ShortField b c) ^ (-(2 ^ (j + 1) : ℤ)))) • v := by
        rw [hvT, map_smul, hcact v hvorb, smul_smul, hcc, hεJ t⁻¹]
        congr 1
        have hA : φ (t : ShortField b c) ≠ 0 := by simp
        change φ (t : ShortField b c) ^ (((∑ i ∈ J, 2 ^ i : ℕ) : ℤ) - 2 ^ (j + 1)) *
          (χ h * φ (t⁻¹ : (ShortField b c)ˣ) ^ (∑ i ∈ J, 2 ^ i)) = _
        rw [Units.val_inv_eq_inv_val, map_inv₀, inv_pow]
        rw [mul_comm _ (χ h * _), mul_assoc]
        congr 1
        rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hA]
        congr 1
        omega

omit [CharP K 2] in
theorem mul_shortTorus_inv_mem_centralizer_of_conj
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h : spinGroup (quadMinus 4 K b c)) (t : (ShortField b c)ˣ)
    (hX : ∀ x : ShortField b c,
      h * shortX 4 hirrQ 2 x * h⁻¹ = shortX 4 hirrQ 2 ((t : ShortField b c) ^ 2 * x))
    (hY : ∀ x : ShortField b c,
      h * shortY 4 hirrQ 2 x * h⁻¹ = shortY 4 hirrQ 2 (((t : ShortField b c) ^ 2)⁻¹ * x)) :
    h * (shortTorusHom 4 hirrQ 2 t)⁻¹ ∈ Subgroup.centralizer
      ((((shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range) :
        Subgroup (spinGroup (quadMinus 4 K b c))) : Set _) := by
  have := fact_shortField hirrQ
  have := finite_shortField (b := b) (c := c)
  let R := shortRels 4 hirrQ 2
  let Ht := shortTorusHom 4 hirrQ 2 t
  have hT : Ht = R.h (t : ShortField b c) := (shortRels_h 4 hirrQ 2 t).symm
  have hconj : ∀ g ∈ R.sub, h * g * h⁻¹ = Ht * g * Ht⁻¹ := by
    let f₁ := (MulAut.conj h).toMonoidHom
    let f₂ := (MulAut.conj Ht).toMonoidHom
    have hle : R.sub ≤ f₁.eqLocus f₂ := by
      rw [RankOneRels.sub, Subgroup.closure_le]
      rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · change h * R.x x * h⁻¹ = Ht * R.x x * Ht⁻¹
        rw [hT, R.h_conj_x t.ne_zero]
        exact hX x
      · change h * R.y x * h⁻¹ = Ht * R.y x * Ht⁻¹
        rw [hT, R.h_conj_y t.ne_zero]
        exact hY x
    exact fun g hg => hle hg
  have hfactor : h * Ht⁻¹ = Ht⁻¹ * h := by
    have htmem : Ht ∈ R.sub := by
      rw [hT, RankOneRels.h_def]
      exact R.sub.mul_mem (R.w_mem_sub _) (R.sub.inv_mem (R.w_mem_sub _))
    have hc : h * Ht * h⁻¹ = Ht := by simpa using hconj Ht htmem
    have hhT : h * Ht = Ht * h := mul_inv_eq_iff_eq_mul.mp hc
    calc
      h * Ht⁻¹ = Ht⁻¹ * (Ht * h) * Ht⁻¹ := by group
      _ = Ht⁻¹ * (h * Ht) * Ht⁻¹ := by rw [← hhT]
      _ = Ht⁻¹ * h := by group
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  have hgR : g ∈ R.sub := by rwa [shortRels_sub]
  have hc : (h * Ht⁻¹) * g * (h * Ht⁻¹)⁻¹ = g := by
    rw [hfactor]
    calc
      (Ht⁻¹ * h) * g * (Ht⁻¹ * h)⁻¹ = Ht⁻¹ * (h * g * h⁻¹) * Ht := by group
      _ = Ht⁻¹ * (Ht * g * Ht⁻¹) * Ht := by rw [hconj g hgR]
      _ = g := by group
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mShortSection
