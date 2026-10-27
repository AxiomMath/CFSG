module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU4Gen
public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU4

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228InspProof

open Matrix CFSG CFSG.RankThree
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor permGL permGL_mem_SU)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (longSL shortSL weyl₁ weyl₂ torusD coe_torusD
  conj_weyl₁ conj_weyl₂ zpowers_torusD_inv line_cases entry_zero_zero_of_mem_longSL
  det_block_of_mem_shortSL perfectResidual_conj)
open CFSG.Assembly.RankThreeEven (projSL)

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

theorem not_mem_map_conj_of_inv {G : Type*} [Group G] {S : Subgroup G} {w x : G}
    (hw : w * w = 1) (hx : w * x * w⁻¹ ∉ S) : x ∉ S.map (MulAut.conj w).toMonoidHom := by
  rintro ⟨y, hy, hyx⟩
  change w * y * w⁻¹ = x at hyx
  apply hx
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have : w * x * w⁻¹ = y := by
    rw [← hyx, hwinv]
    calc w * (w * y * w) * w = (w * w) * y * (w * w) := by group
      _ = y := by rw [hw, one_mul, mul_one]
  rw [this]
  exact hy

omit [Finite F] [CharP F 2] in
theorem torusD_apply_zero (v : D8Mod 3 F) :
    ((torusD v : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 = ((v.1 : Fˣ) : F) := by
  rw [coe_torusD]
  simp

omit [Finite F] [CharP F 2] in
theorem torusD_block_det (v : D8Mod 3 F) :
    ((torusD v : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 *
        ((torusD v : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 1 -
      ((torusD v : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 1 *
        ((torusD v : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 0 =
      ((v.1 : Fˣ) : F) * ((v.2 : Fˣ) : F) := by
  rw [coe_torusD]
  simp

theorem map_conj_self {G : Type} [Group G] {Y : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (Y : Set G)) : Y.map (MulAut.conj w).toMonoidHom = Y := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hw y).mp hy
  · intro hx
    refine ⟨w⁻¹ * x * w, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) x).mp hx
    simpa [mul_assoc] using this

theorem sup_perfCent_conj {G : Type} [Group G] [Finite G] {Y : Subgroup G} {w : G} (hw : w ∈ Y)
    {Z₁ Z₂ : Subgroup G} (h : perfCent Y Z₁ ⊔ perfCent Y Z₂ = Y) :
    perfCent Y (Z₁.map (MulAut.conj w).toMonoidHom) ⊔
      perfCent Y (Z₂.map (MulAut.conj w).toMonoidHom) = Y := by
  rw [perfCent, perfCent, perfectResidual_conj hw, perfectResidual_conj hw, ← Subgroup.map_sup]
  change (perfCent Y Z₁ ⊔ perfCent Y Z₂).map _ = Y
  rw [h, map_conj_self (Subgroup.le_normalizer hw)]

theorem mem_normalizer_of_conj_le {G : Type} [Group G] {T : Subgroup G} {w : G} (hw : w * w = 1)
    (h : ∀ x ∈ T, w * x * w⁻¹ ∈ T) : w ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have := h _ hx
  rwa [hwinv, show w * (w * x * w) * w = (w * w) * x * (w * w) by group, hw, one_mul,
    mul_one] at this

omit [Finite F] [CharP F 2] in
theorem weyl_mul_self :
    (weyl₁ : GL (Fin 4) F) * weyl₁ = 1 ∧ (weyl₂ : GL (Fin 4) F) * weyl₂ = 1 := by
  constructor
  · rw [weyl₁_eq, ← map_mul, show tau₁ * tau₁ = 1 by decide, map_one]
  · rw [weyl₂_eq, ← map_mul, show tau₂ * tau₂ = 1 by decide, map_one]

theorem model_U4 (hb : 0 < b) (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    (∀ ℓ : Subgroup (GL (Fin 4) F), ℓ ≤ d8Tor 3 F 4 → Nat.card ℓ = 3 →
      Nonempty (perfCent (SU (unitaryInvolution F 2 b) 4) ℓ ≃* projSL 2 (GaloisField 2 b)) ∨
        Nonempty (perfCent (SU (unitaryInvolution F 2 b) 4) ℓ ≃*
          projSL 2 (GaloisField 2 (2 * b)))) ∧
    ∀ ℓ₁ ℓ₂ c₁ c₂ : Subgroup (GL (Fin 4) F), ℓ₁ ≤ d8Tor 3 F 4 → ℓ₂ ≤ d8Tor 3 F 4 →
      c₁ ≤ d8Tor 3 F 4 → c₂ ≤ d8Tor 3 F 4 → Nat.card ℓ₁ = 3 → Nat.card ℓ₂ = 3 →
      Nat.card c₁ = 3 → Nat.card c₂ = 3 → ℓ₁ ≠ ℓ₂ →
      c₁ ≤ perfCent (SU (unitaryInvolution F 2 b) 4) ℓ₁ →
      c₂ ≤ perfCent (SU (unitaryInvolution F 2 b) 4) ℓ₂ →
        (c₁ = ℓ₂ → c₂ = ℓ₁ ∧
          (⁅perfCent (SU (unitaryInvolution F 2 b) 4) ℓ₁,
              perfCent (SU (unitaryInvolution F 2 b) 4) ℓ₂⁆ = ⊥ ∨
            (perfCent (SU (unitaryInvolution F 2 b) 4) ℓ₁ ⊔
                perfCent (SU (unitaryInvolution F 2 b) 4) ℓ₂ = SU (unitaryInvolution F 2 b) 4 ∧
              Nonempty (perfCent (SU (unitaryInvolution F 2 b) 4) ℓ₁ ≃*
                projSL 2 (GaloisField 2 (2 * b))) ∧
              Nonempty (perfCent (SU (unitaryInvolution F 2 b) 4) ℓ₂ ≃*
                projSL 2 (GaloisField 2 (2 * b))) ∧
              ∃ w ∈ SU (unitaryInvolution F 2 b) 4,
                w ∈ Subgroup.normalizer (d8Tor 3 F 4 : Set (GL (Fin 4) F)) ∧
                ℓ₁.map (MulAut.conj w).toMonoidHom = ℓ₂ ∧
                ℓ₂.map (MulAut.conj w).toMonoidHom = ℓ₁))) ∧
        (c₁ ≠ ℓ₂ → perfCent (SU (unitaryInvolution F 2 b) 4) ℓ₁ ⊔
          perfCent (SU (unitaryInvolution F 2 b) 4) ℓ₂ = SU (unitaryInvolution F 2 b) 4) := by
  set σ : F ≃+* F := unitaryInvolution F 2 b with hσdef
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have hμ := U4Lines.card_rootsOfUnity_three hbe hF
  have : Nontrivial (rootsOfUnity 3 F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hμ]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : rootsOfUnity 3 F)
  set a : F := ((ω : Fˣ) : F) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 _).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have haa : a * a ≠ 1 := by
    intro h
    apply ha1
    calc a = a ^ 3 * (a * a)⁻¹ := by field_simp
      _ = 1 := by rw [ha3, h, inv_one, one_mul]
  have hainv : a ≠ a⁻¹ := fun h => haa (by
    calc a * a = a * a⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel₀ ha0)
  have hainv1 : a⁻¹ ≠ 1 := fun h => ha1 (by rw [← inv_inv a, h, inv_one])
  have hinv1 : (1 : F) ≠ a⁻¹ := fun h => hainv1 h.symm
  have hval : (((ω : Fˣ)⁻¹ : Fˣ) : F) = a⁻¹ := Units.val_inv_eq_inv_val _
  have hfix := U4Lines.unitaryInvolution_rootsOfUnity (F := F) hbe
  have hw₁ : weyl₁ ∈ SU σ 4 := permGL_mem_SU σ _ (by decide)
  have hw₂ : weyl₂ ∈ SU σ 4 := permGL_mem_SU σ _ (by decide)
  obtain ⟨hww₁, hww₂⟩ := weyl_mul_self (F := F)
  have hperfSU : ∀ ℓ : Subgroup (GL (Fin 4) F), perfCent (SU σ 4) ℓ ≤ SU σ 4 := fun ℓ =>
    (Subgroup.map_subtype_le _).trans inf_le_left
  have ht₁ : ((torusD ((ω, 1) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a, 1, 1, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  have ht₃ : ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  obtain ⟨eL⟩ := U4Lines.nonempty_longSL_mulEquiv (F := F) hb hF
  obtain ⟨eS⟩ := U4Lines.nonempty_shortSL_mulEquiv_galois σ hb hF
  have hperfL : ⁅longSL σ, longSL σ⁆ = longSL σ :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL hb2 eL)
  have hperfS : ⁅shortSL σ, shortSL σ⁆ = shortSL σ :=
    Subgroup.isPerfect_iff.mp (isPerfect_of_mulEquiv_projSL (by omega) eS)
  have hS₁ : perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))) = longSL σ :=
    U4Lines.perfectResidual_long σ ht₁ ha1 hainv hinv1 hperfL
  have hS₃ : perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))) = shortSL σ :=
    U4Lines.perfectResidual_short σ hσσ ht₃ hainv hperfS
  have hL₂ : (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))).map
      (MulAut.conj weyl₁).toMonoidHom = Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact conj_weyl₁ ((ω, 1) : D8Mod 3 F)
  have hL₁ : (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F))).map
      (MulAut.conj weyl₁).toMonoidHom = Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact conj_weyl₁ ((1, ω) : D8Mod 3 F)
  have hL₃₁ : (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
      (MulAut.conj weyl₁).toMonoidHom = Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact conj_weyl₁ ((ω, ω) : D8Mod 3 F)
  have hL₄ : (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
      (MulAut.conj weyl₂).toMonoidHom = Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact conj_weyl₂ ((ω, ω) : D8Mod 3 F)
  have hL₃ : (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))).map
      (MulAut.conj weyl₂).toMonoidHom = Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change weyl₂ * torusD ((ω, ω⁻¹) : D8Mod 3 F) * weyl₂⁻¹ = _
    rw [conj_weyl₂, inv_inv]
  have hL₂₂ : (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F))).map
      (MulAut.conj weyl₂).toMonoidHom = Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)) := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (weyl₂ * torusD ((1, ω) : D8Mod 3 F) * weyl₂⁻¹) = _
    rw [conj_weyl₂, show ((((1, ω) : D8Mod 3 F)).1, ((1, ω) : D8Mod 3 F).2⁻¹) =
      ((1, ω) : D8Mod 3 F)⁻¹ by simp, zpowers_torusD_inv]
  have hL₁₂ : (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))).map
      (MulAut.conj weyl₂).toMonoidHom = Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change weyl₂ * torusD ((ω, 1) : D8Mod 3 F) * weyl₂⁻¹ = _
    rw [conj_weyl₂, inv_one]
  have hS₂ : perfCent (SU σ 4) (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F))) =
      (longSL σ).map (MulAut.conj weyl₁).toMonoidHom := by
    rw [← hL₂, perfCent, perfectResidual_conj hw₁]
    exact congrArg _ hS₁
  have hS₄ : perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) =
      (shortSL σ).map (MulAut.conj weyl₂).toMonoidHom := by
    rw [← hL₄, perfCent, perfectResidual_conj hw₂]
    exact congrArg _ hS₃
  have e₁ : Nonempty (perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))) ≃*
      projSL 2 (GaloisField 2 b)) := by
    rw [hS₁]
    exact ⟨eL⟩
  have e₂ : Nonempty (perfCent (SU σ 4) (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F))) ≃*
      projSL 2 (GaloisField 2 b)) := by
    rw [hS₂]
    exact ⟨((longSL σ).equivMapOfInjective _ (MulAut.conj weyl₁).injective).symm.trans eL⟩
  have e₃ : Nonempty (perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))) ≃*
      projSL 2 (GaloisField 2 (2 * b))) := by
    rw [hS₃]
    exact ⟨eS⟩
  have e₄ : Nonempty (perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) ≃*
      projSL 2 (GaloisField 2 (2 * b))) := by
    rw [hS₄]
    exact ⟨((shortSL σ).equivMapOfInjective _ (MulAut.conj weyl₂).injective).symm.trans eS⟩
  have hdist : ∀ X Y : Subgroup (GL (Fin 4) F),
      Nonempty (perfCent (SU σ 4) X ≃* projSL 2 (GaloisField 2 b)) →
      Nonempty (perfCent (SU σ 4) Y ≃* projSL 2 (GaloisField 2 (2 * b))) → X ≠ Y := by
    rintro X Y ⟨f⟩ ⟨g⟩ rfl
    have := eq_of_mulEquiv_projSL_two (by omega) (by omega) (f.symm.trans g)
    omega
  have hlong : ∀ v : D8Mod 3 F, torusD v ∈ longSL σ → ((v.1 : Fˣ) : F) = 1 := fun v h => by
    rw [← torusD_apply_zero]
    exact entry_zero_zero_of_mem_longSL σ h
  have hshort : ∀ v : D8Mod 3 F, torusD v ∈ shortSL σ →
      ((v.1 : Fˣ) : F) * ((v.2 : Fˣ) : F) = 1 := fun v h => by
    rw [← torusD_block_det]
    exact det_block_of_mem_shortSL σ h
  have n₁₁ : torusD ((ω, 1) : D8Mod 3 F) ∉ longSL σ := fun h => ha1 (hlong _ h)
  have n₁₃ : torusD ((ω, ω) : D8Mod 3 F) ∉ longSL σ := fun h => ha1 (hlong _ h)
  have n₁₄ : torusD ((ω, ω⁻¹) : D8Mod 3 F) ∉ longSL σ := fun h => ha1 (hlong _ h)
  have n₂₂ : torusD ((1, ω) : D8Mod 3 F) ∉ (longSL σ).map (MulAut.conj weyl₁).toMonoidHom :=
    not_mem_map_conj_of_inv hww₁ (by rw [conj_weyl₁]; exact n₁₁)
  have n₂₃ : torusD ((ω, ω) : D8Mod 3 F) ∉ (longSL σ).map (MulAut.conj weyl₁).toMonoidHom :=
    not_mem_map_conj_of_inv hww₁ (by rw [conj_weyl₁]; exact n₁₃)
  have n₂₄ : torusD ((ω, ω⁻¹) : D8Mod 3 F) ∉
      (longSL σ).map (MulAut.conj weyl₁).toMonoidHom :=
    not_mem_map_conj_of_inv hww₁ (by
      rw [conj_weyl₁]
      intro h
      have := hlong _ h
      simp only at this
      rw [Subgroup.coe_inv, hval] at this
      exact hainv1 this)
  have n₃₁ : torusD ((ω, 1) : D8Mod 3 F) ∉ shortSL σ := fun h => hω (by
    simpa using hshort _ h)
  have n₃₂ : torusD ((1, ω) : D8Mod 3 F) ∉ shortSL σ := fun h => hω (by
    simpa using hshort _ h)
  have n₃₃ : torusD ((ω, ω) : D8Mod 3 F) ∉ shortSL σ := fun h => haa (hshort _ h)
  have n₄₁ : torusD ((ω, 1) : D8Mod 3 F) ∉ (shortSL σ).map (MulAut.conj weyl₂).toMonoidHom :=
    not_mem_map_conj_of_inv hww₂ (by rw [conj_weyl₂, inv_one]; exact n₃₁)
  have n₄₂ : torusD ((1, ω) : D8Mod 3 F) ∉ (shortSL σ).map (MulAut.conj weyl₂).toMonoidHom :=
    not_mem_map_conj_of_inv hww₂ (by
      rw [conj_weyl₂]
      intro h
      have := hshort _ h
      simp only [OneMemClass.coe_one, Units.val_one, one_mul] at this
      rw [Subgroup.coe_inv, hval] at this
      exact hainv1 this)
  have n₄₄ : torusD ((ω, ω⁻¹) : D8Mod 3 F) ∉
      (shortSL σ).map (MulAut.conj weyl₂).toMonoidHom :=
    not_mem_map_conj_of_inv hww₂ (by rw [conj_weyl₂, inv_inv]; exact n₃₃)
  have hpartner : ∀ ℓ c : Subgroup (GL (Fin 4) F), ℓ ≤ d8Tor 3 F 4 → Nat.card ℓ = 3 →
      c ≤ d8Tor 3 F 4 → Nat.card c = 3 → c ≤ perfCent (SU σ 4) ℓ →
      (ℓ = Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F)) ∧
          c = Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F))) ∨
        (ℓ = Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)) ∧
          c = Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))) ∨
        (ℓ = Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) ∧
          c = Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) ∨
        (ℓ = Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) ∧
          c = Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))) := by
    intro ℓ c hℓ hℓ3 hc hc3 hcS
    rcases line_cases hμ hω hℓ hℓ3 with rfl | rfl | rfl | rfl <;>
      rcases line_cases hμ hω hc hc3 with rfl | rfl | rfl | rfl <;>
      first
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₁]; exact n₁₁)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₁]; exact n₁₃)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₁]; exact n₁₄)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₂]; exact n₂₂)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₂]; exact n₂₃)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₂]; exact n₂₄)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₃]; exact n₃₁)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₃]; exact n₃₂)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₃]; exact n₃₃)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₄]; exact n₄₁)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₄]; exact n₄₂)
      | exact absurd (hcS (Subgroup.mem_zpowers _)) (by rw [hS₄]; exact n₄₄)
  have g23 : perfCent (SU σ 4) (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F))) ⊔
      perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))) = SU σ 4 := by
    rw [hS₃]
    exact sup_shortSL_eq_SU_of (by omega) hF (hperfSU _) (map_range_suBlock_le hb2 hF (hfix ω))
  have g13 : perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))) ⊔
      perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))) = SU σ 4 := by
    have h := sup_perfCent_conj hw₁ g23
    rwa [hL₁, hL₃₁] at h
  have g24 : perfCent (SU σ 4) (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F))) ⊔
      perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) = SU σ 4 := by
    have h := sup_perfCent_conj hw₂ g23
    rwa [hL₂₂, hL₄] at h
  have g14 : perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))) ⊔
      perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) = SU σ 4 := by
    have h := sup_perfCent_conj hw₂ g13
    rwa [hL₁₂, hL₄] at h
  have g34 : perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))) ⊔
      perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) = SU σ 4 := by
    rw [hS₃, hS₄]
    exact shortSL_sup_weyl₂_eq_SU (by omega) hF
  have c12 : ⁅perfCent (SU σ 4) (Subgroup.zpowers (torusD ((ω, 1) : D8Mod 3 F))),
      perfCent (SU σ 4) (Subgroup.zpowers (torusD ((1, ω) : D8Mod 3 F)))⁆ = ⊥ := by
    rw [hS₁, hS₂]
    exact commutator_longSL_weyl₁ σ
  have hN₂ : weyl₂ ∈ Subgroup.normalizer (d8Tor 3 F 4 : Set (GL (Fin 4) F)) := by
    refine mem_normalizer_of_conj_le hww₂ ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨(v.1, v.2⁻¹), (conj_weyl₂ v).symm⟩
  refine ⟨fun ℓ hℓ h3 => ?_, fun ℓ₁ ℓ₂ c₁ c₂ h₁ h₂ hc₁ hc₂ h₁3 h₂3 hc₁3 hc₂3 hne hc₁S hc₂S => ?_⟩
  · rcases line_cases hμ hω hℓ h3 with rfl | rfl | rfl | rfl
    · exact Or.inl e₁
    · exact Or.inl e₂
    · exact Or.inr e₃
    · exact Or.inr e₄
  · rcases hpartner ℓ₁ c₁ h₁ h₁3 hc₁ hc₁3 hc₁S with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hpartner ℓ₂ c₂ h₂ h₂3 hc₂ hc₂3 hc₂S with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · exact ⟨fun _ => ⟨rfl, Or.inl c12⟩, fun h => absurd rfl h⟩
    · exact ⟨fun h => absurd h (hdist _ _ e₂ e₃), fun _ => g13⟩
    · exact ⟨fun h => absurd h (hdist _ _ e₂ e₄), fun _ => g14⟩
    · exact ⟨fun _ => ⟨rfl, Or.inl (by rw [Subgroup.commutator_comm]; exact c12)⟩,
        fun h => absurd rfl h⟩
    · exact absurd rfl hne
    · exact ⟨fun h => absurd h (hdist _ _ e₁ e₃), fun _ => g23⟩
    · exact ⟨fun h => absurd h (hdist _ _ e₁ e₄), fun _ => g24⟩
    · exact ⟨fun h => absurd h.symm (hdist _ _ e₁ e₄), fun _ => by rw [sup_comm]; exact g13⟩
    · exact ⟨fun h => absurd h.symm (hdist _ _ e₂ e₄), fun _ => by rw [sup_comm]; exact g23⟩
    · exact absurd rfl hne
    · exact ⟨fun _ => ⟨rfl, Or.inr ⟨g34, e₃, e₄, weyl₂, hw₂, hN₂, hL₄, hL₃⟩⟩,
        fun h => absurd rfl h⟩
    · exact ⟨fun h => absurd h.symm (hdist _ _ e₁ e₃), fun _ => by rw [sup_comm]; exact g14⟩
    · exact ⟨fun h => absurd h.symm (hdist _ _ e₂ e₃), fun _ => by rw [sup_comm]; exact g24⟩
    · exact ⟨fun _ => ⟨rfl, Or.inr ⟨by rw [sup_comm]; exact g34, e₄, e₃, weyl₂, hw₂, hN₂, hL₃,
        hL₄⟩⟩, fun h => absurd rfl h⟩
    · exact absurd rfl hne

end Model

end CFSG.RankThree.PartTwo.Sec21.Item228InspProof
