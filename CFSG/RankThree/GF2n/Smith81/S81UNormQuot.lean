module

public import CFSG.RankThree.GF2n.Smith81.S81UAct
public import CFSG.RankThree.GF2n.Smith81.S81UNormalizer
public import CFSG.RankThree.GF2n.Smith81.S81UNorm

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

section Convert

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K] (e : K ≃+* Fσ σ)

@[expose] noncomputable def toWform (T : E3UWspace σ e ≃ₗ[K] E3UWspace σ e) : Wform σ ≃ₗ[Fσ σ] Wform σ where
  toFun w := (show Wform σ from T (show E3UWspace σ e from w))
  map_add' x y := map_add T (show E3UWspace σ e from x) (show E3UWspace σ e from y)
  map_smul' c x := by
    have h := T.map_smul (e.symm c) (show E3UWspace σ e from x)
    have e1 : (e.symm c • (show E3UWspace σ e from x)) = (show E3UWspace σ e from (c • x)) := by
      rw [e3uWspace_smul_def, RingEquiv.apply_symm_apply]
    rw [e1] at h
    have e2 : (e.symm c • T (show E3UWspace σ e from x)) =
        (show E3UWspace σ e from (c • (show Wform σ from T (show E3UWspace σ e from x)))) := by
      rw [e3uWspace_smul_def, RingEquiv.apply_symm_apply]
    rw [e2] at h
    exact h
  invFun w := (show Wform σ from T.symm (show E3UWspace σ e from w))
  left_inv w := T.symm_apply_apply (show E3UWspace σ e from w)
  right_inv w := T.apply_symm_apply (show E3UWspace σ e from w)

theorem toWform_mul (T₁ T₂ : E3UWspace σ e ≃ₗ[K] E3UWspace σ e) :
    toWform e (T₁ * T₂) = toWform e T₁ * toWform e T₂ := rfl

theorem toWform_one : toWform e (1 : E3UWspace σ e ≃ₗ[K] E3UWspace σ e) = 1 := rfl

theorem toWform_pow (T : E3UWspace σ e ≃ₗ[K] E3UWspace σ e) (n : ℕ) :
    toWform e (T ^ n) = toWform e T ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, toWform_mul, ih]

theorem toWform_injective : Function.Injective (toWform (σ := σ) e) := by
  intro T T' h
  refine LinearEquiv.ext fun w => ?_
  exact congrArg (fun S : Wform σ ≃ₗ[Fσ σ] Wform σ => S (show Wform σ from w)) h

theorem toWform_e3uWact (g : SUid σ 6) : toWform e (e3uWact σ e g) = Wact σ g := rfl

end Convert

section Main

def InnerU {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F) (T : Wform σ ≃ₗ[Fσ σ] Wform σ) : Prop :=
  ∃ (P : GL (Fin 6) F) (μ : F), conjTr σ (P : Matrix (Fin 6) (Fin 6) F) *
      (P : Matrix (Fin 6) (Fin 6) F) = 1 ∧
    ∀ w : Wform σ, ((T w : Wform σ) : Cube F) = μ • rho F P (w : Cube F)

def FieldU {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F) (T : Wform σ ≃ₗ[Fσ σ] Wform σ) : Prop :=
  ∃ (P : GL (Fin 6) F) (μ : F), conjTr σ (P : Matrix (Fin 6) (Fin 6) F) *
      (P : Matrix (Fin 6) (Fin 6) F) = 1 ∧
    ∀ w : Wform σ, ((T w : Wform σ) : Cube F) = μ • rho F P (sigmaC σ (w : Cube F))

theorem innerU_or_fieldU {F : Type} [Field F] [CharP F 2] [Finite F] {σ : F ≃+* F} {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hσF : σ = unitaryInvolution F 2 f)
    {T : Wform σ ≃ₗ[Fσ σ] Wform σ} (hT : NormalizesU σ T) : InnerU σ T ∨ FieldU σ T := by
  obtain ⟨P, μ, τ, hτ, hP, hTP⟩ := u6_normalizer_dichotomy hF hσF hT
  rcases hτ with rfl | rfl
  · exact Or.inl ⟨P, μ, hP, fun w => by rw [hTP w, sigmaC_refl]⟩
  · exact Or.inr ⟨P, μ, hP, hTP⟩

variable {G : Type} [Group G] [Finite G]

theorem normQuotE3U_of_uniform (hFE1 : Smith24E3UUniformStatement) : NormQuotE3UStatement := by
  intro G _ _ M Q Z B IH hc h3U E hEH0 hE2
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨F, _, _, _, f, hF, e, ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h3U K γ M₀ hg
  have hctx : Ctx M Q Z B := hc.ctx
  have hH : StrothHyp M Q Z := hctx.hyp
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  have hEM : ∀ m ∈ E, m ∈ M := fun m hm => (Subgroup.mem_inf.mp (hEH0 hm)).1
  have hpow : ∀ m ∈ E, ∃ k : ℕ, m ^ (2 ^ k) = 1 := by
    intro m hm
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hE2) ⟨m, hm⟩
    refine ⟨k, ?_⟩
    have h1 := pow_orderOf_eq_one (⟨m, hm⟩ : E)
    rw [hk] at h1
    exact congrArg Subtype.val h1
  have hact : ∀ m ∈ E, ∃ T : E3UWspace (unitaryInvolution F 2 f) e ≃ₗ[K]
      E3UWspace (unitaryInvolution F 2 f) e, ActsOnQtAsU ψ m T ∧
      NormalizesU (unitaryInvolution F 2 f) (toWform e T) ∧ ∃ k : ℕ, T ^ (2 ^ k) = 1 := by
    intro m hm
    obtain ⟨T, hT⟩ := exists_actsOnQtAsU hg ψ (hEH0 hm)
    obtain ⟨k, hk⟩ := hpow m hm
    refine ⟨T, hT, ?_, k, hT.pow_eq_one hH (hEM m hm) hk⟩
    intro g
    obtain ⟨g', hg', hTg⟩ := hT.normalizesGamma hctx d (hEM m hm) (e3uWact _ e g)
      (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    obtain ⟨g₂, rfl⟩ := MonoidHom.mem_range.mp hg'
    exact ⟨g₂, by
      rw [← toWform_e3uWact e g, ← toWform_e3uWact e g₂, ← toWform_mul, ← toWform_mul, hTg]⟩
  have hinner : ∀ m ∈ E, ∀ T : E3UWspace (unitaryInvolution F 2 f) e ≃ₗ[K]
      E3UWspace (unitaryInvolution F 2 f) e, ActsOnQtAsU ψ m T → (∃ k : ℕ, T ^ (2 ^ k) = 1) →
      InnerU (unitaryInvolution F 2 f) (toWform e T) → m ∈ Lgen M (LB M Q B) := by
    intro m hm T hT hk hI
    obtain ⟨k, hk⟩ := hk
    obtain ⟨P, μ, hP, hTP⟩ := hI
    obtain ⟨g, hg⟩ := mem_Gam_of_innerTypeU_pow hσ hP hTP (k := k)
      (by rw [← toWform_pow, hk, toWform_one])
    have hTg : T = e3uWact _ e g := toWform_injective e (by rw [hg]; rfl)
    exact hT.mem_Lgen hctx d (hEM m hm) (by rw [hTg]; exact MonoidHom.mem_range.mpr ⟨g, rfl⟩)
  have hmul : ∀ m₁ ∈ E, ∀ m ∈ E, m₁ ∉ Lgen M (LB M Q B) → m ∉ Lgen M (LB M Q B) →
      m₁ * m ∈ Lgen M (LB M Q B) := by
    intro m₁ hm₁ m hm hn₁ hn
    obtain ⟨T₁, hT₁, hN₁, hk₁⟩ := hact m₁ hm₁
    obtain ⟨T, hT, hN, hk⟩ := hact m hm
    have hf₁ : FieldU (unitaryInvolution F 2 f) (toWform e T₁) :=
      (innerU_or_fieldU hF rfl hN₁).resolve_left fun hI => hn₁ (hinner m₁ hm₁ T₁ hT₁ hk₁ hI)
    have hf₂ : FieldU (unitaryInvolution F 2 f) (toWform e T) :=
      (innerU_or_fieldU hF rfl hN).resolve_left fun hI => hn (hinner m hm T hT hk hI)
    obtain ⟨P₁, μ₁, hP₁, h₁⟩ := hf₁
    obtain ⟨P₂, μ₂, hP₂, h₂⟩ := hf₂
    obtain ⟨hP, hTT⟩ := innerType_mul_of_fieldType hσ hP₁ hP₂ h₁ h₂
    have hI : InnerU (unitaryInvolution F 2 f) (toWform e (T₁ * T)) :=
      ⟨P₁ * glAut _ P₂, μ₁ * unitaryInvolution F 2 f μ₂, hP, fun w => by
        rw [toWform_mul]; exact hTT w⟩
    have hTT' : ActsOnQtAsU ψ (m₁ * m) (T₁ * T) := ActsOnQtAsU.mul hH (hEM m hm) hT₁ hT
    obtain ⟨k, hk'⟩ := hpow (m₁ * m) (E.mul_mem hm₁ hm)
    have hTk : (T₁ * T) ^ (2 ^ k) = 1 :=
      hTT'.pow_eq_one hH (M.mul_mem (hEM m₁ hm₁) (hEM m hm)) hk'
    exact hinner (m₁ * m) (E.mul_mem hm₁ hm) (T₁ * T) hTT' ⟨k, hTk⟩ hI
  by_cases hE1 : E ≤ Lgen M (LB M Q B)
  · rw [inf_eq_left.mpr hE1]
    omega
  · obtain ⟨m₁, hm₁E, hm₁⟩ : ∃ m₁ ∈ E, m₁ ∉ Lgen M (LB M Q B) := by
      by_contra hcon
      push Not at hcon
      exact hE1 hcon
    have hsub : (E : Set G) ⊆ ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G) ∪
        (fun x => m₁⁻¹ * x) '' ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G) := by
      intro m hm
      by_cases hmL : m ∈ Lgen M (LB M Q B)
      · exact Or.inl ⟨hm, hmL⟩
      · refine Or.inr ⟨m₁ * m, ⟨E.mul_mem hm₁E hm, hmul m₁ hm₁E m hm hm₁ hmL⟩, ?_⟩
        simp
    have h1 : Nat.card ↥E ≤ ((E : Set G)).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact le_refl _
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 := Set.ncard_union_le ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G)
      ((fun x => m₁⁻¹ * x) '' ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G))
    have h4 := Set.ncard_image_le (f := fun x => m₁⁻¹ * x)
      (Set.toFinite ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G))
    have h5 : Nat.card ↥(E ⊓ Lgen M (LB M Q B)) =
        ((E ⊓ Lgen M (LB M Q B) : Subgroup G) : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact le_antisymm le_rfl le_rfl
    omega

end Main

end CFSG.RankThree.GF2n.Smith81
