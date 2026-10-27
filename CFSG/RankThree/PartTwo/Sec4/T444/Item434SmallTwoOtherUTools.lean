module

public import CFSG.ClassicalGroups.Unitary.Generation
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther

namespace UTools

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem herm_smul_of_eigen (g : SUid σ n) {e : Fin n → K} {l m : K} (he : g • e = l • e)
    (hlm : σ l * m = 1) (x : Fin n → K) : herm σ e (g • x) = m * herm σ e x := by
  have h1 := herm_smul_smul σ g e x
  rw [he, herm_smul_left] at h1
  calc herm σ e (g • x) = (σ l * m) * herm σ e (g • x) := by rw [hlm, one_mul]
    _ = m * (σ l * herm σ e (g • x)) := by ring
    _ = m * herm σ e x := by rw [h1]

theorem mul_comm_of_eigen (hσ : ∀ c, σ (σ c) = c) {g s : SUid σ n} {e f : Fin n → K}
    {l m μ ρ : K} (hs : ∀ x, s • x = x + (μ * herm σ e x) • f + (ρ * herm σ f x) • e)
    (he : g • e = l • e) (hf : g • f = m • f) (hlm : σ l * m = 1) : g * s = s * g := by
  have hml : σ m * l = 1 := by
    have h := congrArg σ hlm
    rw [map_mul, hσ, map_one] at h
    rw [mul_comm]
    exact h
  apply ext_smul
  intro x
  rw [mul_smul, mul_smul, hs x, hs (g • x), smul_add, smul_add, smul_comm g _ f,
    smul_comm g _ e, he, hf, herm_smul_of_eigen g he hlm, herm_smul_of_eigen g hf hml]
  generalize g • x = y
  module

theorem mul_self_eq_one_of_smul (h2 : (2 : K) = 0) {s : SUid σ n} {e f : Fin n → K} {μ ρ : K}
    (hs : ∀ x, s • x = x + (μ * herm σ e x) • f + (ρ * herm σ f x) • e)
    (hee : herm σ e e = 0) (hff : herm σ f f = 0) (hef : herm σ e f = 0)
    (hfe : herm σ f e = 0) : s * s = 1 := by
  apply ext_smul
  intro x
  rw [mul_smul, hs (s • x), hs x, one_smul]
  simp only [herm_add_right, herm_smul_right, hee, hff, hef, hfe, mul_zero, add_zero]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (μ * herm σ e x * f i + ρ * herm σ f x * e i) * h2

structure HypPair (σ : K ≃+* K) (n : ℕ) where
  e : Fin n → K
  f : Fin n → K
  hee : herm σ e e = 0
  hff : herm σ f f = 0
  hef : herm σ e f = 1

namespace HypPair

variable (P : HypPair σ n)

theorem hfe (hσ : ∀ c, σ (σ c) = c) : herm σ P.f P.e = 1 := by
  rw [herm_conj σ hσ, P.hef, map_one]

theorem e_ne_zero : P.e ≠ 0 := by
  intro h
  have := P.hef
  rw [h, herm_zero_left] at this
  exact zero_ne_one this

theorem f_ne_zero : P.f ≠ 0 := by
  intro h
  have := P.hef
  rw [h, herm_zero_right] at this
  exact zero_ne_one this

end HypPair

@[expose] noncomputable def planeMat (σ : K ≃+* K) (e f : Fin n → K) (a : K) :
    Matrix (Fin n) (Fin n) K :=
  (1 + vecMulVec ((a - 1) • e) (fun i => σ (f i))) *
    (1 + vecMulVec ((a⁻¹ - 1) • f) (fun i => σ (e i)))

theorem planeMat_mulVec {e f : Fin n → K} (hff : herm σ f f = 0) (a : K) (x : Fin n → K) :
    planeMat σ e f a *ᵥ x = x + ((a - 1) * herm σ f x) • e + ((a⁻¹ - 1) * herm σ e x) • f := by
  rw [planeMat, ← Matrix.mulVec_mulVec]
  have h1 : ∀ (u w z : Fin n → K),
      (1 + vecMulVec u (fun i => σ (w i))) *ᵥ z = z + herm σ w z • u := by
    intro u w z
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    rfl
  rw [h1, h1]
  simp only [herm_add_right, herm_smul_right, hff, mul_zero, add_zero]
  module

theorem planeMat_det {e f : Fin n → K} (hef : herm σ e f = 1) (hfe : herm σ f e = 1) {a : K}
    (ha : a ≠ 0) : (planeMat σ e f a).det = 1 := by
  rw [planeMat, Matrix.det_mul, Matrix.vecMulVec_eq (Fin 1), Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have e1 : (fun i => σ (f i)) ⬝ᵥ ((a - 1) • e) = herm σ f ((a - 1) • e) := rfl
  have e2 : (fun i => σ (e i)) ⬝ᵥ ((a⁻¹ - 1) • f) = herm σ e ((a⁻¹ - 1) • f) := rfl
  rw [e1, e2, herm_smul_right, herm_smul_right, hfe, hef]
  have h : (1 + (a - 1) * 1) * (1 + (a⁻¹ - 1) * 1) = a * a⁻¹ := by ring
  rw [h, mul_inv_cancel₀ ha]

theorem planeMat_isometry (hσ : ∀ c, σ (σ c) = c) {e f : Fin n → K} (hee : herm σ e e = 0)
    (hff : herm σ f f = 0) (hef : herm σ e f = 1) (hfe : herm σ f e = 1) {a : K}
    (hfix : σ a = a) (ha : a ≠ 0) (x y : Fin n → K) :
    herm σ (planeMat σ e f a *ᵥ x) (planeMat σ e f a *ᵥ y) = herm σ x y := by
  rw [planeMat_mulVec hff, planeMat_mulVec hff]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hee, hff, hef, hfe,
    map_mul, map_sub, map_one, map_inv₀, hfix]
  rw [← herm_conj σ hσ f x, ← herm_conj σ hσ e x]
  have ha' : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  linear_combination (herm σ x e * herm σ f y + herm σ x f * herm σ e y) * ha'

@[expose] noncomputable def planeElt (hσ : ∀ c, σ (σ c) = c) (P : HypPair σ n) {a : K}
    (hfix : σ a = a) (ha : a ≠ 0) : SUid σ n :=
  mkSU σ (planeMat σ P.e P.f a) (planeMat_det P.hef (P.hfe hσ) ha)
    (planeMat_isometry hσ P.hee P.hff P.hef (P.hfe hσ) hfix ha)

section PlaneElt

variable (hσ : ∀ c, σ (σ c) = c) (P : HypPair σ n) {a : K} (hfix : σ a = a) (ha : a ≠ 0)

theorem planeElt_smul (x : Fin n → K) :
    planeElt hσ P hfix ha • x =
      x + ((a - 1) * herm σ P.f x) • P.e + ((a⁻¹ - 1) * herm σ P.e x) • P.f :=
  planeMat_mulVec P.hff a x

theorem planeElt_smul_e : planeElt hσ P hfix ha • P.e = a • P.e := by
  rw [planeElt_smul, P.hfe hσ, P.hee]
  module

theorem planeElt_smul_f : planeElt hσ P hfix ha • P.f = a⁻¹ • P.f := by
  rw [planeElt_smul, P.hff, P.hef]
  module

theorem planeElt_smul_of_perp {x : Fin n → K} (he : herm σ P.e x = 0) (hf : herm σ P.f x = 0) :
    planeElt hσ P hfix ha • x = x := by
  rw [planeElt_smul, he, hf]
  simp

end PlaneElt

@[expose] noncomputable def planeHom (hσ : ∀ c, σ (σ c) = c) (P : HypPair σ n) (Z : Subgroup Kˣ)
    (hZ : ∀ a ∈ Z, σ (a : K) = a) : Z →* SUid σ n where
  toFun a := planeElt hσ P (hZ _ a.2) (a : Kˣ).ne_zero
  map_one' := by
    apply ext_smul
    intro x
    rw [planeElt_smul, one_smul]
    simp
  map_mul' a b := by
    apply ext_smul
    intro x
    rw [mul_smul, planeElt_smul, planeElt_smul, planeElt_smul]
    simp only [herm_add_right, herm_smul_right, P.hee, P.hff, P.hef, P.hfe hσ, mul_zero,
      add_zero, mul_one, Subgroup.coe_mul, Units.val_mul, mul_inv]
    module

theorem planeHom_apply (hσ : ∀ c, σ (σ c) = c) (P : HypPair σ n) (Z : Subgroup Kˣ)
    (hZ : ∀ a ∈ Z, σ (a : K) = a) (a : Z) :
    planeHom hσ P Z hZ a = planeElt hσ P (hZ _ a.2) (a : Kˣ).ne_zero :=
  rfl

structure HypQuad (σ : K ≃+* K) (n : ℕ) where
  P₁ : HypPair σ n
  P₂ : HypPair σ n
  he₁e₂ : herm σ P₁.e P₂.e = 0
  he₁f₂ : herm σ P₁.e P₂.f = 0
  hf₁e₂ : herm σ P₁.f P₂.e = 0
  hf₁f₂ : herm σ P₁.f P₂.f = 0

section Torus

variable (hσ : ∀ c, σ (σ c) = c) (Q : HypQuad σ n) (Z : Subgroup Kˣ)
  (hZ : ∀ a ∈ Z, σ (a : K) = a)

theorem commute_planeHom (a b : Z) :
    Commute (planeHom hσ Q.P₁ Z hZ a) (planeHom hσ Q.P₂ Z hZ b) := by
  have h1 : planeHom hσ Q.P₁ Z hZ a • Q.P₂.e = (1 : K) • Q.P₂.e := by
    rw [one_smul, planeHom_apply]
    exact planeElt_smul_of_perp hσ Q.P₁ _ _ Q.he₁e₂ Q.hf₁e₂
  have h2 : planeHom hσ Q.P₁ Z hZ a • Q.P₂.f = (1 : K) • Q.P₂.f := by
    rw [one_smul, planeHom_apply]
    exact planeElt_smul_of_perp hσ Q.P₁ _ _ Q.he₁f₂ Q.hf₁f₂
  exact mul_comm_of_eigen hσ (μ := ((b : Kˣ) : K) - 1) (ρ := ((b : Kˣ) : K)⁻¹ - 1)
    (fun x => by rw [planeHom_apply, planeElt_smul]) h2 h1 (by rw [map_one, one_mul])

@[expose] noncomputable def torusHom : Z × Z →* SUid σ n :=
  (planeHom hσ Q.P₁ Z hZ).noncommCoprod (planeHom hσ Q.P₂ Z hZ) (commute_planeHom hσ Q Z hZ)

theorem torusHom_apply (p : Z × Z) :
    torusHom hσ Q Z hZ p = planeHom hσ Q.P₁ Z hZ p.1 * planeHom hσ Q.P₂ Z hZ p.2 :=
  rfl

theorem torusHom_smul_e₁ (p : Z × Z) :
    torusHom hσ Q Z hZ p • Q.P₁.e = ((p.1 : Kˣ) : K) • Q.P₁.e := by
  have h0 : herm σ Q.P₂.e Q.P₁.e = 0 := herm_eq_zero_comm σ hσ Q.he₁e₂
  have h1 : herm σ Q.P₂.f Q.P₁.e = 0 := herm_eq_zero_comm σ hσ Q.he₁f₂
  rw [torusHom_apply, mul_smul, planeHom_apply, planeHom_apply,
    planeElt_smul_of_perp hσ Q.P₂ _ _ h0 h1, planeElt_smul_e]

theorem torusHom_smul_f₁ (p : Z × Z) :
    torusHom hσ Q Z hZ p • Q.P₁.f = ((p.1 : Kˣ) : K)⁻¹ • Q.P₁.f := by
  have h0 : herm σ Q.P₂.e Q.P₁.f = 0 := herm_eq_zero_comm σ hσ Q.hf₁e₂
  have h1 : herm σ Q.P₂.f Q.P₁.f = 0 := herm_eq_zero_comm σ hσ Q.hf₁f₂
  rw [torusHom_apply, mul_smul, planeHom_apply, planeHom_apply,
    planeElt_smul_of_perp hσ Q.P₂ _ _ h0 h1, planeElt_smul_f]

theorem torusHom_smul_e₂ (p : Z × Z) :
    torusHom hσ Q Z hZ p • Q.P₂.e = ((p.2 : Kˣ) : K) • Q.P₂.e := by
  rw [torusHom_apply, mul_smul, planeHom_apply, planeHom_apply, planeElt_smul_e, smul_comm,
    planeElt_smul_of_perp hσ Q.P₁ _ _ Q.he₁e₂ Q.hf₁e₂]

theorem torusHom_smul_f₂ (p : Z × Z) :
    torusHom hσ Q Z hZ p • Q.P₂.f = ((p.2 : Kˣ) : K)⁻¹ • Q.P₂.f := by
  rw [torusHom_apply, mul_smul, planeHom_apply, planeHom_apply, planeElt_smul_f, smul_comm,
    planeElt_smul_of_perp hσ Q.P₁ _ _ Q.he₁f₂ Q.hf₁f₂]

theorem torusHom_smul_of_perp₁ (a : Z) {y : Fin n → K} (h1 : herm σ Q.P₁.e y = 0)
    (h2 : herm σ Q.P₁.f y = 0) : torusHom hσ Q Z hZ (a, 1) • y = y := by
  rw [torusHom_apply, mul_smul]
  change planeHom hσ Q.P₁ Z hZ a • planeHom hσ Q.P₂ Z hZ 1 • y = y
  rw [map_one, one_smul, planeHom_apply, planeElt_smul_of_perp hσ Q.P₁ _ _ h1 h2]

theorem torusHom_smul_of_perp₂ (b : Z) {y : Fin n → K} (h1 : herm σ Q.P₂.e y = 0)
    (h2 : herm σ Q.P₂.f y = 0) : torusHom hσ Q Z hZ (1, b) • y = y := by
  rw [torusHom_apply, mul_smul]
  change planeHom hσ Q.P₁ Z hZ 1 • planeHom hσ Q.P₂ Z hZ b • y = y
  rw [map_one, one_smul, planeHom_apply, planeElt_smul_of_perp hσ Q.P₂ _ _ h1 h2]

theorem eq_one_of_torusHom_smul (h2 : (2 : K) = 0) {p : Z × Z} {c : K}
    (hc : ∀ v : Fin n → K, torusHom hσ Q Z hZ p • v = c • v) : p = 1 := by
  have key : ∀ (a : K) (u w : Fin n → K), u ≠ 0 → w ≠ 0 → a ≠ 0 → a • u = c • u →
      a⁻¹ • w = c • w → a = 1 := by
    intro a u w hu hw ha h1 h2'
    have hac : a = c := smul_left_injective K hu h1
    have hac' : a⁻¹ = c := smul_left_injective K hw h2'
    have haa : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [hac', ← hac]
        _ = 1 := mul_inv_cancel₀ ha
    have h0 : (a - 1) * (a - 1) = 0 := by linear_combination haa + (1 - a) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)
  have ha := key _ Q.P₁.e Q.P₁.f Q.P₁.e_ne_zero Q.P₁.f_ne_zero (p.1 : Kˣ).ne_zero
    ((torusHom_smul_e₁ hσ Q Z hZ p).symm.trans (hc _))
    ((torusHom_smul_f₁ hσ Q Z hZ p).symm.trans (hc _))
  have hb := key _ Q.P₂.e Q.P₂.f Q.P₂.e_ne_zero Q.P₂.f_ne_zero (p.2 : Kˣ).ne_zero
    ((torusHom_smul_e₂ hσ Q Z hZ p).symm.trans (hc _))
    ((torusHom_smul_f₂ hσ Q Z hZ p).symm.trans (hc _))
  exact Prod.ext (Subtype.ext (Units.ext ha)) (Subtype.ext (Units.ext hb))

end Torus

theorem exists_siegel_perp (hσ : IsUnitaryInvolution σ) (P : HypPair σ n) {e : Fin n → K}
    (hee : herm σ e e = 0) (he₂ : herm σ e P.e = 0) (hf₂ : herm σ e P.f = 0) {a : Fin n → K}
    (ha : herm σ e a ≠ 0) :
    ∃ g₁ g₂ : SUid σ n,
      (∃ μ : K, ∀ x, g₁ • x = x + (μ * herm σ e x) • P.f - (σ μ * herm σ P.f x) • e) ∧
      (∃ μ : K, ∀ x, g₂ • x = x + (μ * herm σ e x) • P.e - (σ μ * herm σ P.e x) • e) ∧
      herm σ P.e ((g₂ * g₁) • a) = 0 ∧ herm σ P.f ((g₂ * g₁) • a) = 0 := by
  have h2e : herm σ P.e e = 0 := herm_eq_zero_comm σ hσ.invol he₂
  have h2f : herm σ P.f e = 0 := herm_eq_zero_comm σ hσ.invol hf₂
  have hfe := P.hfe hσ.invol
  obtain ⟨g₁, -, hg₁⟩ := exists_mem_T_siegel hσ hee P.hff hf₂ (-herm σ P.e a / herm σ e a)
  obtain ⟨g₂, -, hg₂⟩ := exists_mem_T_siegel hσ hee P.hee he₂ (-herm σ P.f a / herm σ e a)
  refine ⟨g₁, g₂, ⟨_, hg₁⟩, ⟨_, hg₂⟩, ?_, ?_⟩
  · rw [mul_smul, hg₂, hg₁]
    simp only [herm_add_right, herm_sub_right, herm_smul_right, P.hee, P.hef, h2e, hee, hf₂,
      mul_zero, sub_zero, add_zero, mul_one]
    field_simp
    ring
  · rw [mul_smul, hg₂, hg₁]
    simp only [herm_add_right, herm_sub_right, herm_smul_right, P.hff, P.hef, hfe, h2e, h2f, hee,
      hf₂, mul_zero, sub_zero, add_zero, mul_one]
    field_simp
    ring

theorem eq_top_of_siegel_tv (hσ : IsUnitaryInvolution σ) (hn : 4 ≤ n) (Q : HypQuad σ n)
    {H : Subgroup (SUid σ n)}
    (hS : ∀ e f : Fin n → K, (e = Q.P₁.e ∨ e = Q.P₁.f) → (f = Q.P₂.e ∨ f = Q.P₂.f) →
      ∀ (μ : K) (g : SUid σ n),
        (∀ x, g • x = x + (μ * herm σ e x) • f - (σ μ * herm σ f x) • e) → g ∈ H)
    (hT : ∀ (y : Fin n → K) (c : K), herm σ y y = 0 → c + σ c = 0 →
      ((herm σ Q.P₁.e y = 0 ∧ herm σ Q.P₁.f y = 0) ∨
        (herm σ Q.P₂.e y = 0 ∧ herm σ Q.P₂.f y = 0)) →
      ∀ g : SUid σ n, (∀ x, g • x = x + (c * herm σ y x) • y) → g ∈ H) :
    H = ⊤ := by
  have key : ∀ e : Fin n → K, (e = Q.P₁.e ∨ e = Q.P₁.f) → ∀ a : Fin n → K, herm σ e a ≠ 0 →
      ∃ k ∈ H, herm σ Q.P₂.e (k • a) = 0 ∧ herm σ Q.P₂.f (k • a) = 0 := by
    intro e he a ha
    have hee : herm σ e e = 0 := by
      rcases he with rfl | rfl
      exacts [Q.P₁.hee, Q.P₁.hff]
    have he₂ : herm σ e Q.P₂.e = 0 := by
      rcases he with rfl | rfl
      exacts [Q.he₁e₂, Q.hf₁e₂]
    have hf₂ : herm σ e Q.P₂.f = 0 := by
      rcases he with rfl | rfl
      exacts [Q.he₁f₂, Q.hf₁f₂]
    obtain ⟨g₁, g₂, ⟨μ₁, hg₁⟩, ⟨μ₂, hg₂⟩, h1, h2⟩ := exists_siegel_perp hσ Q.P₂ hee he₂ hf₂ ha
    exact ⟨g₂ * g₁, H.mul_mem (hS e _ he (Or.inl rfl) μ₂ g₂ hg₂)
      (hS e _ he (Or.inr rfl) μ₁ g₁ hg₁), h1, h2⟩
  rw [eq_top_iff, ← T_eq_top hσ (by omega) (fun h => absurd h (by omega)), T,
    Subgroup.closure_le]
  rintro g ⟨a, c, ha, hc, hg⟩
  have hconj : ∀ k ∈ H, ((herm σ Q.P₁.e (k • a) = 0 ∧ herm σ Q.P₁.f (k • a) = 0) ∨
      (herm σ Q.P₂.e (k • a) = 0 ∧ herm σ Q.P₂.f (k • a) = 0)) → g ∈ H := by
    intro k hk hka
    have h1 : k * g * k⁻¹ ∈ H :=
      hT (k • a) c (by rw [herm_smul_smul, ha]) hc hka _ (conj_smul_of_tv k g hg)
    have h2 : g = k⁻¹ * (k * g * k⁻¹) * k := by group
    rw [h2]
    exact H.mul_mem (H.mul_mem (H.inv_mem hk) h1) hk
  by_cases h1 : herm σ Q.P₁.e a = 0
  · by_cases h2 : herm σ Q.P₁.f a = 0
    · exact hconj 1 H.one_mem (Or.inl ⟨by rw [one_smul]; exact h1, by rw [one_smul]; exact h2⟩)
    · obtain ⟨k, hk, hk1, hk2⟩ := key _ (Or.inr rfl) a h2
      exact hconj k hk (Or.inr ⟨hk1, hk2⟩)
  · obtain ⟨k, hk, hk1, hk2⟩ := key _ (Or.inl rfl) a h1
    exact hconj k hk (Or.inr ⟨hk1, hk2⟩)

theorem injective_comp_torusHom (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0)
    (Q : HypQuad σ n) {Z : Subgroup Kˣ} (hZ : ∀ a ∈ Z, σ (a : K) = a) {X : Type*} [Group X]
    (π : SUid σ n →* X)
    (hπ : ∀ g : SUid σ n, π g = 1 → ∃ c : K, ∀ v : Fin n → K, g • v = c • v) :
    Function.Injective (π.comp (torusHom hσ.invol Q Z hZ)) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  obtain ⟨c, hc⟩ := hπ _ hp
  exact eq_one_of_torusHom_smul hσ.invol Q Z hZ h2 hc

theorem closure_coprime_eq_top (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0)
    (Q : HypQuad σ n) {Z : Subgroup Kˣ} (hZ : ∀ a ∈ Z, σ (a : K) = a) {X : Type*} [Group X]
    (π : SUid σ n →* X)
    (hπ : ∀ g : SUid σ n, π g = 1 → ∃ c : K, ∀ v : Fin n → K, g • v = c • v)
    (hn : 4 ≤ n) {ω : Kˣ} (hωZ : ω ∈ Z) (hω1 : ω ≠ 1) (hπs : Function.Surjective π) :
    Subgroup.closure {x : X | Nat.Coprime (orderOf x) 3 ∧
      ∃ p ∈ (π.comp (torusHom hσ.invol Q Z hZ)).range, p ≠ 1 ∧ p * x = x * p} = ⊤ := by
  set D := torusHom hσ.invol Q Z hZ with hD
  set S := {x : X | Nat.Coprime (orderOf x) 3 ∧
      ∃ p ∈ (π.comp D).range, p ≠ 1 ∧ p * x = x * p} with hSdef
  have hinj := injective_comp_torusHom hσ h2 Q hZ π hπ
  have hmem : ∀ g : SUid σ n, g * g = 1 → ∀ p : Z × Z, p ≠ 1 → D p * g = g * D p →
      π g ∈ Subgroup.closure S := by
    intro g hg p hp hpg
    apply Subgroup.subset_closure
    refine ⟨?_, π (D p), ⟨p, rfl⟩, fun h1 => hp (hinj ?_), ?_⟩
    · have h : π g ^ 2 = 1 := by rw [← map_pow, sq, hg, map_one]
      exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h) (by norm_num)
    · rw [map_one]
      exact h1
    · rw [← map_mul, ← map_mul, hpg]
  set ω' : Z := ⟨ω, hωZ⟩ with hω'
  have hω'1 : ω' ≠ 1 := fun h => hω1 (congrArg Subtype.val h)
  have hfω : σ (ω : K) = ω := hZ ω hωZ
  have hω0 : (ω : K) ≠ 0 := ω.ne_zero
  have hpne : ∀ q : Z, ((ω', q) : Z × Z) ≠ 1 := fun q h => hω'1 (congrArg Prod.fst h)
  have hpne' : ∀ q : Z, ((q, ω') : Z × Z) ≠ 1 := fun q h => hω'1 (congrArg Prod.snd h)
  have hc2 : (((ω'⁻¹ : Z) : Kˣ) : K) = (ω : K)⁻¹ := by
    rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  have htop : (Subgroup.closure S).comap π = ⊤ := by
    refine eq_top_of_siegel_tv hσ hn Q ?_ ?_
    · intro e f he hf μ g hg
      have hs : ∀ x, g • x = x + (μ * herm σ e x) • f + (-σ μ * herm σ f x) • e := by
        intro x
        rw [hg, neg_mul, neg_smul, sub_eq_add_neg]
      have hee : herm σ e e = 0 := by
        rcases he with rfl | rfl
        exacts [Q.P₁.hee, Q.P₁.hff]
      have hff : herm σ f f = 0 := by
        rcases hf with rfl | rfl
        exacts [Q.P₂.hee, Q.P₂.hff]
      have hef : herm σ e f = 0 := by
        rcases he with rfl | rfl <;> rcases hf with rfl | rfl
        exacts [Q.he₁e₂, Q.he₁f₂, Q.hf₁e₂, Q.hf₁f₂]
      have hfe : herm σ f e = 0 := herm_eq_zero_comm σ hσ.invol hef
      have hgg := mul_self_eq_one_of_smul h2 hs hee hff hef hfe
      change π g ∈ Subgroup.closure S
      rcases he with rfl | rfl <;> rcases hf with rfl | rfl
      ·
        refine hmem g hgg (ω', ω'⁻¹) (hpne _) (mul_comm_of_eigen hσ.invol hs
          (torusHom_smul_e₁ hσ.invol Q Z hZ _) (torusHom_smul_e₂ hσ.invol Q Z hZ _) ?_)
        change σ (ω : K) * (((ω'⁻¹ : Z) : Kˣ) : K) = 1
        rw [hc2, hfω, mul_inv_cancel₀ hω0]
      ·
        refine hmem g hgg (ω', ω') (hpne _) (mul_comm_of_eigen hσ.invol hs
          (torusHom_smul_e₁ hσ.invol Q Z hZ _) (torusHom_smul_f₂ hσ.invol Q Z hZ _) ?_)
        change σ (ω : K) * (ω : K)⁻¹ = 1
        rw [hfω, mul_inv_cancel₀ hω0]
      ·
        refine hmem g hgg (ω', ω') (hpne _) (mul_comm_of_eigen hσ.invol hs
          (torusHom_smul_f₁ hσ.invol Q Z hZ _) (torusHom_smul_e₂ hσ.invol Q Z hZ _) ?_)
        change σ (ω : K)⁻¹ * (ω : K) = 1
        rw [map_inv₀, hfω, inv_mul_cancel₀ hω0]
      ·
        refine hmem g hgg (ω', ω'⁻¹) (hpne _) (mul_comm_of_eigen hσ.invol hs
          (torusHom_smul_f₁ hσ.invol Q Z hZ _) (torusHom_smul_f₂ hσ.invol Q Z hZ _) ?_)
        change σ (ω : K)⁻¹ * ((((ω'⁻¹ : Z) : Kˣ) : K))⁻¹ = 1
        rw [hc2, inv_inv, map_inv₀, hfω, inv_mul_cancel₀ hω0]
    · intro y c hy _ hperp g hg
      have hs : ∀ x, g • x = x + (c * herm σ y x) • y + (0 * herm σ y x) • y := by
        intro x
        rw [hg, zero_mul, zero_smul, add_zero]
      have hgg := mul_self_eq_one_of_smul h2 hs hy hy hy hy
      change π g ∈ Subgroup.closure S
      rcases hperp with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
      · have hfix : D (ω', 1) • y = (1 : K) • y := by
          rw [one_smul]
          exact torusHom_smul_of_perp₁ hσ.invol Q Z hZ ω' h1 h1'
        exact hmem g hgg (ω', 1) (hpne _)
          (mul_comm_of_eigen hσ.invol hs hfix hfix (by rw [map_one, one_mul]))
      · have hfix : D (1, ω') • y = (1 : K) • y := by
          rw [one_smul]
          exact torusHom_smul_of_perp₂ hσ.invol Q Z hZ ω' h1 h1'
        exact hmem g hgg (1, ω') (hpne' _)
          (mul_comm_of_eigen hσ.invol hs hfix hfix (by rw [map_one, one_mul]))
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := hπs x
  have hg : g ∈ (Subgroup.closure S).comap π := by
    rw [htop]
    exact Subgroup.mem_top g
  exact hg

theorem herm_single_add_single_left (i j : Fin n) (t : K) (y : Fin n → K) :
    herm σ (Pi.single i 1 + Pi.single j t) y = y i + σ t * y j := by
  rw [herm_add_left, herm_single_left, herm_single_left, map_one, one_mul]

@[expose] noncomputable def coordPair (W : WittData σ) {i j : Fin n} (hij : i ≠ j) :
    HypPair σ n where
  e := Pi.single i 1 + Pi.single j W.u
  f := (1 - W.ω)⁻¹ • (Pi.single i 1 + Pi.single j (W.u * W.ω))
  hee := by
    rw [herm_single_add_single_left]
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne hij.symm, add_zero, zero_add]
    linear_combination W.hu
  hff := by
    rw [herm_smul_left, herm_smul_right, herm_single_add_single_left]
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne hij.symm, add_zero, zero_add, map_mul]
    linear_combination (σ (1 - W.ω)⁻¹ * (1 - W.ω)⁻¹) * (σ W.ω * W.ω * W.hu - W.hω)
  hef := by
    rw [herm_smul_right, herm_single_add_single_left]
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne hij.symm, add_zero, zero_add]
    linear_combination (1 - W.ω)⁻¹ * W.ω * W.hu + inv_mul_cancel₀ W.one_sub_ω_ne_zero

theorem herm_coordPair_e_eq_zero (W : WittData σ) {i j : Fin n} (hij : i ≠ j) {y : Fin n → K}
    (hi : y i = 0) (hj : y j = 0) : herm σ (coordPair W hij).e y = 0 := by
  change herm σ (Pi.single i 1 + Pi.single j W.u) y = 0
  rw [herm_single_add_single_left, hi, hj]
  ring

theorem herm_coordPair_f_eq_zero (W : WittData σ) {i j : Fin n} (hij : i ≠ j) {y : Fin n → K}
    (hi : y i = 0) (hj : y j = 0) : herm σ (coordPair W hij).f y = 0 := by
  change herm σ ((1 - W.ω)⁻¹ • (Pi.single i 1 + Pi.single j (W.u * W.ω))) y = 0
  rw [herm_smul_left, herm_single_add_single_left, hi, hj]
  ring

theorem coordPair_e_apply (W : WittData σ) {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) : (coordPair W hij).e k = 0 := by
  change (Pi.single i 1 + Pi.single j W.u : Fin n → K) k = 0
  simp [hki, hkj]

theorem coordPair_f_apply (W : WittData σ) {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) : (coordPair W hij).f k = 0 := by
  change ((1 - W.ω)⁻¹ • (Pi.single i 1 + Pi.single j (W.u * W.ω)) : Fin n → K) k = 0
  simp [hki, hkj]

@[expose] noncomputable def stdQuad (W : WittData σ) (hn : 4 ≤ n) : HypQuad σ n where
  P₁ := coordPair W (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp)
  P₂ := coordPair W (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩) (by simp)
  he₁e₂ := herm_coordPair_e_eq_zero W _ (coordPair_e_apply W _ (by simp) (by simp))
    (coordPair_e_apply W _ (by simp) (by simp))
  he₁f₂ := herm_coordPair_e_eq_zero W _ (coordPair_f_apply W _ (by simp) (by simp))
    (coordPair_f_apply W _ (by simp) (by simp))
  hf₁e₂ := herm_coordPair_f_eq_zero W _ (coordPair_e_apply W _ (by simp) (by simp))
    (coordPair_e_apply W _ (by simp) (by simp))
  hf₁f₂ := herm_coordPair_f_eq_zero W _ (coordPair_f_apply W _ (by simp) (by simp))
    (coordPair_f_apply W _ (by simp) (by simp))

section GF16

open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.Assembly.RankThreeEven (projSU)

local notation "𝕂" => GaloisField 2 (2 * 2)
local notation "σ₁₆" => unitaryInvolution (GaloisField 2 (2 * 2)) 2 2

theorem card_gf16 : Nat.card 𝕂 = (2 ^ 2) ^ 2 := by
  rw [GaloisField.card 2 (2 * 2) (by norm_num), pow_mul]

theorem isUnitaryInvolution_gf16 : IsUnitaryInvolution σ₁₆ :=
  isUnitaryInvolution_unitaryInvolution card_gf16

theorem two_eq_zero_gf16 : (2 : 𝕂) = 0 := by
  exact_mod_cast CharP.cast_eq_zero 𝕂 2

theorem exists_orderOf_eq_three_gf16 : ∃ ω : 𝕂ˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : Nat.card 𝕂ˣ = 15 := (card_units_of_card card_gf16).trans (by norm_num)
  exact exists_prime_orderOf_dvd_card' 3 (by rw [h]; norm_num)

@[expose] noncomputable def ω₁₆ : 𝕂ˣ := exists_orderOf_eq_three_gf16.choose

theorem orderOf_ω₁₆ : orderOf ω₁₆ = 3 := exists_orderOf_eq_three_gf16.choose_spec

theorem ω₁₆_ne_one : ω₁₆ ≠ 1 := by
  intro h
  have h3 := orderOf_ω₁₆
  rw [h, orderOf_one] at h3
  exact absurd h3 (by norm_num)

@[expose] noncomputable def Z₃ : Subgroup 𝕂ˣ := Subgroup.zpowers ω₁₆

theorem card_Z₃ : Nat.card Z₃ = 3 := by
  rw [Z₃, Nat.card_zpowers, orderOf_ω₁₆]

theorem fix_Z₃ : ∀ a ∈ Z₃, σ₁₆ (a : 𝕂) = a := by
  intro a ha
  have h3 : a ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_ω₁₆]
    exact orderOf_dvd_of_mem_zpowers ha
  have h3' : (a : 𝕂) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  rw [unitaryInvolution_apply]
  calc (a : 𝕂) ^ 2 ^ 2 = (a : 𝕂) ^ 3 * (a : 𝕂) := by ring
    _ = (a : 𝕂) := by rw [h3', one_mul]

@[expose] noncomputable def W₁₆ : WittData σ₁₆ := isUnitaryInvolution_gf16.nonempty_wittData.some

theorem projSU_eq_map_SUid (n : ℕ) :
    projSU n 2 2 = (SUid σ₁₆ n).map (ProjGenLinGroup.mk : GL (Fin n) 𝕂 →* _) := by
  rw [Sec4.projSU_eq_map_statedSU, SUid_eq_statedSU card_gf16 n]

@[expose] noncomputable def piSU (n : ℕ) : SUid σ₁₆ n →* projSU n 2 2 :=
  (MulEquiv.subgroupCongr (projSU_eq_map_SUid n).symm).toMonoidHom.comp
    ((ProjGenLinGroup.mk : GL (Fin n) 𝕂 →* _).subgroupMap (SUid σ₁₆ n))

theorem piSU_surjective (n : ℕ) : Function.Surjective (piSU n) :=
  (MulEquiv.subgroupCongr (projSU_eq_map_SUid n).symm).surjective.comp
    (MonoidHom.subgroupMap_surjective _ _)

theorem piSU_eq_one {n : ℕ} (g : SUid σ₁₆ n) (hg : piSU n g = 1) :
    ∃ c : 𝕂, ∀ v : Fin n → 𝕂, g • v = c • v := by
  have h1 : ProjGenLinGroup.mk (g : GL (Fin n) 𝕂) = 1 :=
    congrArg (fun x : projSU n 2 2 => (x : ProjGenLinGroup (Fin n) 𝕂)) hg
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨c, fun v => ?_⟩
  rw [smul_def, ← hc]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem finite_projSU_gf16 (n : ℕ) : Finite (projSU n 2 2) :=
  Finite.of_surjective _ (piSU_surjective n)

@[expose] noncomputable def P₀U (n : ℕ) (hn : 4 ≤ n) : Subgroup (projSU n 2 2) :=
  ((piSU n).comp (torusHom isUnitaryInvolution_gf16.invol (stdQuad W₁₆ hn) Z₃ fix_Z₃)).range

theorem card_P₀U {n : ℕ} (hn : 4 ≤ n) : Nat.card (P₀U n hn) = 9 := by
  rw [P₀U, MonoidHom.range_eq_map, Subgroup.card_map_of_injective
    (injective_comp_torusHom isUnitaryInvolution_gf16 two_eq_zero_gf16 _ fix_Z₃ (piSU n)
      piSU_eq_one), Subgroup.card_top, Nat.card_prod, card_Z₃]

theorem closure_P₀U {n : ℕ} (hn : 4 ≤ n) :
    Subgroup.closure {x : projSU n 2 2 | Nat.Coprime (orderOf x) 3 ∧
      ∃ p ∈ P₀U n hn, p ≠ 1 ∧ p * x = x * p} = ⊤ :=
  closure_coprime_eq_top isUnitaryInvolution_gf16 two_eq_zero_gf16 (stdQuad W₁₆ hn) fix_Z₃
    (piSU n) piSU_eq_one hn (Subgroup.mem_zpowers ω₁₆) ω₁₆_ne_one (piSU_surjective n)

end GF16

end UTools

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
