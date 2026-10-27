module

public import CFSG.RankThree.GF2n.Stroth80.Sec51Main
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9ROneOm
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10Sec
import CFSG.RankThree.GF2n.Stroth80.Sec7VanishGeomOm4
public import CFSG.CGT.Timmesfeld75.NormalClosure
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime
public import CFSG.RankThree.GF2n.Smith81.Sec220Defs
public import CFSG.RankThree.GF2n.Smith81.Sec220Local
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Dict
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Final
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9N5
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9ROneSL
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RSec4
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Schur
public import CFSG.RankThree.GF2n.Stroth80.Sec10Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClMain
public import CFSG.RankThree.GF2n.Stroth80.Sec311Torus
public import CFSG.RankThree.GF2n.Stroth80.Sec78SylowConj
public import CFSG.RankThree.GF2n.Stroth80.Sec9Chain
public import CFSG.RankThree.GF2n.Tim81.Components
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Timmesfeld.RankOne
import CFSG.CGT.A8S.N0EnumInputs
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.Main
import CFSG.CGT.Timmesfeld75.Sec5One
import CFSG.GH74.KGroups.L34Aut
import CFSG.LargeExtraspecial.S4Three
import CFSG.LargeExtraspecial.S4TwoA
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
import CFSG.RankThree.GF2n.Smith81.EStmt
import CFSG.RankThree.GF2n.Smith81.OrthE2Layer
import CFSG.RankThree.GF2n.Smith81.TiLane
import CFSG.RankThree.GF2n.Smith81.TiLemmaC
import CFSG.RankThree.GF2n.Stroth80.OppDecompSplit
import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec37Inputs
import CFSG.RankThree.GF2n.Stroth80.Sec4ClassicalFacts
import CFSG.RankThree.GF2n.Stroth80.Sec710Lemma61
import CFSG.RankThree.GF2n.Stroth80.Sec78Centre
import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
import CFSG.RankThree.GF2n.Stroth80.Sec78QB
import CFSG.RankThree.GF2n.Stroth80.Sec78ZtOmega
import CFSG.RankThree.GF2n.Stroth80.Sec79Split
import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial
import Certificates.Certificate10021
import Certificates.Certificate14982
import Certificates.Certificate14983
import Certificates.Certificate14984
import Certificates.Certificate14988
import Certificates.Certificate14989
import Certificates.Certificate21102
import Certificates.Certificate21190
import Certificates.Certificate21191
import Certificates.Certificate21192
import Certificates.Certificate21193
import Certificates.Certificate21194
import Certificates.Certificate21195
import Certificates.Certificate21196
import Certificates.Certificate21197
import Certificates.Certificate21198
import Certificates.Certificate21199
import Certificates.Certificate271010
import Certificates.Certificate271011
import Certificates.Certificate271015
import Certificates.Certificate271030
import Certificates.Certificate271031
import Certificates.Certificate271032
import Certificates.Certificate271033
import Certificates.Certificate5124
import Certificates.Certificate5150
import Certificates.Certificate5153

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace HS9

section OrthMatrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

theorem exists_perp_polar_one (hQ : (polarBilin Q').Nondegenerate) {u w : ι → K} (hu0 : u ≠ 0)
    (hw : ¬ ∃ μ : K, w = μ • u) : ∃ v : ι → K, polar Q' v u = 0 ∧ polar Q' v w = 1 := by
  classical
  have hnd : ∀ {x : ι → K}, (∀ y, polar Q' x y = 0) → x = 0 := fun {x} h =>
    hQ.1 x (fun y => by simpa [polarBilin_apply_apply] using h y)
  obtain ⟨v₁, hv₁⟩ : ∃ v₁, polar Q' v₁ u = 1 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∀ y, polar Q' u y = 0 := by
      intro y
      by_contra hy
      have hy' : polar Q' y u ≠ 0 := by rw [polar_comm Q' y u]; exact hy
      apply hcon ((polar Q' y u)⁻¹ • y)
      rw [polar_smul_left_eq]
      exact inv_mul_cancel₀ hy'
    exact hu0 (hnd h0)
  obtain ⟨v', hv'u, hv'w⟩ : ∃ v', polar Q' v' u = 0 ∧ polar Q' v' w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw
    refine ⟨polar Q' v₁ w, ?_⟩
    have h0 : ∀ y, polar Q' (w - polar Q' v₁ w • u) y = 0 := by
      intro y
      have h1 : polar Q' (y - polar Q' y u • v₁) u = 0 := by
        rw [polar_sub_left, polar_smul_left_eq, hv₁, mul_one, sub_self]
      have h2 := hcon _ h1
      rw [polar_sub_left, polar_smul_left_eq] at h2
      rw [polar_sub_left, polar_smul_left_eq, polar_comm Q' w y, polar_comm Q' u y]
      linear_combination h2
    exact sub_eq_zero.mp (hnd h0)
  refine ⟨(polar Q' v' w)⁻¹ • v', ?_, ?_⟩
  · rw [polar_smul_left_eq, hv'u, mul_zero]
  · rw [polar_smul_left_eq]
    exact inv_mul_cancel₀ hv'w

theorem eichler_smul_self {u : ι → K} (hu : Q' u = 0) (μ : K) : eichler Q' u (μ • u) = 1 := by
  have hw : polar Q' u (μ • u) = 0 := by
    rw [polar_smul_right_eq, polar_self_eq_zero hu, mul_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu hw]
  have hQ0 : Q' (μ • u) = 0 := by rw [QuadraticMap.map_smul, hu, smul_zero]
  rw [polar_smul_right_eq, hQ0, zero_mul, add_zero]
  show x + polar Q' x u • μ • u - (μ * polar Q' x u) • u = x
  module

theorem eichler_commute_form (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    {u : ι → K} (hu : Q' u = 0) (hu0 : u ≠ 0) {A₁ : Subgroup (GL ι K)} (hA₁ : A₁ ≤ E.LomGL u)
    {y : GL ι K} (hy : ∀ a ∈ A₁, a * y = y * a)
    (hyu : ∀ c : K, (y : Matrix ι ι K) *ᵥ u ≠ c • u) :
    ∀ a ∈ A₁, ∃ γ : K, ∀ v, (a : Matrix ι ι K) *ᵥ v =
      eichler Q' u (γ • ((y : Matrix ι ι K) *ᵥ u)) v := by
  classical
  intro a ha
  obtain ⟨-, w, hw, hav⟩ := (Om10.mem_LomGL_iff_eichler E).mp (hA₁ ha)
  by_cases hwu : ∃ μ : K, w = μ • u
  · obtain ⟨μ, rfl⟩ := hwu
    refine ⟨0, fun v => ?_⟩
    rw [hav v, eichler_smul_self hu μ, zero_smul, eichler_zero_right]
  · obtain ⟨v₀, hv₀u, hv₀w⟩ := exists_perp_polar_one hQ hu0 hwu
    have hcomm : ∀ v, (a : Matrix ι ι K) *ᵥ ((y : Matrix ι ι K) *ᵥ v) =
        (y : Matrix ι ι K) *ᵥ ((a : Matrix ι ι K) *ᵥ v) := by
      intro v
      have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) *ᵥ v) (hy a ha)
      simpa [Matrix.mulVec_mulVec] using this
    have h1 : (a : Matrix ι ι K) *ᵥ v₀ = v₀ - u := by
      rw [hav v₀, eichler_apply hu hw, hv₀u, hv₀w]
      simp
    obtain ⟨β, hβ⟩ : ∃ β : K, β = polar Q' ((y : Matrix ι ι K) *ᵥ v₀) u := ⟨_, rfl⟩
    obtain ⟨α, hα⟩ : ∃ α : K, α = polar Q' ((y : Matrix ι ι K) *ᵥ v₀) w + Q' w * β := ⟨_, rfl⟩
    have h2 : (y : Matrix ι ι K) *ᵥ u = (-β) • w + α • u := by
      have h3 := hcomm v₀
      rw [h1, Matrix.mulVec_sub, hav, eichler_apply hu hw, ← hβ, ← hα] at h3
      linear_combination (norm := module) h3
    have hβ0 : β ≠ 0 := by
      intro h0
      apply hyu α
      rw [h2, h0, neg_zero, zero_smul, zero_add]
    have hw' : w = (-β⁻¹) • ((y : Matrix ι ι K) *ᵥ u) + (β⁻¹ * α) • u := by
      rw [h2]
      have e : (-β⁻¹) • ((-β) • w + α • u) + (β⁻¹ * α) • u = ((-β⁻¹) * (-β)) • w := by module
      rw [e, neg_mul_neg, inv_mul_cancel₀ hβ0, one_smul]
    have hX : (-β⁻¹) • ((y : Matrix ι ι K) *ᵥ u) = w - (β⁻¹ * α) • u :=
      eq_sub_of_add_eq hw'.symm
    have hp1 : polar Q' u ((-β⁻¹) • ((y : Matrix ι ι K) *ᵥ u)) = 0 := by
      rw [hX, polar_sub_right, hw, polar_smul_right_eq, polar_self_eq_zero hu]
      ring
    have hp2 : polar Q' u ((β⁻¹ * α) • u) = 0 := by
      rw [polar_smul_right_eq, polar_self_eq_zero hu, mul_zero]
    refine ⟨-β⁻¹, fun v => ?_⟩
    calc (a : Matrix ι ι K) *ᵥ v = eichler Q' u w v := hav v
      _ = eichler Q' u ((-β⁻¹) • ((y : Matrix ι ι K) *ᵥ u) + (β⁻¹ * α) • u) v := by
          rw [← hw']
      _ = (eichler Q' u ((-β⁻¹) • ((y : Matrix ι ι K) *ᵥ u)) *
            eichler Q' u ((β⁻¹ * α) • u)) v := by rw [eichler_mul hp1 hp2]
      _ = eichler Q' u ((-β⁻¹) • ((y : Matrix ι ι K) *ᵥ u)) v := by
          rw [eichler_smul_self hu, mul_one]

theorem eq_of_mulVec_eq_gen {A B : Matrix ι ι K} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v

theorem card_le_of_eichler_commute [Finite K] (E : ElemMatrixIso Q' X)
    (hQ : (polarBilin Q').Nondegenerate) {u : ι → K} (hu : Q' u = 0) (hu0 : u ≠ 0)
    {A₁ : Subgroup (GL ι K)} (hA₁ : A₁ ≤ E.LomGL u) {y : GL ι K}
    (hy : ∀ a ∈ A₁, a * y = y * a) (hyu : ∀ c : K, (y : Matrix ι ι K) *ᵥ u ≠ c • u) :
    Nat.card A₁ ≤ Nat.card K := by
  classical
  have key := eichler_commute_form E hQ hu hu0 hA₁ hy hyu
  choose! γ hγ using key
  refine Nat.card_le_card_of_injective (fun a : ↥A₁ => γ (a : GL ι K)) ?_
  intro a b hab
  have hv : ∀ v, ((a : GL ι K) : Matrix ι ι K) *ᵥ v = ((b : GL ι K) : Matrix ι ι K) *ᵥ v := by
    intro v
    rw [hγ a a.2 v, hγ b b.2 v]
    have hab' : γ (a : GL ι K) = γ (b : GL ι K) := hab
    rw [hab']
  exact Subtype.ext (Units.ext (eq_of_mulVec_eq_gen hv))

theorem eq_one_of_witt (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    {u : ι → K} (hu : Q' u = 0) (hu0 : u ≠ 0) {A₁ : Subgroup (GL ι K)} (hA₁ : A₁ ≤ E.LomGL u)
    {y : GL ι K} (hyX : y ∈ X) (hy : ∀ a ∈ A₁, a * y = y * a)
    (hyu : ∀ c : K, (y : Matrix ι ι K) *ᵥ u ≠ c • u)
    (hW : ∀ F : (ι → K) →ₗ[K] (ι → K), (∀ w, Q' (F w) = Q' w) →
      (∀ w, Q' (F w - w) = 0) → ∀ w, F w = w) :
    ∀ a ∈ A₁, a = 1 := by
  classical
  intro a ha
  obtain ⟨γ, hγ⟩ := eichler_commute_form E hQ hu hu0 hA₁ hy hyu a ha
  have haX : (a : GL ι K) ∈ X := ((Om10.mem_LomGL_iff_eichler E).mp (hA₁ ha)).1
  have hyu0 : Q' ((y : Matrix ι ι K) *ᵥ u) = 0 := by rw [E.quad_mulVec hyX, hu]
  have hid : ∀ v, (a : Matrix ι ι K) *ᵥ v = v := by
    by_cases hp : polar Q' u (γ • ((y : Matrix ι ι K) *ᵥ u)) = 0
    · have hQw' : Q' (γ • ((y : Matrix ι ι K) *ᵥ u)) = 0 := by
        rw [QuadraticMap.map_smul, hyu0, smul_zero]
      have hsing : ∀ v, Q' ((a : Matrix ι ι K) *ᵥ v - v) = 0 := by
        intro v
        rw [hγ v, eichler_apply hu hp, hQw']
        have e : v + polar Q' v u • (γ • ((y : Matrix ι ι K) *ᵥ u)) -
            (polar Q' v (γ • ((y : Matrix ι ι K) *ᵥ u)) + 0 * polar Q' v u) • u - v =
            polar Q' v u • (γ • ((y : Matrix ι ι K) *ᵥ u)) +
              (-(polar Q' v (γ • ((y : Matrix ι ι K) *ᵥ u)))) • u := by module
        have hpw : polar Q' (γ • ((y : Matrix ι ι K) *ᵥ u)) u = 0 := by
          rw [polar_comm Q']
          exact hp
        rw [e, QuadraticMap.map_add Q']
        simp only [QuadraticMap.map_smul, hQw', hu, smul_zero, polar_smul_left_eq,
          polar_smul_right_eq, hpw, mul_zero, add_zero]
      intro v
      have := hW (Matrix.mulVecLin (a : Matrix ι ι K)) (fun w => by
        simpa using E.quad_mulVec haX w) (fun w => by simpa using hsing w) v
      simpa using this
    · intro v
      rw [hγ v, eichler_of_polar_ne_zero hp]
      rfl
  exact Units.ext (eq_of_mulVec_eq_gen fun v => by rw [hid v]; simp)

end OrthMatrix

section SpMatrix

open CFSG.ClassicalGroups.Symplectic

variable {m : ℕ} {K : Type} [Field K]

theorem exists_form_one {V : Type} [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V)
    (hrefl : ∀ x y, B x y = 0 → B y x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {u : V}
    (hu0 : u ≠ 0) : ∃ v, B v u = 1 := by
  by_contra hcon
  push Not at hcon
  have h0 : ∀ y, B u y = 0 := by
    intro y
    by_contra hy
    have hy' : B y u ≠ 0 := fun h => hy (hrefl y u h)
    apply hcon ((B y u)⁻¹ • y)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hy'
  exact hu0 (hnd u h0)

theorem exists_perp_form_one {V : Type} [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hrefl : ∀ x y, B x y = 0 → B y x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {u w : V} (hu0 : u ≠ 0)
    (hw : ¬ ∃ μ : K, w = μ • u) : ∃ v, B v u = 0 ∧ B v w = 1 := by
  obtain ⟨v₁, hv₁⟩ := exists_form_one B hrefl hnd hu0
  obtain ⟨v', hv'u, hv'w⟩ : ∃ v', B v' u = 0 ∧ B v' w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw
    refine ⟨B v₁ w, ?_⟩
    have h0 : ∀ y, B (w - B v₁ w • u) y = 0 := by
      intro y
      apply hrefl
      have h1 : B (y - B y u • v₁) u = 0 := by
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hv₁,
          mul_one, sub_self]
      have h2 := hcon _ h1
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h2 ⊢
      linear_combination h2
    exact sub_eq_zero.mp (hnd _ h0)
  refine ⟨(B v' w)⁻¹ • v', ?_, ?_⟩
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hv'u, mul_zero]
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hv'w

local notation "𝕄" => Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K

theorem siegel_commute_form [CharP K 2] {u : Fin m ⊕ Fin m → K} (hu0 : u ≠ 0)
    {A₁ : Subgroup (GL (Fin m ⊕ Fin m) K)} (hA₁ : A₁ ≤ LspGL m K u)
    {y : GL (Fin m ⊕ Fin m) K} (hyX : y ∈ StatedSp m K) (hy : ∀ a ∈ A₁, a * y = y * a)
    (hyu : ∀ c : K, (y : 𝕄) *ᵥ u ≠ c • u) :
    ∀ a ∈ A₁, ∃ γ : K, ∀ x, (a : 𝕄) *ᵥ x =
      x + spForm m K x u • (γ • ((y : 𝕄) *ᵥ u)) + spForm m K x (γ • ((y : 𝕄) *ᵥ u)) • u := by
  classical
  intro a ha
  obtain ⟨-, w, c, hw, hax⟩ := mem_LspGL_iff_siegel.mp (hA₁ ha)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h2u : (2 : K) • u = 0 := by rw [h2, zero_smul]
  have hB := (mem_statedSp_iff_forall y).mp hyX
  have hrefl : ∀ x z, spForm m K x z = 0 → spForm m K z x = 0 := by
    intro x z h
    rw [← spForm_isAlt.neg_eq, h, neg_zero]
  have hnd : ∀ x, (∀ z, spForm m K x z = 0) → x = 0 := fun x h => spForm_nondegenerate.1 x h
  have hcomm : ∀ v, (a : 𝕄) *ᵥ ((y : 𝕄) *ᵥ v) = (y : 𝕄) *ᵥ ((a : 𝕄) *ᵥ v) := by
    intro v
    have := congrArg (fun g : GL (Fin m ⊕ Fin m) K => (g : 𝕄) *ᵥ v) (hy a ha)
    simpa [Matrix.mulVec_mulVec] using this
  have indep : ∀ p q : K, p • ((y : 𝕄) *ᵥ u) + q • u = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    by_cases hp : p = 0
    · subst hp
      simp only [zero_smul, zero_add] at h
      exact ⟨rfl, (smul_eq_zero.mp h).resolve_right hu0⟩
    · exfalso
      apply hyu (-(p⁻¹ * q))
      have h' : p • ((y : 𝕄) *ᵥ u) = (-q) • u := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_left h
      calc (y : 𝕄) *ᵥ u = p⁻¹ • (p • ((y : 𝕄) *ᵥ u)) := by
            rw [smul_smul, inv_mul_cancel₀ hp, one_smul]
        _ = p⁻¹ • ((-q) • u) := by rw [h']
        _ = (-(p⁻¹ * q)) • u := by rw [smul_smul]; congr 1; ring
  by_cases hwu : ∃ μ : K, w = μ • u
  ·
    obtain ⟨μ, rfl⟩ := hwu
    have hax' : ∀ x, (a : 𝕄) *ᵥ x = x + (c * spForm m K x u) • u := by
      intro x
      rw [hax x]
      have e : x + spForm m K x u • μ • u + spForm m K x (μ • u) • u +
          (c * spForm m K x u) • u =
          x + (c * spForm m K x u) • u + (μ * spForm m K x u) • (2 : K) • u := by
        simp only [map_smul, smul_eq_mul]
        module
      rw [e, h2u, smul_zero, add_zero]
    obtain ⟨x₁, hx₁⟩ := exists_form_one (spForm m K) hrefl hnd hu0
    have hc0 : c = 0 := by
      by_contra hc
      have h3 := hcomm x₁
      rw [hax', hax', Matrix.mulVec_add, Matrix.mulVec_smul, hx₁] at h3
      apply hyu (spForm m K ((y : 𝕄) *ᵥ x₁) u)
      have h4 : (c * spForm m K ((y : 𝕄) *ᵥ x₁) u) • u = c • ((y : 𝕄) *ᵥ u) := by
        simp only [mul_one] at h3
        exact add_left_cancel h3
      have h5 : c • ((y : 𝕄) *ᵥ u) = c • (spForm m K ((y : 𝕄) *ᵥ x₁) u • u) := by
        rw [← h4, mul_smul]
      exact smul_right_injective _ hc h5
    refine ⟨0, fun x => ?_⟩
    rw [hax' x, hc0]
    simp
  ·
    obtain ⟨x₀, hx₀u, hx₀w⟩ := exists_perp_form_one (spForm m K) hrefl hnd hu0 hwu
    have hax0 : (a : 𝕄) *ᵥ x₀ = x₀ + u := by
      rw [hax x₀, hx₀u, hx₀w]
      simp
    obtain ⟨β, hβ⟩ : ∃ β : K, β = spForm m K ((y : 𝕄) *ᵥ x₀) u := ⟨_, rfl⟩
    have h3 : (y : 𝕄) *ᵥ u =
        β • w + (spForm m K ((y : 𝕄) *ᵥ x₀) w + c * β) • u := by
      have h := hcomm x₀
      rw [hax0, Matrix.mulVec_add, hax ((y : 𝕄) *ᵥ x₀), ← hβ] at h
      linear_combination (norm := module) (-1 : K) • h
    have hβ0 : β ≠ 0 := by
      intro h0
      apply hyu (spForm m K ((y : 𝕄) *ᵥ x₀) w + c * β)
      rw [h3, h0, zero_smul, zero_add]
    obtain ⟨μ, hμ⟩ : ∃ μ : K, μ = -(β⁻¹ * (spForm m K ((y : 𝕄) *ᵥ x₀) w + c * β)) := ⟨_, rfl⟩
    have hw' : w = β⁻¹ • ((y : 𝕄) *ᵥ u) + μ • u := by
      rw [h3, hμ]
      have e : β⁻¹ • (β • w + (spForm m K ((y : 𝕄) *ᵥ x₀) w + c * β) • u) +
          (-(β⁻¹ * (spForm m K ((y : 𝕄) *ᵥ x₀) w + c * β))) • u = (β⁻¹ * β) • w := by module
      rw [e, inv_mul_cancel₀ hβ0, one_smul]
    obtain ⟨x₂, hx₂u, hx₂y⟩ := exists_perp_form_one (spForm m K) hrefl hnd hu0
      (w := (y : 𝕄) *ᵥ u) (fun ⟨c', hc'⟩ => hyu c' hc')
    have hBw : spForm m K x₂ w = β⁻¹ := by
      rw [hw']
      simp only [map_add, map_smul, hx₂y, hx₂u, smul_eq_mul]
      ring
    have hax2 : (a : 𝕄) *ᵥ x₂ = x₂ + β⁻¹ • u := by
      rw [hax x₂, hx₂u, hBw]
      simp
    obtain ⟨β₂, hβ₂⟩ : ∃ β₂ : K, β₂ = spForm m K ((y : 𝕄) *ᵥ x₂) u := ⟨_, rfl⟩
    have hBy : spForm m K ((y : 𝕄) *ᵥ x₂) w = μ * β₂ := by
      rw [hw']
      simp only [map_add, map_smul, smul_eq_mul]
      rw [hB x₂ u, hx₂u, ← hβ₂]
      ring
    have h4 := hcomm x₂
    rw [hax2, Matrix.mulVec_add, Matrix.mulVec_smul, hax ((y : 𝕄) *ᵥ x₂), ← hβ₂, hBy, hw'] at h4
    have h5 : (β₂ * β⁻¹ - β⁻¹) • ((y : 𝕄) *ᵥ u) + (β₂ * μ + μ * β₂ + c * β₂) • u = 0 := by
      linear_combination (norm := module) h4
    obtain ⟨hp, hq⟩ := indep _ _ h5
    have hβ₂1 : β₂ = 1 := by
      have : β₂ * β⁻¹ = 1 * β⁻¹ := by linear_combination hp
      exact mul_right_cancel₀ (inv_ne_zero hβ0) this
    have hc0 : c = 0 := by
      rw [hβ₂1] at hq
      linear_combination hq - μ * h2
    refine ⟨β⁻¹, fun x => ?_⟩
    rw [hax x, hc0, hw']
    simp only [map_add, map_smul, smul_eq_mul]
    linear_combination (norm := module) (μ * spForm m K x u) • h2u

theorem card_le_of_siegel_commute [CharP K 2] [Finite K] {u : Fin m ⊕ Fin m → K} (hu0 : u ≠ 0)
    {A₁ : Subgroup (GL (Fin m ⊕ Fin m) K)} (hA₁ : A₁ ≤ LspGL m K u)
    {y : GL (Fin m ⊕ Fin m) K} (hyX : y ∈ StatedSp m K) (hy : ∀ a ∈ A₁, a * y = y * a)
    (hyu : ∀ c : K, (y : 𝕄) *ᵥ u ≠ c • u) : Nat.card A₁ ≤ Nat.card K := by
  classical
  have key := siegel_commute_form hu0 hA₁ hyX hy hyu
  choose! γ hγ using key
  refine Nat.card_le_card_of_injective (fun a : ↥A₁ => γ (a : GL (Fin m ⊕ Fin m) K)) ?_
  intro a b hab
  have hv : ∀ v, ((a : GL (Fin m ⊕ Fin m) K) : 𝕄) *ᵥ v =
      ((b : GL (Fin m ⊕ Fin m) K) : 𝕄) *ᵥ v := by
    intro v
    rw [hγ a a.2 v, hγ b b.2 v]
    have hab' : γ (a : GL (Fin m ⊕ Fin m) K) = γ (b : GL (Fin m ⊕ Fin m) K) := hab
    rw [hab']
  exact Subtype.ext (Units.ext (eq_of_mulVec_eq_gen hv))

end SpMatrix

section GroupLevel

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem not_Y_le_LB (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) : ¬ Y ≤ LB M Q B := by
  intro hYL
  obtain ⟨⟨hQX, hXR, hQY, hYRt, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  obtain ⟨hYQn, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := isSLModel_two_data hq4 hq2 hYmod
  have hQYidx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have h2 := h4.2.1
  rw [inf_eq_right.mpr hYL, hQYidx] at h2
  have h3 : Nat.card Z ^ 2 - 1 = 1 := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) ?_
    rw [h2, mul_one]
  have h16 : 16 ≤ Nat.card Z ^ 2 := by nlinarith
  omega

theorem LB_inf_CN_le_E (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {x : G}
    (hxL : x ∈ LB M Q B) (hxQ : x ∉ Q) (hYR : Y ≤ Rt M (LB M Q B) x) :
    LB M Q B ⊓ hc.CN x ≤ LB M Q B ⊓ X := by
  classical
  obtain ⟨⟨hQX, hXR, hQY, hYRt, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hQN : Q ≤ hc.CN x := hc.Q_le_CN hxL
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hLR : LB M Q B ≤ Rt M (LB M Q B) x := le_Rt (M := M) (LB M Q B) hxL
  have hYN : Y ⊓ hc.CN x ≤ Q := Y_inf_CN_le_Q h34 h311a hc hs hxL hxQ hQY hYR hYsl
  have hQE : Q ≤ LB M Q B ⊓ X := le_inf hQL hQX
  have hnormEY : (LB M Q B ⊓ X) ≤ Subgroup.normalizer ((LB M Q B ⊓ Y : Subgroup G) : Set G) :=
    normalizer_of_commutator_le (X := LB M Q B ⊓ Y) (Y := LB M Q B ⊓ X)
      (le_inf hQL hQY) fun a ha y hy => by
        have := Q.inv_mem (hcXY y hy.2 a ha.2)
        rwa [commutatorElement_inv] at this
  intro z hz
  have hLeq : z ∈ (LB M Q B ⊓ X) ⊔ (LB M Q B ⊓ Y) := h4.2.2 ▸ hz.1
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_normalizer hnormEY hLeq
  have haR : a ∈ Rt M (LB M Q B) x := hLR ha.1
  have hbQ : b ∈ Q := by
    refine mem_of_comm_mem_Q hq4 hq2 hYsl hb.2 fun y hy => ?_
    have hzy : ⁅z, y⁆ ∈ hc.CN x := by
      have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (hc.CN x).mul_mem hz.2
        (hc.CN_conj_mem hxL (hYR hy) ((hc.CN x).inv_mem hz.2))
    have h1 : a * ⁅b, y⁆ * a⁻¹ ∈ hc.CN x := by
      have e : a * ⁅b, y⁆ * a⁻¹ = ⁅z, y⁆ * ⁅a, y⁆⁻¹ := by
        rw [← hab]
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (hc.CN x).mul_mem hzy ((hc.CN x).inv_mem (hQN (hcXY a ha.2 y hy)))
    have h2 : ⁅b, y⁆ ∈ hc.CN x := by
      have := hc.CN_conj_mem hxL ((Rt M (LB M Q B) x).inv_mem haR) h1
      have e : a⁻¹ * (a * ⁅b, y⁆ * a⁻¹) * a⁻¹⁻¹ = ⁅b, y⁆ := by group
      rwa [e] at this
    have h3 : ⁅b, y⁆ ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem hb.2 hy) (Y.inv_mem hb.2)) (Y.inv_mem hy)
    exact hYN ⟨h3, h2⟩
  rw [← hab]
  exact (LB M Q B ⊓ X).mul_mem ha (hQE hbQ)

theorem commuting_data (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {x : G}
    (hxL : x ∈ LB M Q B) (hxQ : x ∉ Q) (hYR : Y ≤ Rt M (LB M Q B) x) {H : Type} [Group H]
    (φ : ↥(Rt M (LB M Q B) x) →* H)
    (hker : φ.ker = (hc.CN x).subgroupOf (Rt M (LB M Q B) x)) :
    ((LB M Q B ⊓ X).subgroupOf (Rt M (LB M Q B) x)).map φ ≤
        ((LB M Q B).subgroupOf (Rt M (LB M Q B) x)).map φ ∧
      Nat.card Z * Nat.card ↥(((LB M Q B ⊓ X).subgroupOf (Rt M (LB M Q B) x)).map φ) =
        Nat.card ↥(((LB M Q B).subgroupOf (Rt M (LB M Q B) x)).map φ) ∧
      ∀ (y : G) (hy : y ∈ Y), ∀ a ∈ ((LB M Q B ⊓ X).subgroupOf (Rt M (LB M Q B) x)).map φ,
        φ ⟨y, hYR hy⟩ * a = a * φ ⟨y, hYR hy⟩ := by
  classical
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYRt, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hQN : Q ≤ hc.CN x := hc.Q_le_CN hxL
  have hLR : LB M Q B ≤ Rt M (LB M Q B) x := le_Rt (M := M) (LB M Q B) hxL
  have hER : LB M Q B ⊓ X ≤ Rt M (LB M Q B) x := inf_le_left.trans hLR
  refine ⟨?_, ?_, ?_⟩
  · exact Subgroup.map_mono fun z hz =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).1
  · have h1 := card_inf_mul_card_map hLR φ hker
    have h2 := card_inf_mul_card_map hER φ hker
    have hEN : (LB M Q B ⊓ X) ⊓ hc.CN x = LB M Q B ⊓ hc.CN x :=
      le_antisymm (fun z hz => ⟨hz.1.1, hz.2⟩) (fun z hz =>
        ⟨LB_inf_CN_le_E h34 h311a hc hs hsplit0 h4 hxL hxQ hYR hz, hz.2⟩)
    rw [hEN] at h2
    have hLE : Nat.card Z * Nat.card ↥(LB M Q B ⊓ X) = Nat.card ↥(LB M Q B) := by
      have := Subgroup.relIndex_mul_card (H := LB M Q B ⊓ X) (K := LB M Q B)
      rw [inf_eq_left.mpr inf_le_left, relIndex_LB_inf_X hc hsplit0 h4] at this
      exact this
    have hpos : 0 < Nat.card ↥(LB M Q B ⊓ hc.CN x) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc Nat.card ↥(LB M Q B ⊓ hc.CN x) *
          (Nat.card Z * Nat.card ↥(((LB M Q B ⊓ X).subgroupOf (Rt M (LB M Q B) x)).map φ)) =
        Nat.card Z * (Nat.card ↥(LB M Q B ⊓ hc.CN x) *
          Nat.card ↥(((LB M Q B ⊓ X).subgroupOf (Rt M (LB M Q B) x)).map φ)) := by ring
      _ = Nat.card Z * Nat.card ↥(LB M Q B ⊓ X) := by rw [h2]
      _ = Nat.card ↥(LB M Q B) := hLE
      _ = _ := h1.symm
  · intro y hy a ha
    obtain ⟨e', he', rfl⟩ := ha
    have he'E : (e' : G) ∈ LB M Q B ⊓ X := Subgroup.mem_subgroupOf.mp he'
    have hcQ : ⁅(y : G), (e' : G)⁆ ∈ Q := by
      rw [← commutatorElement_inv]
      exact Q.inv_mem (hcXY _ he'E.2 y hy)
    have h3 : ⁅(⟨y, hYR hy⟩ : ↥(Rt M (LB M Q B) x)), e'⁆ ∈ φ.ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.mpr (hQN hcQ)
    rw [MonoidHom.mem_ker, map_commutatorElement] at h3
    exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem exists_moves_point (hc : Ctx M Q Z B) {t : G} {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {x : G}
    (hxL : x ∈ LB M Q B) (hYR : Y ≤ Rt M (LB M Q B) x) {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (φ : ↥(Rt M (LB M Q B) x) →* GL ι K)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z x)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z x) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z x) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) x)) (v w : ↥(Vt M (LB M Q B) B Z x)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {u : ι → K}
    (hBiff : ∀ z : ι → K, (∃ b : ↥(Vt M (LB M Q B) B Z x), (b : G) ∈ B ∧ secVec ψ b = z) ↔
      ∃ c : K, z = c • u) :
    ∃ (y : G) (hy : y ∈ Y), ∀ c : K, (φ ⟨y, hYR hy⟩ : Matrix ι ι K) *ᵥ u ≠ c • u := by
  classical
  by_contra hcon
  push Not at hcon
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYRt, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hBV : B ≤ Vt M (LB M Q B) B Z x := hc.B_le_Vt hxL
  have hVR := hc.Rt_normalizes_Vt hxL
  have hnormB : ∀ (y : G) (hy : y ∈ Y), conjSubgroup y B ≤ B ⊔ Z := by
    intro y hy z hz
    have hb₀B : y⁻¹ * z * y ∈ B := mem_conjSubgroup.mp hz
    have hb₀V : y⁻¹ * z * y ∈ Vt M (LB M Q B) B Z x := hBV hb₀B
    obtain ⟨c₀, hc₀⟩ := hcon y hy
    obtain ⟨c, hc⟩ := (hBiff _).mp ⟨⟨y⁻¹ * z * y, hb₀V⟩, hb₀B, rfl⟩
    have hzV : z ∈ Vt M (LB M Q B) B Z x := by
      have := (Subgroup.mem_normalizer_iff.mp (hVR (hYR hy)) (y⁻¹ * z * y)).mp hb₀V
      simpa [mul_assoc] using this
    have hsz := hψ ⟨y, hYR hy⟩ ⟨y⁻¹ * z * y, hb₀V⟩ ⟨z, hzV⟩ (by simp [mul_assoc])
    have hsv : secVec ψ ⟨z, hzV⟩ = (c * c₀) • u := by
      show Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨z, hzV⟩)) = _
      rw [hsz]
      have hc' : Multiplicative.toAdd (ψ (QuotientGroup.mk
          (⟨y⁻¹ * z * y, hb₀V⟩ : ↥(Vt M (LB M Q B) B Z x)))) = c • u := hc
      rw [hc', Matrix.mulVec_smul, hc₀, smul_smul]
    obtain ⟨b', hb'B, hb'⟩ := (hBiff ((c * c₀) • u)).mpr ⟨c * c₀, rfl⟩
    have hmem : z * (b' : G)⁻¹ ∈ Z := (secVec_eq_iff ψ ⟨z, hzV⟩ b').mp (hsv.trans hb'.symm)
    have h5 : z * (b' : G)⁻¹ * (b' : G) ∈ Z ⊔ B := Subgroup.mul_mem_sup hmem hb'B
    rw [inv_mul_cancel_right, sup_comm] at h5
    exact h5
  have hLconj : ∀ (y : G), y ∈ Y → conjSubgroup y (LB M Q B) = LB M Q B := fun y hy =>
    hc.conj_LB_eq_of_le_sup_Z (hc.Rt_le_M x (hYR hy)) (hnormB y hy)
  have hKnorm : ∀ y ∈ Y, ∀ k ∈ LB M Q B ⊓ Y, y * k * y⁻¹ ∈ LB M Q B ⊓ Y := by
    intro y hy k hk
    refine ⟨?_, Y.mul_mem (Y.mul_mem hy hk.2) (Y.inv_mem hy)⟩
    have h1 : y * k * y⁻¹ ∈ conjSubgroup y (LB M Q B) := by
      rw [mem_conjSubgroup, show y⁻¹ * (y * k * y⁻¹) * y = k by group]
      exact hk.1
    rwa [hLconj y hy] at h1
  obtain ⟨σ, hσ, hσQ⟩ := exists_mem_LB_inf_Y_not_mem hc h4
  have hY' := eq_of_normal_of_ne_Q (K := LB M Q B ⊓ Y) hq4 hq2 hYsl
    (le_inf (le_sup_left : Q ≤ LB M Q B) hQY) inf_le_right hKnorm (fun h => hσQ (h hσ))
  refine not_Y_le_LB hc hsplit0 h4 ?_
  intro z hz
  have : z ∈ LB M Q B ⊓ Y := by
    rw [hY']
    exact hz
  exact this.1

end GroupLevel

end HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem not_omegaPlusNat_of_three_le (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : HS9.Split95 M Q Z B t X Y) (h4 : HS9.Sec4Concl M Q Z B X Y) {x : G}
    (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q) {m : ℕ} (hm : 3 ≤ m) : ¬ OmegaPlusNat hc x m := by
  classical
  rintro ⟨K, fK, finK, hK, hnat⟩
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := hx.1
  have hsx : Sec5Hyp hc n x := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩
  have hYR : Y ≤ Rt M (LB M Q B) x := le_sup_right.trans (HS9.one_part_a hc hsplit h4 hxL hx.2)
  have hnatSO : SpNat hc x ∨ OmegaNat hc x := Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm, hnat⟩⟩
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hdim : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by omega
  obtain ⟨φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hnat
  obtain ⟨u, hQu, hu0, hBiff, -, hL, -⟩ := hc.omega_points_core h34 hRoot hsx hnatSO hK
    (ElemMatrixIso.plus hm) (nondegenerate_polarBilin_quadPlus m K) h3
    (addCommutantScalar_statedOmegaPlus hm) φ hφ hker ψ hψ
    (hc.natSingular_of h34 hRoot hsx hnatSO hK (ElemMatrixIso.plus hm)
      (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm)
      φ hφ hker ψ hψ)
  obtain ⟨hle, hcard, hcomm⟩ := HS9.commuting_data h34 h311a hc hs hsplit h4 hxL hxQ hYR φ hker
  obtain ⟨y, hyY, hyu⟩ := HS9.exists_moves_point hc hsplit h4 hxL hYR φ ψ hψ hBiff
  rw [hL] at hle hcard
  have hbound := HS9.card_le_of_eichler_commute (ElemMatrixIso.plus hm)
    (nondegenerate_polarBilin_quadPlus m K) hQu hu0 hle
    (fun a ha => (hcomm y hyY a ha).symm) hyu
  rw [(ElemMatrixIso.plus hm).card_LomGL (nondegenerate_polarBilin_quadPlus m K) hQu hu0, hdim,
    hK] at hcard
  rw [hK] at hbound
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have h5 : Nat.card Z ^ 4 ≤ Nat.card Z ^ (2 * m - 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : Nat.card Z * Nat.card ↥(((LB M Q B ⊓ X).subgroupOf (Rt M (LB M Q B) x)).map φ) ≤
      Nat.card Z * Nat.card Z := Nat.mul_le_mul_left _ hbound
  rw [hcard] at h6
  have hq2 : 16 ≤ Nat.card Z * Nat.card Z := by nlinarith
  have h7 : Nat.card Z ^ 4 = Nat.card Z * Nat.card Z * (Nat.card Z * Nat.card Z) := by ring
  have h8 := Nat.mul_le_mul_left (Nat.card Z * Nat.card Z) hq2
  have h9 : Nat.card Z * Nat.card Z * 16 ≤ Nat.card Z * Nat.card Z :=
    h8.trans (h7.symm.le.trans (h5.trans h6))
  generalize Nat.card Z * Nat.card Z = a at h9 hq2
  omega

theorem not_omegaMinusNat_of_two_le (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : HS9.Split95 M Q Z B t X Y) (h4 : HS9.Sec4Concl M Q Z B X Y) {x : G}
    (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q) {m : ℕ} (hm : 2 ≤ m) : ¬ OmegaMinusNat hc x m := by
  classical
  rintro ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := hx.1
  have hsx : Sec5Hyp hc n x := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩
  have hYR : Y ≤ Rt M (LB M Q B) x := le_sup_right.trans (HS9.one_part_a hc hsplit h4 hxL hx.2)
  have hnatSO : SpNat hc x ∨ OmegaNat hc x :=
    Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hdim : Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by omega
  obtain ⟨φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hnat
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  obtain ⟨u, hQu, hu0, hBiff, -, hL, -⟩ := hc.omega_points_core h34 hRoot hsx hnatSO hK
    (ElemMatrixIso.minus hm hirr) hQ h3 (addCommutantScalar_statedOmegaMinus hm hirr) φ hφ hker
    ψ hψ
    (hc.natSingular_of h34 hRoot hsx hnatSO hK (ElemMatrixIso.minus hm hirr) hQ h3
      (addCommutantScalar_statedOmegaMinus hm hirr) φ hφ hker ψ hψ)
  obtain ⟨hle, hcard, hcomm⟩ := HS9.commuting_data h34 h311a hc hs hsplit h4 hxL hxQ hYR φ hker
  obtain ⟨y, hyY, hyu⟩ := HS9.exists_moves_point hc hsplit h4 hxL hYR φ ψ hψ hBiff
  rw [hL] at hle hcard
  rw [(ElemMatrixIso.minus hm hirr).card_LomGL hQ hQu hu0, hdim, hK] at hcard
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  by_cases hm3 : 3 ≤ m
  · have hbound := HS9.card_le_of_eichler_commute (ElemMatrixIso.minus hm hirr) hQ hQu hu0 hle
      (fun a ha => (hcomm y hyY a ha).symm) hyu
    rw [hK] at hbound
    have h5 : Nat.card Z ^ 4 ≤ Nat.card Z ^ (2 * m - 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h6 : Nat.card Z * Nat.card ↥(((LB M Q B ⊓ X).subgroupOf (Rt M (LB M Q B) x)).map φ) ≤
        Nat.card Z * Nat.card Z := Nat.mul_le_mul_left _ hbound
    rw [hcard] at h6
    have hq2 : 16 ≤ Nat.card Z * Nat.card Z := by nlinarith
    have h7 : Nat.card Z ^ 4 = Nat.card Z * Nat.card Z * (Nat.card Z * Nat.card Z) := by ring
    have h8 := Nat.mul_le_mul_left (Nat.card Z * Nat.card Z) hq2
    have h9 : Nat.card Z * Nat.card Z * 16 ≤ Nat.card Z * Nat.card Z :=
      h8.trans (h7.symm.le.trans (h5.trans h6))
    generalize Nat.card Z * Nat.card Z = a at h9 hq2
    omega
  · have hm2 : m = 2 := by omega
    subst hm2
    have hyX : (φ ⟨y, hYR hyY⟩ : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) ∈
        StatedOmega (StatedQuadMinus 2 K b c) := hφ ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have htriv := HS9.eq_one_of_witt (ElemMatrixIso.minus hm hirr) hQ hQu hu0 hle hyX
      (fun a ha => (hcomm y hyY a ha).symm) hyu
      (fun F hiso hsing w => OmegaMinusFourGeom.eq_of_isometry_of_singular hirr F hiso hsing w)
    have hbot : ((LB M Q B ⊓ X).subgroupOf (Rt M (LB M Q B) x)).map φ = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr htriv
    rw [hbot, Subgroup.card_bot] at hcard
    have h22 : Nat.card Z ^ (2 * 2 - 2) = Nat.card Z * Nat.card Z := by
      rw [show 2 * 2 - 2 = 2 from rfl, pow_two]
    rw [h22] at hcard
    nlinarith

theorem not_spMNat_of_two_le (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h311a : Stroth311aStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {X Y : Subgroup G} (hsplit : HS9.Split95 M Q Z B t X Y) (h4 : HS9.Sec4Concl M Q Z B X Y) {x : G}
    (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q) {m : ℕ} (hm : 2 ≤ m) : ¬ SpMNat hc x m := by
  classical
  rintro ⟨K, fK, finK, hK, hnat⟩
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := hx.1
  have hsx : Sec5Hyp hc n x := ⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩
  have hYR : Y ≤ Rt M (LB M Q B) x := le_sup_right.trans (HS9.one_part_a hc hsplit h4 hxL hx.2)
  obtain ⟨φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hnat
  obtain ⟨u, hu0, hBiff, hL, -⟩ := hc.sp_points_core h34 hRoot hsx hK hm φ hφ hker ψ hψ
  obtain ⟨hle, hcard, hcomm⟩ := HS9.commuting_data h34 h311a hc hs hsplit h4 hxL hxQ hYR φ hker
  obtain ⟨y, hyY, hyu⟩ := HS9.exists_moves_point hc hsplit h4 hxL hYR φ ψ hψ hBiff
  rw [hL] at hle hcard
  have hyX : (φ ⟨y, hYR hyY⟩ : GL (Fin m ⊕ Fin m) K) ∈ StatedSp m K :=
    hφ ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hbound := HS9.card_le_of_siegel_commute hu0 hle hyX
    (fun a ha => (hcomm y hyY a ha).symm) hyu
  rw [CFSG.ClassicalGroups.Symplectic.card_LspGL hu0, hK] at hcard
  rw [hK] at hbound
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have h5 : Nat.card Z ^ 3 ≤ Nat.card Z ^ (2 * m - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : Nat.card Z * Nat.card ↥(((LB M Q B ⊓ X).subgroupOf (Rt M (LB M Q B) x)).map φ) ≤
      Nat.card Z * Nat.card Z := Nat.mul_le_mul_left _ hbound
  rw [hcard] at h6
  have hq2 : 16 ≤ Nat.card Z * Nat.card Z := by nlinarith
  have h7 : Nat.card Z ^ 3 = Nat.card Z * (Nat.card Z * Nat.card Z) := by ring
  have h8 := Nat.mul_le_mul_right (Nat.card Z * Nat.card Z) hq4
  have h9 : 4 * (Nat.card Z * Nat.card Z) ≤ Nat.card Z * Nat.card Z :=
    h8.trans (h7.symm.le.trans (h5.trans h6))
  generalize Nat.card Z * Nat.card Z = a at h9 hq2
  omega

theorem sec97OneTypesNoSL_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h311a : Stroth311aStatement) : Sec97OneTypesNoSL := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 x hx hxQ
  exact ⟨fun m hm => not_spMNat_of_two_le h34 hRoot h311a hc hs hsplit h4 hx hxQ hm,
    fun m hm => not_omegaPlusNat_of_three_le h34 hRoot h311a hc hs hsplit h4 hx hxQ hm,
    fun m hm => not_omegaMinusNat_of_two_le h34 hRoot h311a hc hs hsplit h4 hx hxQ hm⟩

end CFSG.RankThree.GF2n.Stroth80
