module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Frame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwCent
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwLat
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwLatSub
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootRefl
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootJ
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootC
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveLang

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups

section AtFrame


private theorem ggKGTd_Y_injective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) :
    Function.Injective (ggKGTwY F) := by
  intro x y h
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  have h3 : F.g0 * ggKGTwY F x * F.g0⁻¹ = F.g0 * ggKGTwY F y * F.g0⁻¹ := by
    rw [h]
  rw [ggKGTwY_apply, ggKGTwY_apply] at h3
  calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K)
      = F.g0 * (F.g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          F.g0) * F.g0⁻¹ := by group
    _ = F.g0 * (F.g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
          F.g0) * F.g0⁻¹ := h3
    _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) := by group

private theorem ggKGTd_mem_centralizer_iff
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    {γ : Fin Tag.E6.rank → ℤ}
    {w : twistedE6RootGroup K σ} (F : TwE6Frame K σ n p E)
    (hwγ : ggKGTwY F w =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ))
    (e : twistedE6RootGroup K σ) :
    e ∈ Subgroup.centralizer ({w} : Set (twistedE6RootGroup K σ)) ↔
      ggKGTwY F e ∈ Subgroup.centralizer
        ({canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ)} :
          Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← hwγ, ← map_mul, ← map_mul, h]
  · intro h
    apply ggKGTd_Y_injective F
    rw [map_mul, map_mul, hwγ]
    exact h

private theorem ggKGTd_isQuasisimple_assembly
    {Q : Type*} [Group Q]
    (h : CFSG.IsQuasisimple Q) : CFSG.Assembly.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem ggKGTd_inf_centralizer_eq_hyp
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    {γ : Fin Tag.E6.rank → ℤ}
    {w : twistedE6RootGroup K σ} (F : TwE6Frame K σ n p E)
    (hwγ : ggKGTwY F w =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ)) :
    E ⊓ Subgroup.centralizer ({w} : Set (twistedE6RootGroup K σ)) = ggKGTwHyp F γ := by
  ext e
  unfold ggKGTwHyp
  simp only [Subgroup.mem_inf, Subgroup.mem_comap]
  constructor
  · rintro ⟨he, hc⟩
    exact ⟨he, (ggKGTd_mem_centralizer_iff F hwγ e).mp hc⟩
  · rintro ⟨he, hc⟩
    exact ⟨he, (ggKGTd_mem_centralizer_iff F hwγ e).mpr hc⟩

theorem ggKGTwE6_latticeAt
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E)
    (hv : (p ∣ 2 ^ n - 1 ∧ F.v = 1) ∨ (p ∣ 2 ^ n + 1 ∧ ExcIsLongest TwistTag.E6.tag F.v)) :
    GGKGLatticeAt p E := by
  rcases hv with ⟨hpq, hv1⟩ | ⟨hpq, hlong⟩
  · exact ggKGTwE6_latticeAt_sub hK hσ hp hp5 hpq F hv1
  · exact ggKGTwE6_latticeAt_add hK hσ hp hp5 hpq F hlong

theorem ggKGTwE6_rootDatumAt
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) : GGKGRootDatumAt p E := by
  intro w₀ hrefl
  obtain ⟨γ, hγ, hγeq⟩ := ggKGTwE6_reflection_isRoot hK hσ hp hp5 hpq F hv hrefl
  obtain ⟨w, hwJ, hwγ⟩ := ggKGTwJ_weyl hK hσ F hv hγ
  have h4 : 4 ≤ 2 ^ n := by
    have hle : p ≤ 2 ^ n + 1 := Nat.le_of_dvd (by positivity) hpq
    omega
  have hinf : E ⊓ Subgroup.centralizer ({w} : Set (twistedE6RootGroup K σ)) =
      ggKGTwHyp F γ :=
    ggKGTd_inf_centralizer_eq_hyp F hwγ
  refine ⟨w, ?_, ggKGTwJ F γ, hwJ, ?_, ?_, ?_⟩
  · intro e he
    have hleft : ggKGTwY F (w * e * w⁻¹) =
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ) *
          ggKGTwY F e *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
            (rootReflection γ))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hwγ]
    have hright : ggKGTwY F (w₀ * e * w₀⁻¹) =
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ) *
          ggKGTwY F e *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
            (rootReflection γ))⁻¹ := by
      rw [ggKGTwY_apply, ggKGTwY_apply]
      exact hγeq e he
    exact ggKGTd_Y_injective F (hleft.trans hright.symm)
  · rw [hinf]
    exact ⟨ggKGTwJ_le_centralizer hp hp5 F hγ,
      ggKGTwJ_subnormal hK hσ hp hp5 hpq F hv hγ,
      ggKGTd_isQuasisimple_assembly (ggKGTwJ_quasisimple hK hσ F hv hγ h4)⟩
  · exact ggKGTwJ_dvd_card hK hσ F hv hγ hpq
  · intro a ha haw
    apply ggKGTwJ_layer hK hσ hp hp5 F hv hγ h4
    rw [← hinf]
    exact ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr haw.symm⟩

end AtFrame

theorem ggKGTwE6_latticeElt
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p r₀ : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) (h : TwE6SCTorusInput K σ n p r₀) :
    GGKGLatticeElt p r₀ (twistedE6RootGroup K σ) := by
  intro E hE h3 hr hsc
  obtain ⟨F, h1, h2⟩ := h E hE h3 hr hsc
  exact ggKGTwE6_latticeAt hK hσ hp hp5 F (hpq.imp (fun h => ⟨h, h1 h⟩) fun h => ⟨h, h2 h⟩)

theorem ggKGTwE6_rootDatum
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p r₀ : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n + 1) (h : TwE6SCTorusInput K σ n p r₀) :
    GGKGRootDatum p r₀ (twistedE6RootGroup K σ) := by
  intro E hE h3 hr hsc
  obtain ⟨F, -, h2⟩ := h E hE h3 hr hsc
  exact ggKGTwE6_rootDatumAt hK hσ hp hp5 hpq F (h2 hpq)

end CFSG.StandardType
