module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Framework
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocal
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Fitting
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalAlmostSimple

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def FieldClauses (p : ℕ) (X : Type*) [Group X] : Prop :=
  (∃ f : MulAut X, orderOf f = p) →
    ∃ f₀ : MulAut X, orderOf f₀ = p ∧ FixedClauses p (signalizerFixedSubgroup f₀)

theorem FixedClauses.of_mulEquiv {p : ℕ} {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (f : MulAut Y) (h : FixedClauses p (signalizerFixedSubgroup (MulAut.congr e.symm f))) :
    FixedClauses p (signalizerFixedSubgroup f) :=
  ⟨TransportA.not_le_normalizer_of_congr e f h.1, TransportA.fitting_clause_of_congr e f h.2.1,
    TransportA.eq_one_of_congr e f h.2.2⟩

theorem FieldClauses.of_mulEquiv {p : ℕ} {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : FieldClauses p X) : FieldClauses p Y := by
  rintro ⟨f, hf⟩
  have hf' : orderOf (MulAut.congr e.symm f) = p := by
    rw [MulEquiv.orderOf_eq]; exact hf
  obtain ⟨f₀, hf₀, hcl⟩ := h ⟨MulAut.congr e.symm f, hf'⟩
  refine ⟨MulAut.congr e f₀, by rw [MulEquiv.orderOf_eq]; exact hf₀, ?_⟩
  refine FixedClauses.of_mulEquiv e _ ?_
  have : MulAut.congr e.symm (MulAut.congr e f₀) = f₀ := by
    ext x
    simp [MulAut.congr_apply]
  rw [this]
  exact hcl

theorem hypothesisA_of_near_or_fieldClauses {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (hsimple : IsSimpleGroup X) (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hcop : Nat.Coprime p (Nat.card X)) (hcyc : PSubgroupsCyclic p X)
    (h : signalizerNearPSolvable p X ∨ FieldClauses p X) : signalizerMcBrideHypothesisA p X := by
  rcases h with hnear | hfield
  · exact ⟨hp, hsimple, hnonab, hcop, hcyc, Or.inl hnear⟩
  · exact hypothesisA_of_fixedClauses hp hsimple hnonab hcop hcyc hfield

@[expose] def FStarSimple {X : Type*} [Group X] (C : Subgroup X) : Prop :=
  IsSimpleGroup (signalizerGeneralizedFitting C) ∧
    ∃ a b : signalizerGeneralizedFitting C, a * b ≠ b * a

theorem fStarSimple_of_simple {X : Type*} [Group X] {C : Subgroup X} (hs : IsSimpleGroup C)
    (hn : ∃ a b : C, a * b ≠ b * a) : FStarSimple C := by
  have hnc : ¬ IsMulCommutative C := by
    rw [isMulCommutative_iff]
    push Not
    exact hn
  have hF := McBride.Nonsolv.L514.isFStarSimple_of_isSimpleGroup hnc
  rw [McBride.Nonsolv.L514.IsFStarSimple, ← McBride.Nonsolv.L514.signalizerGeneralizedFitting_eq]
    at hF
  refine ⟨hF.1, ?_⟩
  have := hF.2
  rw [isMulCommutative_iff] at this
  push Not at this
  exact this

theorem fStarSimple_iff_isFStarSimple {X : Type*} [Group X] (C : Subgroup X) :
    FStarSimple C ↔ McBride.Nonsolv.L514.IsFStarSimple ↥C := by
  rw [McBride.Nonsolv.L514.IsFStarSimple, ← McBride.Nonsolv.L514.signalizerGeneralizedFitting_eq,
    FStarSimple, isMulCommutative_iff]
  push Not
  rfl

theorem isFStarSimple_of_simple_normal {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] [IsSimpleGroup N] (hN : ∃ a b : N, a * b ≠ b * a)
    (hC : Subgroup.centralizer (N : Set G) = ⊥) : McBride.Nonsolv.L514.IsFStarSimple G := by
  let φ : G →* MulAut N := MulAut.conjNormal
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : G)) hg
      simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc n * g = g * n * g⁻¹ * g := by rw [h1]
        _ = g * n := by group
    rw [hC, Subgroup.mem_bot] at hgC
    exact hgC
  have : Finite (MulAut N) :=
    Finite.of_injective (fun f : MulAut N => (f : N → N)) fun f g h => MulEquiv.ext (congrFun h)
  let B : Subgroup (MulAut N) := φ.range
  have hB : (MulAut.conj : N →* MulAut N).range ≤ B := by
    rintro _ ⟨n, rfl⟩
    refine ⟨(n : G), ?_⟩
    ext x
    simp [φ, MulAut.conjNormal_apply, MulAut.conj_apply]
  obtain ⟨-, -, -, hF, ⟨e⟩⟩ :=
    ComponentClassification.SmallLocal.almost_simple_inner_generalized_fitting hN B hB
  have hFB : McBride.Nonsolv.L514.IsFStarSimple ↥B := by
    refine ⟨?_, ?_⟩
    · rw [hF]
      exact e.isSimpleGroup
    · rw [hF, isMulCommutative_iff]
      push Not
      obtain ⟨a, b, hab⟩ := hN
      exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  exact (McBride.Nonsolv.L514.isFStarSimple_congr (MonoidHom.ofInjective hφ)).mpr hFB

theorem fixedClauses_of_stabilizer {p : ℕ} {X : Type*} [Group X] {f₀ : MulAut X}
    (hf₀ : orderOf f₀ = p) (hF : FStarSimple (signalizerFixedSubgroup f₀))
    (hNL : FStarSimple (signalizerFixedSubgroup f₀) → NonLocalized (signalizerFixedSubgroup f₀))
    (hstab : ∀ g : MulAut X, (∀ x ∈ signalizerFixedSubgroup f₀, g x = x) →
      g ∈ Subgroup.zpowers f₀) :
    FixedClauses p (signalizerFixedSubgroup f₀) := by
  refine ⟨hNL hF, hF, ?_⟩
  intro g hg hfix
  have hmem := hstab g hfix
  have hdvd : orderOf g ∣ p := by
    rw [← hf₀]
    exact orderOf_dvd_of_mem_zpowers hmem
  have h1 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd hg.symm hdvd
  exact orderOf_eq_one_iff.mp h1

end CFSG.SignalizerFunctorTheorem.CatalogBridge
