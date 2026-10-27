module

public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneProducts
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneFullCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryMultiplicity
public import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalEndpointStatements

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.RankThree.Classical2
  CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.PartOne.KCOrthogonalModel
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.GroupTheory

section Endpoint

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem liftMultiplicitiesCoprime_of_lift (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hpl : p ≠ ringChar K) {T : Type*} [Group T] (ξ : T ≃* ProjOrthDerived Q)
    (hmult : OrthogonalLiftMultiplicity p Q ξ) (A : Subgroup (MulAut T)) (hA : A ≤ inner T) :
    LiftMultiplicitiesCoprime p Q (A.map (MulAut.congr ξ).toMonoidHom) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := center_projOrthDerived_eq_bot hQ hT
  have hinj : Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_trivial_center hcenter
  intro x hxp hxA hx1 h hh hne
  obtain ⟨b, hbA, hb⟩ := hxA
  obtain ⟨t₀, rfl⟩ : b ∈ (MulAut.conj : T →* MulAut T).range := hA hbA
  have hξt : ξ t₀ = QuotientGroup.mk x := by
    apply hinj
    exact (congr_conj ξ t₀).symm.trans hb
  have hmkx : (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
  have hmkxp : orderOf (QuotientGroup.mk x : ProjOrthDerived Q) = p := by
    refine orderOf_eq_prime ?_ hmkx
    rw [← QuotientGroup.mk_pow, ← hxp, pow_orderOf_eq_one]
    rfl
  have hord : orderOf t₀ = p := by
    rw [← MulEquiv.orderOf_eq ξ, hξt, hmkxp]
  obtain ⟨-, -, hmp, -⟩ := (hmult t₀ hord).2 x hξt.symm hxp h hh hne
  intro hdvd
  have hsq := (oddOrderIsometry_of_orthDerived hp hpl hQ x hxp).squarefree_minpoly
  have hpos : 0 < primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h := by
    have hne' := primaryComponent_ne_bot hsq hh
    have : Nontrivial ↥(primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne'
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    exact Module.finrank_pos
  have := Nat.le_of_dvd hpos hdvd
  omega

theorem orthogonal_inner_actual_component_of_intrinsic {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hrank : localRank p G ≤ 3) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (htE : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpl : p ≠ ringChar K)
    (ξ : L ⧸ Subgroup.center L ≃* ProjOrthDerived Q)
    (hfull : CommonLayerCentralizerTrivial (ProjOrthDerived Q) p) :
    ComponentLocalCoreNormalizes p E t L ∧
      ((E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
          actualPlane L E ≤
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G)) := by
  have hp2 : p ≠ 2 := by omega
  have hmult : OrthogonalLiftMultiplicity p Q ξ :=
    orthogonalLiftMultiplicity_of_cover L hQ hT hp hp3 hpl hrank
      (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']) ξ
  have hint := orthogonal_inner_plane_planeLocalCoreInner hQ hT hp hp3 hpl hfull
  have hplaneL := PlaneLocalCoreInner.of_mulEquiv hp ξ hint
  have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t htE ht1
  have hWN : localCoreProduct p E t ≤ Subgroup.normalizer (L : Set G) := by
    refine sup_le (commutator_le_normalizer_of_le hSL hEL) ?_
    exact (iInf_le_of_le t (iInf_le_of_le htE (iInf_le _ ht1))).trans hSL
  refine ⟨⟨hset, hWN⟩, fun hinn => ?_⟩
  have hP : E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
      (LiftMultiplicitiesCoprime p Q ((actualPlane L E).map (MulAut.congr ξ).toMonoidHom) ∧
        actualPlane L E ≤
          (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) := by
    rcases hinn with h1 | h2
    · exact Or.inl h1
    · exact Or.inr ⟨liftMultiplicitiesCoprime_of_lift hQ hT hp hpl ξ hmult _ h2, h2⟩
  exact (component_local_core_centralizes_of_inner_plane hp hp2 hE hEcard htE ht1 hL hEL hSL
    hplaneL hP).2.2

theorem orthogonal_actual_rank_inner_plane_local_core_product_centralizes :
    OrthogonalActualRankInnerPlaneLocalCoreProductCentralizes := by
  intro G _ _ p ℓ f n hp hp3 hrank hℓp c hc E hE hEcard t htE ht1 L hL hmod hEL hSL
  have hpℓ : p ≠ ℓ := fun h => hℓp h.symm
  have hfullG := orthogonal_inner_plane_local_components_full_automorphism_centralizer
    (L ⧸ Subgroup.center L) c hc n ℓ f p hmod hp hp3 hpℓ
  have hmod' := hmod
  rcases hc with rfl | rfl | rfl
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    obtain ⟨hchar, hnd, hS3, -⟩ := coordinate_model_witness_odd hmod' K hK e
    have hpl : p ≠ ringChar K := by rw [hchar]; exact hpℓ
    exact orthogonal_inner_actual_component_of_intrinsic hp hp3 hrank hE hEcard htE ht1 hL hEL hSL
      hnd hS3 hpl ((coordinateOddWitnessEquiv K e).trans
        (bridgeEquiv (coordinateQuadOdd n K) (by omega)))
      (CommonLayerCentralizerTrivial.of_mulEquiv (bridgeEquiv (coordinateQuadOdd n K) (by omega))
        (hfullG K hK e))
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    obtain ⟨hchar, hnd, hS3, -⟩ := coordinate_model_witness_plus hmod' K hK e
    have hpl : p ≠ ringChar K := by rw [hchar]; exact hpℓ
    have hn : 1 ≤ n := by
      have := hmod'.1.2.2
      omega
    exact orthogonal_inner_actual_component_of_intrinsic hp hp3 hrank hE hEcard htE ht1 hL hEL hSL
      hnd hS3 hpl ((coordinatePlusWitnessEquiv K e).trans
        (bridgeEquiv (coordinateQuadPlus n K) (by omega)))
      (CommonLayerCentralizerTrivial.of_mulEquiv (bridgeEquiv (coordinateQuadPlus n K) (by omega))
        (hfullG K hK e))
  ·
    have hn : 1 ≤ n := by
      have := hmod'.1.2.2
      omega
    obtain ⟨-, K, _, _, hK, b, c', hirr, ⟨e⟩⟩ := hmod
    obtain ⟨hchar, hnd, hS3, -⟩ := coordinate_model_witness_minus hmod' K hK b c' hirr e
    have hpl : p ≠ ringChar K := by rw [hchar]; exact hpℓ
    exact orthogonal_inner_actual_component_of_intrinsic hp hp3 hrank hE hEcard htE ht1 hL hEL hSL
      hnd hS3 hpl ((coordinateMinusWitnessEquiv K hn b c' e).trans
        (bridgeEquiv (coordinateQuadMinus n K hn b c') (by omega)))
      (CommonLayerCentralizerTrivial.of_mulEquiv
        (bridgeEquiv (coordinateQuadMinus n K hn b c') (by omega)) (hfullG hn K hK b c' hirr e))

end Endpoint

end CFSG.RankThree.PartOne
