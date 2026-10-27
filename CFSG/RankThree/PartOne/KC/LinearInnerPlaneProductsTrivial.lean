module

public import Mathlib
public import CFSG.RankThree.PartOne.KC.LinearPlaneStatements
public import CFSG.RankThree.PartOne.KC.LinearPlaneCore
public import CFSG.RankThree.PartOne.KC.CentralizerOfInnerTrivial
public import CFSG.RankThree.PartOne.KC.PlaneProductsTrivialOfRigidity
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.LinearSplitInner
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCLinPlane

@[expose] def LinearNonsplitAllDimensionInnerPlaneLocalCoreCentralization : Prop :=
  ∀ (p ℓ f n : ℕ) (K : Type) [Field K], p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p → 1 ≤ f → 3 ≤ n →
    Nat.card K = ℓ ^ f → ¬ p ∣ ℓ ^ f - 1 →
    ∀ B : Subgroup (MulAut (projectiveSL n K)), innSL n K ≤ B →
    ∀ E : Subgroup (MulAut (projectiveSL n K)), E ≤ innSL n K → IsElementaryAbelian p E →
      Nat.card E = p ^ 2 →
      ∃ E₀ : Subgroup (SpecialLinearGroup (Fin n) K), IsElementaryAbelian p E₀ ∧
        Nat.card E₀ = p ^ 2 ∧ E₀.map (innerOfSL n K) = E ∧
        Set.InjOn (innerOfSL n K) (E₀ : Set (SpecialLinearGroup (Fin n) K)) ∧
        (∀ a ∈ E₀, a ≠ 1 →
          ∀ (hsq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))))
            (h : primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))),
            KCLinPlane.GoodBlock h →
            ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
                (B ⊓ Subgroup.centralizer {innerOfSL n K a}),
              ∀ g ∈ blockImage hsq h, s * conjAut n K g = conjAut n K g * s) ∧
        (∀ t ∈ E, t ≠ 1 →
          ⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}), E⁆ = ⊥)

theorem linear_nonsplit_inner_plane_products_trivial_of_CA
    (hCA : LinearNonsplitAllDimensionInnerPlaneLocalCoreCentralization) :
    LinearNonsplitInnerPlaneProductsTrivial := by
  intro p ℓ f n K _ hp hp3 hℓ hℓp hf hn3 hK hpq B hB E hE hEel hEcard
  obtain ⟨E₀, hE₀el, hE₀card, hE₀map, hinj, hblk, hcomm⟩ :=
    hCA p ℓ f n K hp hp3 hℓ hℓp hf hn3 hK hpq B hB E hE hEel hEcard
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hpK : (p : K) ≠ 0 := by
    intro h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp ((CharP.cast_eq_zero_iff K ℓ p).mp h0))
  have hpcard : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hdvd
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hdvd)).symm
  have hpq' : ¬ p ∣ Nat.card K - 1 := by rwa [hK]
  refine ⟨fun a haE ha1 => hcomm a haE ha1, ?_⟩
  let J : MulAut (projectiveSL n K) → Subgroup (MulAut (projectiveSL n K)) := fun a =>
    Subgroup.closure {y | ∃ (a₀ : SpecialLinearGroup (Fin n) K) (_ : a₀ ∈ E₀) (_ : a₀ ≠ 1)
      (_ : innerOfSL n K a₀ = a)
      (hsq : Squarefree (minpoly K (Matrix.toLin' (a₀ : Matrix (Fin n) (Fin n) K))))
      (h : primaryFactors (Matrix.toLin' (a₀ : Matrix (Fin n) (Fin n) K)))
      (_ : KCLinPlane.GoodBlock h) (g : GL (Fin n) K) (_ : g ∈ blockImage hsq h),
      y = conjAut n K g}
  have hJ : ∀ a ∈ E, a ≠ 1 →
      ∀ s ∈ inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}),
        ∀ j ∈ J a, s * j = j * s := by
    intro a haE ha1 s hs j hj
    have hle : J a ≤ Subgroup.centralizer ({s} : Set (MulAut (projectiveSL n K))) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨a₀, ha₀, ha₀1, rfl, hsq, h, hgood, g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hblk a₀ ha₀ ha₀1 hsq h hgood s hs g hg).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hj)).symm
  have hrigid : ∀ β : MulAut (projectiveSL n K), (∀ a ∈ E, β * a = a * β) →
      (∀ a ∈ E, a ≠ 1 → ∀ j ∈ J a, β * j = j * β) → β = 1 := by
    intro β _ hβJ
    let 𝒢 : Subgroup (SpecialLinearGroup (Fin n) K) :=
      (Subgroup.centralizer ({β} : Set (MulAut (projectiveSL n K)))).comap (innerOfSL n K)
    have h𝒢 : 𝒢 = ⊤ := by
      refine eq_top_of_good_blocks_le hp hp3 hpK hpcard hpq' E₀ hE₀card 𝒢 ?_
      intro a haE₀ ha1 hsq h hgood g hg
      obtain ⟨s, rfl⟩ := blockImage_le_range_toGL_of_good hsq h hgood hg
      refine ⟨s, ?_, rfl⟩
      have haE : innerOfSL n K a ∈ E := hE₀map ▸ Subgroup.mem_map_of_mem _ haE₀
      have ha1' : innerOfSL n K a ≠ 1 := by
        intro h1
        exact ha1 (hinj haE₀ E₀.one_mem (by rw [h1, map_one]))
      have h1 := hβJ (innerOfSL n K a) haE ha1' (conjAut n K (SpecialLinearGroup.toGL s))
        (Subgroup.subset_closure ⟨a, haE₀, ha1, rfl, hsq, h, hgood, _, hg, rfl⟩)
      show innerOfSL n K s ∈ Subgroup.centralizer ({β} : Set (MulAut (projectiveSL n K)))
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [conjAut_toGL] at h1
      exact h1.symm
    refine mulAut_eq_one_of_commute_conj_of_surjective
      (CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := K) hn3) (proj n K)
      (proj_surjective n K) (S := Set.univ) ?_ ?_
    · exact Subgroup.closure_univ
    · intro g _
      have hg : g ∈ 𝒢 := h𝒢 ▸ Subgroup.mem_top g
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hg
      exact hg.symm
  exact KCGeneric.plane_products_trivial_of_rigidity B E J hcomm hJ hrigid

end CFSG.RankThree.PartOne
