module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOn
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOrth
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryMaxBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal QuadraticMap Subgroup
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type} [Field K]

private theorem Xstar_singular (hr : 0 < r) : ∀ x ∈ Xstar r K hr, quadPlus r K x = 0 := by
  intro x hx
  rw [Xstar_eq_coordSpan, coordSpan] at hx
  refine map_eq_zero_of_mem_span (fun u hu => ?_) (fun u hu w hw => ?_) hx
  · obtain ⟨c, -, rfl⟩ := hu
    exact quadPlus_single c
  · obtain ⟨c, hc, rfl⟩ := hu
    obtain ⟨d, hd, rfl⟩ := hw
    refine polar_single_single fun hdc => ?_
    simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff] at hc hd
    rcases hc with ⟨j, hj, rfl⟩ | rfl <;> rcases hd with ⟨j', hj', rfl⟩ | rfl <;>
      simp [Fin.ext_iff] at hdc <;> omega

private theorem Xstar_ne_bot (hr : 0 < r) : Xstar r K hr ≠ ⊥ := by
  intro h
  have hmem : (Pi.single (Sum.inr (⟨r - 1, by omega⟩ : Fin r)) (1 : K) :
      Fin r ⊕ Fin r → K) ∈ Xstar r K hr :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  rw [h, Submodule.mem_bot] at hmem
  have := congrFun hmem (Sum.inr ⟨r - 1, by omega⟩)
  simp at this

private theorem flag_ne_bot {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ r) : flag r K i ≠ ⊥ := by
  intro h
  have := finrank_flag_of_le (K := K) hi2
  rw [h, finrank_bot] at this
  omega

private theorem borel_le_flagStab : borel r K ≤ flagStab r K := by
  intro g hg
  rw [mem_borel] at hg
  exact mem_flagStab.2 ⟨hg.1, fun i hi1 hi2 => hg.2 i hi1 (by omega)⟩

theorem ggNormalizerOvergroupsChar_projElementary_quadPlus [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : p ≠ 2) (hr : 4 ≤ r) :
    GGNormalizerOvergroupsChar p (ProjElementary (quadPlus r K)) := by
  obtain ⟨U, hUc⟩ := projUnip_isSylow (K := K) p (by omega : 3 ≤ r)
  refine ggNormalizerOvergroupsChar_projElementary p hp (quadPlus r K)
    (nondegenerate_polarBilin_quadPlus r K) ?_ (borel r K) (flagStab r K) borel_le_flagStab
    borel_le ?_ U ?_
  · rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  · intro M hMG hBM hne hmax
    rcases eq_stabilizer_of_isMax (by omega) hMG hBM hne hmax with ⟨i, hi1, hi2, h⟩ | h | h
    · exact ⟨flag r K i, ⟨flag_ne_bot hi1 (by omega), flag_singular i⟩, h⟩
    · exact ⟨Xstar r K (by omega), ⟨Xstar_ne_bot _, Xstar_singular _⟩, h⟩
    · exact ⟨flag r K r, ⟨flag_ne_bot (by omega) le_rfl, flag_singular r⟩, h⟩
  · rw [hUc]
    exact normalizer_projUnip (by omega)

theorem ggLieParabolicCharInputOn_D :
    GGLieParabolicCharInputOn fun d => ∃ r q, d.1 = .D r q := by
  rintro K _ _ d ⟨r, q, hm⟩ ⟨e⟩ hp2 S X hS hSi hNX hX
  have hp : d.1.characteristic = q.p := by
    rw [hm]
    exact TauCeti.LieTypeIndex.characteristic_D r q
  rw [hp] at hp2 hS hSi ⊢
  have hv : (TauCeti.LieTypeIndex.D r q).Valid := hm ▸ d.2
  obtain rfl : d = ⟨.D r q, hv⟩ := Subtype.ext hm
  obtain ⟨hadm, K', _, _, hcard, ⟨φ⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI := Fintype.ofFinite K'
  haveI : CharP K' q.p := charP_of_card_eq_prime_pow (f := q.exponent)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  have hr4 : 4 ≤ r := hadm.2.2
  let ψ : K ≃* ProjElementary (quadPlus r K') := φ.trans
    (statedProjEquiv (coe_quadPlus (n := r) (K := K'))
      (commutator_orthogonalGroup_quadPlus (by omega)))
  exact (GGNormalizerOvergroupsChar.of_mulEquiv ψ
    (ggNormalizerOvergroupsChar_projElementary_quadPlus q.p hp2 hr4)) S X hS hSi hNX hX

end CFSG.StandardType
