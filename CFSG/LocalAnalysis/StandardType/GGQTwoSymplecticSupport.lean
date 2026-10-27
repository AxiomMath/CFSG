module

public import CFSG.RankThree.PartOne.S11d.PSpComponent
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsDiag
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneFixed
public import CFSG.RankThree.PartOne.S11d.LayerDecomp
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Matrix CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.RankThree.Classical CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul)
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open WitSpNs

variable {K : Type} [Field K] {n : ℕ}

theorem fix_range_of_disjoint_support {S : Set (Fin n ⊕ Fin n)}
    {t g : StatedSp n K} (ht : t ∈ suppGroup Sᶜ) (hg : g ∈ suppGroup S) :
    ∀ w ∈ LinearMap.range (spEnd t - 1), spEnd g w = w := by
  intro w hw
  obtain ⟨v, rfl⟩ := hw
  change mat n K g *ᵥ ((spEnd t - 1) v) = (spEnd t - 1) v
  apply mulVec_eq_self_of_isSupp hg
  intro a ha
  change (spEnd t v) a - v a = 0
  rw [show spEnd t v = mat n K t *ᵥ v from rfl]
  have hrow : mat n K t a = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a := by
    funext b
    exact ht a b (fun h => h.1 ha)
  change mat n K t a ⬝ᵥ v - v a = 0
  rw [hrow]
  exact sub_eq_zero.mpr (congrFun (Matrix.one_mulVec v) a)

theorem conj_mem_fixedFactor_of_fix_range (a : StatedSp n K) {t g : StatedSp n K}
    (hc : g * t = t * g) (hW : ∀ w ∈ LinearMap.range (spEnd t - 1), spEnd g w = w) :
    a * g * a⁻¹ ∈ spFixedFactor (a * t * a⁻¹) := by
  apply mem_spFixedFactor_of_fix
  · calc (a * g * a⁻¹) * (a * t * a⁻¹) = a * (g * t) * a⁻¹ := by group
      _ = a * (t * g) * a⁻¹ := by rw [hc]
      _ = (a * t * a⁻¹) * (a * g * a⁻¹) := by group
  · intro w hw
    obtain ⟨v, hv⟩ := hw
    apply spEnd_injective' a⁻¹
    have hconj : spEnd a⁻¹ (spEnd (a * g * a⁻¹) w) = spEnd g (spEnd a⁻¹ w) := by
      rw [← Module.End.mul_apply, ← spEnd_mul,
        show a⁻¹ * (a * g * a⁻¹) = g * a⁻¹ by group, spEnd_mul, Module.End.mul_apply]
    have hw' : spEnd a⁻¹ w = (spEnd t - 1) (spEnd a⁻¹ v) := by
      rw [← hv, LinearMap.sub_apply, Module.End.one_apply, map_sub,
        ← Module.End.mul_apply, ← spEnd_mul,
        show a⁻¹ * (a * t * a⁻¹) = t * a⁻¹ by group, spEnd_mul, Module.End.mul_apply]
      rfl
    rw [hconj, hw']
    exact hW _ ⟨spEnd a⁻¹ v, rfl⟩

theorem conj_mem_fixedFactor_of_disjoint_support (a : StatedSp n K)
    {S : Set (Fin n ⊕ Fin n)} {t g : StatedSp n K}
    (ht : t ∈ suppGroup Sᶜ) (hg : g ∈ suppGroup S) :
    a * g * a⁻¹ ∈ spFixedFactor (a * t * a⁻¹) :=
  conj_mem_fixedFactor_of_fix_range a (commute_suppGroup_compl hg ht).eq
    (fix_range_of_disjoint_support ht hg)

theorem mem_suppGroup_compl_of_planeMat
    {t : StatedSp n K} {I : Finset (Fin n)}
    {P : Fin n → Matrix (Fin 2) (Fin 2) K} (ht : mat n K t = planeMat P)
    (hI : ∀ i ∈ I, P i = 1) : t ∈ suppGroup (planeCoords I)ᶜ := by
  change IsSupp (planeCoords I)ᶜ (mat n K t)
  rw [ht]
  intro a b hab
  have hab' : a ∈ planeCoords I ∨ b ∈ planeCoords I := by
    simpa only [Set.mem_compl_iff, not_and_or, not_not] using hab
  calc planeMat P a b = planeMat (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) a b := by
        rw [planeMat_apply, planeMat_apply]
        by_cases hp : plane a = plane b
        · have hb : plane b ∈ I := by
            rcases hab' with ha | hb
            · change plane a ∈ I at ha
              rwa [hp] at ha
            · exact hb
          rw [if_pos hp, if_pos hp, hI _ hb]
        · rw [if_neg hp, if_neg hp]
    _ = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a b :=
        congrFun (congrFun planeMat_one a) b

end CFSG.StandardType.QTwoSymplecticCav

end
