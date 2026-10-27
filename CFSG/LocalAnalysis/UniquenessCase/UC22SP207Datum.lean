module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
public import CFSG.LieType.Steinberg.BruhatWeyl
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Tits
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Coxeter
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.SteinbergBNPair
import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GH74.BNPair (cartan WeylGroup wordLength)
open CFSG.GroupTheory.TitsSystem (IsBNPair)
open CFSG.ASVolI.ChIJK (IsSplitBNPair burnsideI2BN_of_datum)
open CFSG.AGLEmbeddingD2.McLaughlin.Lie (simpleRefl isBNPair_borel_weylN
  cartan_borel_weylN_normal)
open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.GH74.GLS.SP

private theorem uc22sp207_hasCentralLongest_of_weylEquiv {X : Type} [Group X] {B N : Subgroup X}
    [(cartan B N).Normal] (hBN : IsSplitBNPair 2 B N) {S : Set (WeylGroup B N)}
    (h : IsBNPair B N S) {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W]
    (cs : CoxeterSystem M W) (e : WeylGroup B N ≃* W) (hSe : e '' S = Set.range cs.simple)
    {z : W} (hzmax : ∀ w, cs.length w ≤ cs.length z) (hzc : ∀ w, z * w = w * z) :
    HasCentralLongest X := by
  obtain ⟨n₀, hn₀⟩ := QuotientGroup.mk_surjective (e.symm z)
  have hlen : ∀ w, wordLength S w = cs.length (e w) := fun w => by
    rw [← uc22sp207_wordLength_range_simple, ← hSe, uc22sp207_wordLength_map]
  refine uc22sp207_hasCentralLongest_of_isBNPair hBN h (n₀ := n₀) (fun w => ?_) (fun w => ?_)
  · rw [hlen, hlen, hn₀, MulEquiv.apply_symm_apply]
    exact hzmax _
  · apply e.injective
    rw [map_mul, map_mul, hn₀, MulEquiv.apply_symm_apply, hzc]

theorem uc22sp207_hasCentralLongest_of_datum {K : Type} [Group K] [Finite K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBE : BruhatExtras D H)
    (hU : IsPGroup 2 (posUnipotent D)) (hT : ¬ 2 ∣ Nat.card (⨆ i, H i : Subgroup K))
    (hz : ∃ z : (coxeterMatrix D.isFiniteType).Group,
      (∀ w, (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w ≤
        (coxeterMatrix D.isFiniteType).toCoxeterSystem.length z) ∧ ∀ w, z * w = w * z) :
    HasCentralLongest K := by
  have := cartan_borel_weylN_normal hct hext
  obtain ⟨z, hzmax, hzc⟩ := hz
  refine uc22sp207_hasCentralLongest_of_weylEquiv
    (burnsideI2BN_of_datum Nat.prime_two hct hext hBE hU hT) (isBNPair_borel_weylN hct hext)
    _ (weylEquiv hct hext) ?_ hzmax hzc
  rw [simpleRefl, ← Set.range_comp]
  exact congrArg Set.range (funext fun i => weylEquiv_n hct hext i)

end CFSG.LocalAnalysis.UniquenessCase.UC22
