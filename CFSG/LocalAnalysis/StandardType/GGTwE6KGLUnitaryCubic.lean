module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLUnitaryCubicLabel
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedUnitary
import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem odd_of_three_dvd_two_pow_add_one {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : Odd n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ho
  · have : 2 ^ (k + k) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  · exact ho

theorem mem_largeEvenMatConjImage_of_mem_innAutDerived {K : Type} [Field K] [Finite K]
    {d m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 2) (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ m = 2))
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m)))}
    (hφ : φ ∈ innAutDerived (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m)))) :
    φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))
      (LargeEvenGUSet (Fin d) K (2 ^ m)) := by
  have h : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, hB⟩ := exists_primeFormConjHom_of_mem_innAutDerived h
    CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram hd hq
    ((mem_innAutDerived_congr (InndiagSU.projEquiv h hd1)).2 hφ)
  have hφB : φ = (MulAut.congr (InndiagSU.projEquiv h hd1)).symm (primeFormConjHom h _ B) := by
    rw [← hB, MulEquiv.symm_apply_apply]
  rw [hφB]
  exact InndiagSU.congr_symm_mem h hd1 B


theorem not_ggOutsideInndiag_of_recipeUnitary {K : Type} [Field K] [Finite K] {d g : ℕ} (hg : 1 ≤ g)
    (hK : Nat.card K = (2 ^ g) ^ 2) (hd : 3 ≤ d) (hd6 : d ≤ 6) (hdq : ¬(d = 3 ∧ 2 ^ g = 2))
    (hfin : Finite (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ g))))
    {s t : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ g)))}
    (hsI : s ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ g)))
      (LargeEvenGUSet (Fin d) K (2 ^ g)))
    (htI : t ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ g)))
      (LargeEvenGUSet (Fin d) K (2 ^ g)))
    (hs3 : s ^ 3 = 1) (ht3 : t ^ 3 = 1) (hst : s * t = t * s) {n : ℕ} (hn : 3 ∣ 2 ^ n + 1)
    {J₁ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ g)))}
    (hJ₁ : CFSG.Open.IsComponentOf J₁ (fixSubgroup s))
    (hmark : LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ =>
      lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
        lab' = ⟨.twA, 2, 3 * n⟩))
    (hout : GGOutsideInndiag J₁ t) : False := by
  classical
  haveI := hfin
  have hodd := odd_of_three_dvd_two_pow_add_one hn
  obtain ⟨hJperf, lab, hlabΛ, hraw⟩ := hout.2 _ hmark
  have hJlab : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel ↥J₁ (· = lab) :=
    largeEvenMarkingLegacy_to_canonical_carrier (P := fun l _ _ _ => l = lab)
      ⟨hJperf, lab, hlabΛ, largeEvenRawDatum_mono
        (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨_, _, _, _, -, -, -, hlab, -⟩ := largeEvenRawDatum_exists hraw
  obtain rfl := label_eq_twA_of_isComponentOf_fixSubgroup ggLabelRigidInput_holds hK hd hdq hsI
    hs3 hJ₁ hodd hlab hJlab
  have hcard : Nat.card (↥J₁ ⧸ Subgroup.center ↥J₁) = CFSG.Open.ordTwistedA 2 (2 ^ (3 * n)) := by
    have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hJlab
    unfold CFSG.StandardType.MarkedModel at hM
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg] at hM
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM]
    norm_num [CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  have h3 : ∀ x, t (t (t x)) = x := fun x => by
    have hx := DFunLike.congr_fun ht3 x
    rwa [pow_three] at hx
  have hstab : t ∈ CFSG.GroupActions.subgroupStabAut J₁ := by
    change J₁.map t.toMonoidHom = J₁
    refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun l hl => hout.1 l hl) fun l hl => ?_
    exact ⟨t (t l), hout.1 _ (hout.1 l hl), h3 l⟩
  have hinn := centerQuotientHom_mem_innAutDerived_of_recipeUnitary hg hK hd hd6 hsI htI hs3 ht3
    hst hJ₁ (Nat.odd_mul.2 ⟨⟨1, rfl⟩, hodd⟩) hcard hstab
  obtain ⟨K', _, _, hK', -, -, θ, -, hQ⟩ := hraw
  have h8 : 2 ^ 3 ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by have := hodd.pos; omega)
  refine hQ ⟨MulAut.congr θ
    (centerQuotientHom ↥J₁ (CFSG.GroupActions.subgroupStabRestrict J₁ ⟨t, hstab⟩)),
    Subgroup.subset_closure (mem_largeEvenMatConjImage_of_mem_innAutDerived (d := 3)
      (m := 3 * n) (by have := hodd.pos; omega) hK' le_rfl (fun h => by have := h.2; omega)
      ((mem_innAutDerived_congr θ).2 hinn)), fun l l' hll' => ?_⟩
  have hγ : CFSG.GroupActions.subgroupStabRestrict J₁ ⟨t, hstab⟩ l = l' :=
    Subtype.ext (by rw [CFSG.GroupActions.subgroupStabRestrict_apply]; exact Eq.symm hll')
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk, hγ]

theorem ggUnitaryCubicKnown_holds : GGUnitaryCubicKnown := by
  intro lab hlab _ htag hrank _
  obtain ⟨tag, r, g⟩ := lab
  dsimp only at htag hrank
  subst htag
  obtain ⟨hg, -, hr2⟩ := hlab
  have hg' : 1 ≤ g := hg
  have hr2' : r = 2 → 2 ≤ g := hr2
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  intro _ _ hfin s t n hs3 _ ht3 hst hsI htI hn J₁ hJ₁ hmark hout
  have hJ : CFSG.Open.IsComponentOf J₁ (fixSubgroup s) := by
    have hfix : ggFix s = fixSubgroup s := Subgroup.ext fun _ => Iff.rfl
    rw [← hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.1 hJ₁
  have hdq : ¬(r + 1 = 3 ∧ 2 ^ g = 2) := fun ⟨h3, h2⟩ => by
    have : 2 ^ 2 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) (hr2' (by omega))
    omega
  exact not_ggOutsideInndiag_of_recipeUnitary (d := r + 1) (g := g) hg' hK (by omega) (by omega) hdq
    hfin hsI htI hs3 ht3 hst hn hJ hmark hout

end CFSG.StandardType.SCFourCover

end
