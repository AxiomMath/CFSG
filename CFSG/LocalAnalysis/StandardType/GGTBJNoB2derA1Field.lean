module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA1
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA6
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem simpleSympFieldInput_holds :
    SimpleSympFieldInput := by
  intro lab hlam hsymp Q hQ
  rcases lab with ⟨tag, rank, n⟩
  rcases hsymp with ht | ht <;> subst ht
  all_goals
    simp only [LargeEvenInLambda2, LargeEvenLabelAll, LargeEvenRawDatum] at hlam hQ ⊢
    obtain ⟨hnpos, hrank2, hrankn⟩ := hlam
    obtain ⟨K, hKfld, hKfin, hKcard, hQ'⟩ := hQ
    letI : Field K := hKfld
    letI : Finite K := hKfin
    haveI : Fintype K := Fintype.ofFinite K
    have hcardK : Fintype.card K = 2 ^ n := by
      rw [Fintype.card_eq_nat_card, hKcard]
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n) hcardK
    refine ⟨K, hKfld, hKfin, hKcard, hQ', ?_⟩
    intro φ hφ1 hφ3 hφI J hJ hlabel
    haveI : NeZero rank := ⟨by omega⟩
    have hcenter : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K rank)) = ⊥ :=
      TableBSymp.center_spProj_eq_bot
    obtain ⟨g, hg⟩ := TableBSymp.sp_I_subset_inn (K := K) (m := rank) hφI
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hφ1 (by simpa using hg.symm)
    have hg3 : g ^ 3 = 1 := by
      apply mulAut_conj_injective hcenter
      rw [map_pow, hg, hφ3, map_one]
    obtain ⟨x, hx⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := rank) (K := K) g
    have hx3 : x ^ 3 = 1 := by
      apply AutPSp.proj_injective (n := rank) (K := K)
      rw [map_pow, hx, hg3, map_one]
    have hx1 : x ≠ 1 := by
      intro h
      apply hg1
      rw [← hx, h, map_one]
    have hJasm : CFSG.Assembly.IsComponentOf J (ggFixSub φ) := hJ
    rw [← hg, ← hx] at hJasm
    rw [CFSG.StandardType.TCJ.tcj_ggFixSub_eq_fixSubgroup] at hJasm
    have hJopen : CFSG.Open.IsComponentOf J
        (fixSubgroup (MulAut.conj (proj rank K x))) :=
      CFSG.Assembly.isComponentOf_iff_open.mp hJasm
    obtain ⟨-, hcomps⟩ := lieCompsCore_conj_sp_card (a6 := True)
      slFactorFacts_holds suFactorFacts_holds spFactorFacts_holds spFourTwoFacts_holds
      (fun _ => slAltSixFacts_holds) (fun _ => suAltSixFacts_holds)
      (fun _ => spAltSixFacts_holds) Nat.prime_three (by decide) Nat.prime_two hnpos
      hKcard (by omega) (by decide) (fun _ => by decide) x hx3
    obtain ⟨X, instX, hfinX, ⟨hXLD, hA6cond⟩, _, f', hf'surj, hf'ker⟩ := hcomps J hJopen
    have hA6J : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6)) :=
      ggB2der_label_iso_A6 hlabel
    have hA6X : Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)) := by
      obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hXLD.perfect f' hf'surj hf'ker
      obtain ⟨a⟩ := hA6J
      exact ⟨e.trans a⟩
    have hK2 : Nat.card K = 2 := hA6cond trivial hA6X
    have hn1 : n = 1 := Nat.pow_right_injective (a := 2) (by norm_num) (by
      change 2 ^ n = 2 ^ 1
      rw [← hKcard, hK2, pow_one])
    refine ⟨hn1, ?_⟩
    omega

end CFSG.StandardType.S2MathAs4B2der1822

end
