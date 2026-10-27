module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenDefs
import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddL3
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddGlue
import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenL2
import CFSG.RankThree.PartTwo.Sec14.Ronan148TCenterFree

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

theorem inspectSig148L3LocEven_of_list (hList : EvenSimpleList) : InspectSig148L3LocEven := by
  intro X _ _ e he hiso hlist E hE9 hE3 hloc hfix K hKE hKp hK1 hKq hK46 hgen
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ := theta_eq_bot_of_loc hE9 hE3 hloc hfix hKE hKp hK1 hgen
  have hKq' : IsQuasisimple K := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot) hKq
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_isoLThreePi he hiso hKq' (isPGroup_center_of_theta_eq_bot hθ)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hKq'.2.1
  haveI hKs : IsSimpleGroup K := MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hfaith : ∀ ε ∈ E, ε ≠ 1 → ¬ K ≤ Sec4.autFix ε := fun ε hε hε1 =>
    faithful_of_loc hE9 hE3 hloc hfix hKE hKp hK1 hgen hε hε1
  have hinj := restrictAut_injective hKE hfaith
  have hE'9 : Nat.card (restrictAut hKE).range = 9 := by
    rw [← hE9]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hE'3 : ∀ ε ∈ (restrictAut hKE).range, ε ^ 3 = 1 := by
    rintro _ ⟨ε, rfl⟩
    rw [← map_pow, show ε ^ 3 = 1 from Subtype.ext (hE3 ε ε.2), map_one]
  have hgen' := top_le_iSup_restrictAut hKE hinj hgen
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKq'.2.2
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  rcases hList X e he hiso K hKs hnonab with ⟨j, hj, hM⟩ | hM | ⟨f, hf, hfe, hε⟩
  · exact (evenL2Excl hj hKs hM hE'9 hE'3 hgen').elim
  · refine (oddL2Excl K 3 2 Nat.prime_three (by norm_num) (by norm_num) hKs hM
      (fun P hP => ?_) _ hE'9 hE'3 hgen').elim
    rw [← Subgroup.card_map_of_injective K.subtype_injective]
    exact oddThreeRank X 2 e he hiso _ (isElemAbelian_map_subtype hP)
  · have hfe' : f * (e / f) = e := Nat.mul_div_cancel' hfe
    have he' : 1 ≤ e / f := Nat.div_pos (Nat.le_of_dvd (by omega) hfe) (by omega)
    have hiso' : Sec4.IsoLThreePi X 2 (f * (e / f)) := by rw [hfe']; exact hiso
    exact Or.inr (Or.inr ⟨2, f, e / f, inferInstance, hf, he', hiso', hε⟩)


theorem inspectSig148L3Loc_of_list (hList : EvenSimpleList) : InspectSig148L3Loc :=
  inspectSig148L3Loc_of_parts (inspectSig148L3LocEven_of_list hList) oddCenterFree oddTwoRank
      oddThreeRank oddL2Excl oddL3U3 oddU34Excl oddFive

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
