module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Red
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413L33Data
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413SpCaseI
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413SpCaseII
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413SpEnd
import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.PerfectCase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81.Asch1413
open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank

theorem asch1413_sp4_false (h64o : Asch6_4Odd) (h64s : Asch6_4Seven)
    {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {ρ : Q →* MulAut V} (hρ : Function.Injective ρ)
    {L A : Subgroup Q} (hF : genFittingFStar Q = L) (hZL : Subgroup.center ↥L = ⊥) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) (hmodel : LieModel ↥L .PSp 2 p 1)
    (hC : ∀ v : V, (∀ l ∈ L, ρ l v = v) → v = 1) (hA : Nat.card A = 4)
    (hAe : IsElemAbelian 2 A) (hq : IsQuadraticOn ρ A) : False := by
  classical
  obtain ⟨-, -, K, hKf, hKfin, hKcard, hne⟩ :=
    CFSG.GH74.Generic.lieModel_psp_data hmodel
  letI : Field K := hKf
  letI : Finite K := hKfin
  obtain ⟨e⟩ := hne
  have hKp : Nat.card K = p := by simpa using hKcard
  have hp2 : p ≠ 2 := by omega
  have hp6 : p ≠ 6 := by
    rintro rfl
    exact absurd hp (by norm_num)
  have h7 : 7 ≤ p := by omega
  have hodd : Odd (Nat.card K) := by
    rw [hKp]
    exact hp.odd_of_ne_two hp2
  have hK7 : 7 ≤ Nat.card K := by omega
  have hK5 : 5 ≤ Nat.card K := by omega
  subst hF
  have hLn : (genFittingFStar Q).Normal :=
    CFSG.ClassicalInvolution.genFittingFStar_normal Q
  have hsimp := shape1413Prime_simple_nonab (Or.inr ⟨p, hp, hp5, hmodel⟩)
  haveI := hsimp.1
  have hcent : Subgroup.centralizer (genFittingFStar Q : Set Q) = ⊥ :=
    CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hsimp.2
  have hc : Subgroup.centralizer (genFittingFStar Q : Set Q) ≤ genFittingFStar Q := by
    rw [hcent]; exact bot_le
  by_cases hI : ∃ z ∈ A, ∃ hzL : z ∈ genFittingFStar Q,
      IsConj (u1 K) (e ⟨z, hzL⟩)
  · obtain ⟨z, hzA, hzL, hzD⟩ := hI
    exact asch1413_sp4_caseI hV hρ rfl hZL hodd hK7 e hC hA hAe hq hzA hzL hzD
  · obtain ⟨e', hconj, hfix⟩ := asch1413_sp4_fixed_point hLn hodd hK5 e hA hAe
    have hzA : spIota e' (u1 K) ∉ A := by
      intro hzA
      apply hI
      have hzL : spIota e' (u1 K) ∈ genFittingFStar Q := (e'.symm (u1 K)).2
      refine ⟨spIota e' (u1 K), hzA, hzL, ?_⟩
      apply (hconj ⟨spIota e' (u1 K), hzL⟩).mp
      have he'z : e' ⟨spIota e' (u1 K), hzL⟩ = u1 K := by
        have h : (⟨spIota e' (u1 K), hzL⟩ : ↥(genFittingFStar Q)) = e'.symm (u1 K) :=
          Subtype.ext rfl
        rw [h, MulEquiv.apply_symm_apply]
      rw [he'z]
    obtain ⟨-, hAX⟩ :=
      asch1413_sp4_caseII_le h64o h64s hV hρ hLn hc hZL hp hKp h7 e' hA hAe hq hfix hzA
    exact asch1413_sp4_end h64o hV hρ hp hp5 hKp e' hA hAe hq hAX hzA

theorem asch1413_redfor_prime (h64o : Asch6_4Odd) (h64s : Asch6_4Seven) :
    Asch1413RedFor Shape1413Prime := by
  intro Q _ _ V _ _ hV ρ hρ L A hF hS hA hAe hq hC
  rcases hS with h33 | ⟨p, hp, hp5, hmodel⟩
  · exact asch1413_L33_of_model hV hρ hF h33 hA hAe hq
  · obtain ⟨hsimp, hnab⟩ := shape1413Prime_simple_nonab (Or.inr ⟨p, hp, hp5, hmodel⟩)
    haveI := hsimp
    have hZL : Subgroup.center ↥L = ⊥ :=
      CFSG.ComponentClassification.Helpers.center_eq_bot ↥L hnab
    exact asch1413_sp4_false h64o h64s hV hρ hF hZL hp hp5 hmodel hC hA hAe hq

theorem asch5_14_13Prime_holds (h64o : Asch6_4Odd) (h64s : Asch6_4Seven) :
    Asch5_14_13Prime :=
  asch5_14_13Prime_of_red (asch1413_redfor_prime h64o h64s)

end CFSG.LocalAnalysis.WeakClosure81

end
