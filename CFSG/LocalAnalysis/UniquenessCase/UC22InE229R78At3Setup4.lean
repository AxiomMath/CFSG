module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R78At3
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ReeU3Excl
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Fstar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.ReeThreeType
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.UnitaryRow
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh
import CFSG.LocalAnalysis.UniquenessCase.UC7P3At3Layer
import CFSG.LocalAnalysis.UniquenessCase.UC7P3At3Lift
import CFSG.LocalAnalysis.UniquenessCase.UC7P3At3Rows
import CFSG.LocalAnalysis.UniquenessCase.UC7P3At3Sylow2
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Core3
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Good
import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic
import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.LayerBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (IsReeType LKQuot7 PPrimeCoreIn)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IrrOnMod)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem r7_8At3_of_config (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (k : Sec7Core4 G) (hp3 : k.p = 3) {H : Subgroup G} (hH : Config k H) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf k.p P (H ⊓ k.M)) :
    (∀ x ∈ CFSG.RankThree.PartOne.omegaOne k.p P, x ^ k.p = 1) ∧
      ((H ⊓ k.M = H ⊓ normalizer (P : Set G) ∧
          IrrOnMod (CFSG.Open.rankThreeLayer H ⊓ normalizer (P : Set G))
            (CFSG.RankThree.PartOne.omegaOne k.p P)
            (CFSG.inSubgroup frattini (CFSG.RankThree.PartOne.omegaOne k.p P)) ∧
          P = CFSG.RankThree.PartOne.omegaOne k.p P) ∨
        (IsReeType (LKQuot7 k.p H) 1 ∧
          ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ k.M) ∧
            S ≤ normalizer (CFSG.RankThree.PartOne.omegaOne k.p P : Set G) ∧ IsCyclic S ∧
              S ≤ CFSG.Open.rankThreeLayer (UC22.Opp k.p H) ∧
                S ≤ centralizer (PPrimeCoreIn k.p H : Set G))) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨hPHM, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  have hPH : P ≤ H := hPHM.trans inf_le_left
  have h75 := step75_of_stronglyEmbeddedThree k hp3 hK3
  obtain ⟨P', hP'eq, hP'N⟩ := k.exists_sylow_map_of_isSylowOf hH hP
  obtain ⟨hG, hR, hU⟩ := k.rows3_of_config hG3 hRee hp3 hH P'
  obtain ⟨hNF, hNn⟩ := k.inf_eq_and_le_normalizer_quotient hG3 hp3 hH P' hP'N
  rcases irreducible_or_psl28_of_gls3ConclusionPlus hp3 P' hG hR hU with
    ⟨hPF, hexp, hirr⟩ | ⟨hI, hidx, h9, h18, h27⟩
  ·
    rw [inf_of_le_left hPF] at hNn
    obtain ⟨hpow, hMN, hW⟩ := k.alt1_of_quotient h75 hH hP hP'eq.symm hPF
      (fun x hx => (congrArg (fun n => x ^ n) hp3).trans (hexp x hx)) hNn hirr
    rw [CFSG.RankThree.PartOne.CTP.omegaOne_eq_of_pow_eq_one hpow]
    refine ⟨hpow, Or.inl ⟨hMN, fun W hFW hWP hWN => ?_, rfl⟩⟩
    rcases hW W hWP hWN with h | h
    · exact Or.inl (le_antisymm
        (h.trans (CFSG.Quasithin.Ch1Sec3.frattiniIn_eq_commutator hPp hpow).ge) hFW)
    · exact Or.inr h
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, -, hFn, hFc⟩ := k.isSimpleGroup_generalizedFitting_quotient hH
    rw [hP'eq] at h9 h18 h27 hNF
    have hPF : ¬ (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ≤
        CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) := fun h => by
      rw [inf_of_le_left h, h27] at h9
      exact absurd h9 (by norm_num)
    obtain ⟨S, hS, hSN, hSc, hSF⟩ :=
      k.exists_isSylowOf_two_of_index_eq_three hH hP rfl hidx hPF h27 (by rw [hNF]; exact h18)
    obtain ⟨hSHM, hS2, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
    have hcop : Nat.Coprime (Nat.card S) (Nat.card (CFSG.pPrimeCore k.p ↥H)) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hS2
      rw [hn]
      exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr
        (k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank))
    obtain ⟨hSE, hSC⟩ :=
      k.le_rankThreeLayer_opp_of_coprime h75 hH (hSHM.trans inf_le_left) hcop hSF
    have hP27 : Nat.card P = 27 := by
      rw [← h27, CFSG.RankThree.PartOne.StrongP.card_map_quotient_of_coprime
        (E := P.subgroupOf H) hPp.comap_subtype
        ((k.prime.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card)]
      exact (Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv).symm
    have hcl : ⁅⁅P, P⁆, P⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (CFSG.Quasithin.EmptyFaithfulMultiple.L3213.commutator_le_centralizer_of_card_dvd
        (p := k.p) (by rw [hP27, hp3]; norm_num))
    have hL := R72.imageModK_opp_eq_top k hH ⟨1, by rw [hidx, hp3, pow_one]⟩
    refine ⟨fun x hx => CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_omega1p_exponent
        k.prime k.odd hPp hcl x hx,
      Or.inr ⟨R72.isReeType_of_mulEquiv ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv).symm
        (R72.isReeType_one_of_psl28 _ hFn hFc hI hidx), S, hS,
        fun x hx => CFSG.RankThree.PartOne.Sec12Fus.mem_normalizer_omegaOne (hSN hx), hSc, hSE,
        hSC⟩⟩

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open PartOne.Section7 (Sec7Core4 StronglyEmbeddedThree normalizer_le_of_r6_3)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

theorem r7_8At3_dataOfSetup4 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hC : TheoremCAt S.M) : R7_8At3 (UC6.dataOfSetup4 hS hU S) := by
  intro H P D₀ hH hP hD₀
  obtain ⟨-, -, hsp, hHt, hHM, h2⟩ := hH
  subst hD₀
  exact Sec7Core4.r7_8At3_of_config hG3 hRee hK3
    (Sec7Core4.ofHuniq (UC6.dataOfSetup4 hS hU S).standing hU S.M S.maxLocal 3 Nat.prime_three
      (by norm_num) hsp fun T hT hT2 hT3 => normalizer_le_of_r6_3 _
        (UC6.r6_3_dataOfSetup4 hS hU S hC) Nat.prime_three (by norm_num) hsp hT hT2 hT3)
    rfl ⟨hHt, hHM, h2⟩ hP

end CFSG.LocalAnalysis.UniquenessCase.UC22
