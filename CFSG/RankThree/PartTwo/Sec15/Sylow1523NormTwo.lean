module

public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofDefs
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bA7
import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofE9Aut
import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofE9L
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec15.Item155RProof
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2ProofInner
public import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofZDefs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res2ProofHJ
public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartTwo.KFacts.KP4Aut
import CFSG.RankThree.PartTwo.KFacts.KP4Gen
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec12.Item128Bar125
import CFSG.RankThree.PartTwo.Sec13.Item131Assembly
import CFSG.RankThree.PartTwo.Sec13.Item131bProofK
import CFSG.RankThree.PartTwo.Sec13.Item131bProofOmega
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import Certificates.Certificate13951

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG.RankThree.PartTwo.Sec16.Proof166Res6 CFSG.RankThree.PartTwo.Sec13.RonanStep131b

theorem exists_normTwo_of_mulAut {H : Type} [Group H] (X B : Subgroup H)
    (h : ∀ E : Subgroup (MulAut X), IsPGroup 3 E → ∃ S : Subgroup X, S ≠ ⊥ ∧ IsPGroup 2 S ∧
      ∀ σ ∈ E, S.map (σ : X →* X) = S)
    (hB : IsPGroup 3 B) (hBN : B ≤ Subgroup.normalizer (X : Set H)) :
    ∃ U : Subgroup H, U ≤ X ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set H) := by
  let ρ : B →* MulAut X := X.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  obtain ⟨S, hS, h2, hfix⟩ :=
    h ρ.range (hB.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective)
  refine ⟨S.map X.subtype, Subgroup.map_subtype_le S, ?_, h2.map _, fun b hb => ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
    exact hS
  have hρ : ∀ s : X, ((ρ ⟨b, hb⟩ s : X) : H) = b * s * b⁻¹ := fun _ => rfl
  have hS' : S.map (ρ ⟨b, hb⟩ : X →* X) = S := hfix _ (MonoidHom.mem_range.mpr ⟨⟨b, hb⟩, rfl⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [SetLike.mem_coe, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨ρ ⟨b, hb⟩ s, ?_, hρ s⟩
    rw [← hS']
    exact Subgroup.mem_map_of_mem _ hs
  · rintro ⟨s, hs, hsy⟩
    rw [← hS'] at hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    refine ⟨t, ht, ?_⟩
    have h' : b * (t : H) * b⁻¹ = b * y * b⁻¹ := (hρ t).symm.trans hsy
    exact mul_left_cancel (mul_right_cancel h')

theorem ks1523NormTwo_holds : KS1523NormTwo := by
  intro H _ _ X B hX hB hBN
  refine exists_normTwo_of_mulAut X B ?_ hB hBN
  rcases hX with ⟨_, ⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · obtain ⟨ψ⟩ := KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 7 1)
    have h2 : (2 : GaloisField 7 1) ≠ 0 := two_ne_zero_of_charP (p := 7) (by norm_num)
    have hK : Nat.card (GaloisField 7 1) % 3 = 1 := by
      norm_num [GaloisField.card 7 1 (by norm_num)]
    exact transport_fourGroup (φ.trans ψ)
      (fun E₀ hE₀ => exists_fixed_fourGroup_projectiveSL h2 hK E₀ hE₀)
  · refine transport_fourGroup φ (fun E₀ hE₀ => ?_)
    have : Finite (MulAut (alternatingGroup (Fin 7))) :=
      Nat.finite_of_card_ne_zero (by rw [a7_card_mulAut]; norm_num)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hE₀
    have hdvd : 3 ^ n ∣ 5040 := by
      rw [← hn, ← a7_card_mulAut]
      exact Subgroup.card_subgroup_dvd_card E₀
    have hn2 : n ≤ 2 := by
      by_contra hlt
      have h27 := (pow_dvd_pow 3 (by omega : 3 ≤ n)).trans hdvd
      norm_num at h27
    have hcard : Nat.card E₀ ≤ 9 := by
      rw [hn]
      calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
        _ = 9 := by norm_num
    obtain ⟨V, hV, hV2, hfix⟩ := norm2_alt7 E₀ hE₀ hcard
    exact ⟨V, hV, hV2, hfix⟩

end CFSG.RankThree.PartTwo.Sec15
