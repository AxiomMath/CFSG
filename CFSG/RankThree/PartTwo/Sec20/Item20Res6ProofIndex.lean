module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec18.Item186a
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KFactL3ParabolicOrbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M K P : Subgroup G) (n : ℕ), K ≤ M →
    M ≤ Subgroup.normalizer (K : Set G) →
    Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n)) →
    CFSG.Open.pCoreOf 2 K ≤ P → P ≤ K →
    Sec18.IsMaxParabolicRankTwo ((P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) →
      ¬ 4 ∣ (M ⊓ Subgroup.normalizer (P : Set G)).relIndex M

@[expose] def Step2051IndexN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T →
    (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
        projSL 3 (GaloisField 2 n)) ∧
      Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c))))) →
      ¬ 2 ∣ (M ⊓ N).relIndex (M ⊓ Subgroup.normalizer
        (((kTwenty M c ⊓ N) ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c) : Subgroup G) : Set G))

namespace Res6

variable {G : Type} [Group G]

theorem map_sup_pCoreOf_eq {K X : Subgroup G} (hXK : X ≤ K) :
    ((X ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) =
      (X.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
  have hOK : CFSG.Open.pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  rw [Subgroup.subgroupOf_sup hXK hOK, Subgroup.map_sup]
  have : ((CFSG.Open.pCoreOf 2 K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    exact (Sec18.mem_pCore_iff_mem_pCoreOf _).mpr hx
  rw [this, sup_bot_eq]

end Res6

theorem step2051Index_of (hK : KFactL3ParabolicOrbit) (hN : Step2051IndexN) : Step2051Index := by
  intro G _ _ A M L N c T hT hcase
  set K := kTwenty M c with hKdef
  set P := (K ⊓ N) ⊔ CFSG.Open.pCoreOf 2 K with hP
  set Y := M ⊓ Subgroup.normalizer (P : Set G) with hY
  obtain ⟨n, hn, ⟨e⟩, hpar⟩ := hcase
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hPK : P ≤ K := sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  have hpar' : Sec18.IsMaxParabolicRankTwo
      ((P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
    rw [hP, Res6.map_sup_pCoreOf_eq inf_le_left]
    exact hpar
  have ha := hK G M K P n hKM hMK ⟨e⟩ le_sup_right hPK hpar'
  have hb := hN G A M L N c T hT ⟨n, hn, ⟨e⟩, hpar⟩
  have hMNY : M ⊓ N ≤ Y := by
    intro x hx
    refine ⟨hx.1, Res6.mem_normalizer_sup (Sec20.mem_normalizer_inf_of_mem (hMK hx.1)
      (Subgroup.le_normalizer hx.2))
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hMK hx.1))⟩
  have hmul := Subgroup.relIndex_mul_relIndex (M ⊓ N) Y M hMNY inf_le_left
  intro h4
  rw [← hmul] at h4
  have hcop : Nat.Coprime 4 ((M ⊓ N).relIndex Y) := by
    have : Nat.Coprime 2 ((M ⊓ N).relIndex Y) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hb
    exact Nat.Coprime.pow_left 2 this
  exact ha (hcop.dvd_of_dvd_mul_left h4)

end CFSG.RankThree.PartTwo.Sec20
