module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105SuzukiPGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105SuzukiLayer
import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofKO3
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankBridge
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2
open scoped commutatorElement


theorem kSuzukiL2_holds : KSuzukiL2 := by
  intro Y _ _ I K hIK h3 hrank hKN hperf m hm hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : Group.IsPerfect ↥K := by
    refine Group.isPerfect_def.2 (Subgroup.map_injective K.subtype_injective ?_)
    rw [Subgroup.map_subtype_commutator, hperf, Subgroup.map_top, Subgroup.range_subtype]
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL
  have hcard := card_of_isL2 hL (by omega)
  have h4m : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h3K : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [hcard, h4m]
    exact Dvd.dvd.mul_left (by simpa using Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := m)) _
  have h6K : ¬ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ 6 := by
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    rw [hcard] at hle
    have h16 : 16 ≤ 2 ^ m := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h256 : 256 ≤ (2 ^ m) ^ 2 := by nlinarith
    have : 16 * 255 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := Nat.mul_le_mul h16 (by omega)
    omega
  have hS3 : ∀ (H : Type) [Group H] (f : ↥K →* H), ¬ 3 ∣ Nat.card f.range → f.range = ⊥ :=
    fun H _ f hf => range_eq_bot_of_not_dvd hS f (fun hd => hf (h3K.trans hd))
  have hS6 : ∀ (H : Type) [Group H] (f : ↥K →* H), Nat.card f.range ∣ 6 → f.range = ⊥ :=
    fun H _ f hf => range_eq_bot_of_not_dvd hS f (fun hd => h6K (hd.trans hf))
  have h3c : Nat.Coprime 3 (Nat.card I) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  set Q := CFSG.pCore 2 I with hQ
  set σ := CFSG.RankThree.PartTwo.Sec20.Res11.quotAction hKN with hσdef
  have hfixP : ∀ p : ℕ, p.Prime → ∀ (k' : K), ∀ y ∈ CFSG.pCore p (↥I ⧸ Q), σ k' y = y := by
    intro p hp k' y hy
    by_cases hp2 : p = 2
    · subst hp2
      rw [CFSG.RankThree.PartTwo.Sec18.pCore_quotient_pCore_eq_bot, Subgroup.mem_bot] at hy
      rw [hy, map_one]
    by_cases hp3 : p = 3
    · subst hp3
      rw [CFSG.RankThree.PartTwo.Sec20.Res11.eq_one_of_mem_pCore_three h3c hy, map_one]
    have : Fact p.Prime := ⟨hp⟩
    set P := CFSG.pCore p (↥I ⧸ Q) with hP
    let ρ : ↥K →* MulAut P := (MulAut.characteristic P).comp σ
    have hrankP : CFSG.pRank p P ≤ 3 :=
      ((RankThree.PartOne.FixedRank36.pRank_le_of_injective P.subtype P.subtype_injective).trans
        (CFSG.RankThree.PartTwo.Sec20.Res11.pRank_quotient_le I hp hp2)).trans (hrank p hp hp2)
    have hρ : ρ = 1 := eq_one_of_pRank_le_three hL hm hp2 CFSG.pCore_isPGroup hrankP ρ
    exact congrArg (fun τ : MulAut P => ((τ ⟨y, hy⟩ : P) : ↥I ⧸ Q)) (DFunLike.congr_fun hρ k')
  have hfixF : ∀ (k' : K), ∀ y ∈ CFSG.fittingSubgroup (↥I ⧸ Q), σ k' y = y := by
    intro k' y hy
    rw [CFSG.fitting_eq_sup_pCore] at hy
    have hle : (⨆ p : (Nat.card (↥I ⧸ Q)).primeFactors.attach, CFSG.pCore p.1.1 (↥I ⧸ Q)) ≤
        RankThree.PartOne.FixedRank36.fixedSub (σ k') :=
      iSup_le fun p z hz => hfixP p.1.1 (Nat.prime_of_mem_primeFactors p.1.2) k' z hz
    exact hle hy
  have hKX : CFSG.IsKGroup (↥I ⧸ Q) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient
      (CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
        CFSG.Assembly.inCatalog_containsAbelianSimple hIK) Q
  have h3X : ¬ 3 ∣ Nat.card (↥I ⧸ Q) := fun hd =>
    h3 (hd.trans (Subgroup.card_quotient_dvd_card Q))
  have hrank5 : CFSG.Open.pRank 5 (⊤ : Subgroup (↥I ⧸ Q)) ≤ 3 := by
    have h5 := (CFSG.RankThree.PartTwo.Sec20.Res11.pRank_quotient_le I (p := 5) (by norm_num)
      (by norm_num)).trans (hrank 5 (by norm_num) (by norm_num))
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h5
    exact h5
  have hfixE : ∀ (k' : K), ∀ y ∈ CFSG.layer (↥I ⧸ Q), σ k' y = y := by
    intro k' y hy
    have hle : CFSG.layer (↥I ⧸ Q) ≤ RankThree.PartOne.FixedRank36.fixedSub (σ k') :=
      sSup_le fun J hJ z hz => fix_component_of_rank_three hKp hS3 hS6 σ hKX h3X hrank5 hJ k' hz
    exact hle hy
  have hfix : ∀ k' : K, ∀ y ∈ CFSG.generalizedFitting (↥I ⧸ Q), σ k' y = y := by
    intro k' y hy
    have hle : CFSG.generalizedFitting (↥I ⧸ Q) ≤
        RankThree.PartOne.FixedRank36.fixedSub (σ k') :=
      sup_le (fun z hz => hfixF k' z hz) (fun z hz => hfixE k' z hz)
    exact hle hy
  have hσ : σ = 1 := CFSG.RankThree.PartTwo.Sec20.Res11.eq_one_of_fix_generalizedFitting σ hfix
  rw [Subgroup.commutator_le]
  intro o ho k hk
  have hc := CFSG.RankThree.PartTwo.Sec20.Res11.comm_mem_of_quotAction_fix hKN ⟨k, hk⟩ ⟨o, ho⟩
    (by rw [← hσdef, hσ]; rfl)
  have he : ⁅o, k⁆ = ((k : Y) * o * (k : Y)⁻¹ * (o : Y)⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [he]
  exact Subgroup.inv_mem _ hc

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
