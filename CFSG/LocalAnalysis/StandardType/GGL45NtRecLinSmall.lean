module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial

private noncomputable def ggL45NtRecLinSmall_statedProjEquiv (d : ℕ) (K : Type) [Field K] :
    LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃* StatedProj (StatedSL d K) :=
  (TypeA.recipeEquiv d K).trans
    ((LinearCover.projectiveSpecialLinearEquivProjectiveSL d K).symm.trans
      (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d K))

private theorem ggL45NtRecLinSmall_statedClassicalModel (d : ℕ) (K : Type) [Field K] [Finite K]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hadm : StatedLieAdmissible .PSL d 2 f) :
    StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) .PSL d 2 f :=
  ⟨hadm, K, inferInstance, inferInstance, hK, ⟨ggL45NtRecLinSmall_statedProjEquiv d K⟩⟩

private theorem ggL45NtRecLinSmall_lieModel (d : ℕ) (K : Type) [Field K] [Finite K]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hadm : StatedLieAdmissible .PSL d 2 f) :
    CFSG.Blueprint.LieModel (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) .PSL d 2 f :=
  Or.inl ⟨by decide, ggL45NtRecLinSmall_statedClassicalModel d K hK hadm⟩

private theorem ggL45NtRecLinSmall_card_hopfMultiplier_congr {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) =
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) :=
  ((Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv).symm.trans
    ((Nat.card_congr
        (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv).trans
      (Nat.card_congr
        (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess Y).toEquiv)))

private theorem ggL45NtRecLinSmall_center_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [h, Subgroup.mem_bot] at hz'
  exact e.injective (by rw [hz', map_one])

private theorem ggL45NtRecLinSmall_centerPrime_of_hopf {R L' : Type} [Group R] [Group L']
    (hZR : Subgroup.center R = ⊥) {p : ℕ}
    (hM : ¬ p ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier R))
    (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    ¬ p ∣ Nat.card (Subgroup.center L') := by
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  have hcen : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    have h1 : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZR, Subgroup.mem_bot] at h1
    exact h1
  have heq : Subgroup.center L' = ψ.ker := le_antisymm hcen hker
  have hsurj :=
    CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective ψ hψ hker
  have hdvd : Nat.card ψ.ker ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier R) :=
    ⟨Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplierToKer ψ hψ hker).ker,
      CFSG.RankThree.PerfectCover.card_eq_card_mul_card_ker _ hsurj⟩
  rw [heq]
  exact fun hp => hM (hp.trans hdvd)

theorem ggL45NtRecLinSmall_three_two
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ 3) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) := by
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) = ⊥ :=
    ggL45NtRecLinSmall_center_eq_bot_of_mulEquiv (TypeA.recipeEquiv 3 K)
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := K) (by norm_num))
  have hLie3 : CFSG.Blueprint.LieModel (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) .PSL 3 2 1 :=
    ggL45NtRecLinSmall_lieModel 3 K (by simpa using hK)
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  have hLie2 : CFSG.Blueprint.LieModel (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) .PSL 2 7 1 :=
    CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _ hLie3
  obtain ⟨-, K', _, _, hK'card, ⟨eK'⟩⟩ :=
    (CFSG.Blueprint.LieModel.statedClassicalModel hLie2 (by decide) :
      StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) .PSL 2 7 1)
  haveI : Fintype K' := Fintype.ofFinite K'
  have hcard7 : Fintype.card K' = 7 := by
    rw [Fintype.card_eq_nat_card, hK'card]; norm_num
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier
      (k := K') (by rw [hcard7]; norm_num) (by rw [hcard7]; norm_num)
  have hgcd : Nat.gcd 2 (Fintype.card K' - 1) = 2 := by rw [hcard7]; norm_num
  have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K')) = 2 := by
    rw [Nat.card_congr eM.toEquiv, hgcd]
    change Nat.card (ZMod 2) = 2
    rw [Nat.card_zmod]
  have eR2 : LargeEvenProj (LargeEvenSLGroup (Fin 3) K) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K' :=
    eK'.trans (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K').symm
  have hcongr := ggL45NtRecLinSmall_card_hopfMultiplier_congr eR2
  have hcardH : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K')) = 2 :=
    ((Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K')).toEquiv).symm.trans hcardM)
  have hcardR : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))) = 2 := hcongr.trans hcardH
  have hM : ¬ p ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))) := by
    intro hpdiv
    rw [hcardR] at hpdiv
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv)
  intro L' _ _ ψ hψ hker hperf
  exact ggL45NtRecLinSmall_centerPrime_of_hopf hZR hM ψ hψ hker hperf

theorem ggL45NtRecLinSmall_three_four
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ 3) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) := by
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) = ⊥ :=
    ggL45NtRecLinSmall_center_eq_bot_of_mulEquiv (TypeA.recipeEquiv 3 K)
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := K) (by norm_num))
  have hLie3 : CFSG.Blueprint.LieModel (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) .PSL 3 2 2 :=
    ggL45NtRecLinSmall_lieModel 3 K (by rw [hK]; norm_num)
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Multipliers.L34Upper.multiplier_PSL_three_four _ hLie3
  have hcardG : Nat.card (CFSG.Open.griessHopfMultiplier
      (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))) = 48 := by
    rw [Nat.card_congr eM.toEquiv]
    change Nat.card (ZMod 3 × ZMod 4 × ZMod 4) = 48
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod]
    norm_num
  have hcardR : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))) = 48 :=
    ((Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
        (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))).toEquiv).symm.trans hcardG)
  have hM : ¬ p ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))) := by
    intro hpdiv
    rw [hcardR] at hpdiv
    rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at hpdiv
    rcases (Nat.Prime.dvd_mul hp).mp hpdiv with h2 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
    · exact hpd h3
  intro L' _ _ ψ hψ hker hperf
  exact ggL45NtRecLinSmall_centerPrime_of_hopf hZR hM ψ hψ hker hperf

theorem ggL45NtRecLinSmall_four_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) := by
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) = ⊥ :=
    ggL45NtRecLinSmall_center_eq_bot_of_mulEquiv (TypeA.recipeEquiv 4 K)
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 4) (k := K) (by norm_num))
  have hLie : CFSG.Blueprint.LieModel (LargeEvenProj (LargeEvenSLGroup (Fin 4) K)) .PSL 4 2 1 :=
    ggL45NtRecLinSmall_lieModel 4 K (by simpa using hK)
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  obtain ⟨eA8⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hLie
  have hcongr := ggL45NtRecLinSmall_card_hopfMultiplier_congr eA8
  have hcard8 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (alternatingGroup (Fin 8))) = 2 :=
    CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup le_rfl
  have hcardR : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (LargeEvenProj (LargeEvenSLGroup (Fin 4) K))) = 2 := hcongr.trans hcard8
  have hM : ¬ p ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (LargeEvenProj (LargeEvenSLGroup (Fin 4) K))) := by
    intro hpdiv
    rw [hcardR] at hpdiv
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv)
  intro L' _ _ ψ hψ hker hperf
  exact ggL45NtRecLinSmall_centerPrime_of_hopf hZR hM ψ hψ hker hperf

end CFSG.StandardType
