module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCThetaComponents
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha

open CFSG Subgroup
open CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data calC Bar2)

private theorem bar2_quasisimple_and_dvd_card_center_quotient
    {G : Type} [Group G] [Finite G] (d : SylowThreeData G)
    (hcal : ∀ i, d.Lf i ∈ calC d.M) {k : Fin 3} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hRank : CFSG.Open.pRank p (d.Lf k) = 1) :
    CFSG.IsQuasisimple (Bar2 (d.Lf k)) ∧ p ∣ Nat.card (Bar2 (d.Lf k)) ∧
      p ∣ Nat.card (Bar2 (d.Lf k) ⧸ center (Bar2 (d.Lf k))) ∧
      3 ∣ Nat.card (Bar2 (d.Lf k) ⧸ center (Bar2 (d.Lf k))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  have hQsimple : CFSG.IsQuasisimple (Bar2 (d.Lf k)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr (hcal k).2.2)
  have hqRank : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 (d.Lf k))) = 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp
        (CFSG.pCore 2 (d.Lf k))
        (CFSG.GroupTheory.not_dvd_card_of_isPGroup CFSG.pCore_isPGroup hp hp2),
      CFSG.SectionRank.pRank_coe_eq_openPRank, hRank]
  have hqRank3 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 (d.Lf k))) = 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three
        (CFSG.pCore 2 (d.Lf k))
        (CFSG.GroupTheory.not_dvd_card_of_isPGroup CFSG.pCore_isPGroup Nat.prime_three
          (by norm_num)),
      CFSG.SectionRank.pRank_coe_eq_openPRank, d.hrank k]
  have hQbarperf : Group.IsPerfect (Bar2 (d.Lf k)) := hQsimple.1
  have hpZ :=
    @CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.not_dvd_card_center_of_pRank_eq_one
      (Bar2 (d.Lf k)) _ _ hQbarperf p inferInstance hp2 hqRank
  have h3Z :=
    @CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.not_dvd_card_center_of_pRank_eq_one
      (Bar2 (d.Lf k)) _ _ hQbarperf 3 inferInstance (by norm_num) hqRank3
  have hpBar := CFSG.GroupTheory.dvd_card_of_one_le_pRank hp hqRank.ge
  have h3Bar := CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three hqRank3.ge
  rw [Nat.card_congr (Subgroup.topEquiv (G := Bar2 (d.Lf k))).toEquiv] at hpBar h3Bar
  have hpSimple : p ∣ Nat.card (Bar2 (d.Lf k) ⧸ center (Bar2 (d.Lf k))) := by
    have h := hpBar
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (Bar2 (d.Lf k)))] at h
    exact (hp.dvd_mul.mp h).resolve_right hpZ
  have h3Simple : 3 ∣ Nat.card (Bar2 (d.Lf k) ⧸ center (Bar2 (d.Lf k))) := by
    have h := h3Bar
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (Bar2 (d.Lf k)))] at h
    exact (Nat.prime_three.dvd_mul.mp h).resolve_right h3Z
  exact ⟨hQsimple, hpBar, hpSimple, h3Simple⟩


theorem exists_perfect_commutator_pPrimeCore_eq_bot
    {G : Type} [Group G] [Finite G] {D : Data G} (c : Ctx82E3 D) (d : SylowThreeData G)
    (hcal : ∀ i, d.Lf i ∈ calC d.M) (hdL : d.L = c.L) {i j k : Fin 3} (hki : k ≠ i)
    (hkj : k ≠ j) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hRank : CFSG.Open.pRank p (d.Lf k) = 1) {b : G} (hb : b ∈ d.A i ⊔ d.A j)
    (hC : CFSG.Open.IsKGroup (centralizer ({b} : Set G))) :
    ∃ Q : Subgroup G, Q ≤ centralizer ({b} : Set G) ∧ Q ≤ d.M ∧ p ∣ Nat.card Q ∧
      ⁅(Q.subgroupOf (centralizer ({b} : Set G))).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 (centralizer ({b} : Set G)))),
        (CFSG.pPrimeCore 3 (centralizer ({b} : Set G))).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 (centralizer ({b} : Set G))))⁆ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  let C := centralizer ({b} : Set G)
  let θ := aschbacherSolvableCore 3 C
  let ρ := QuotientGroup.mk' θ
  obtain ⟨hQsimple, hpBar, hpSimple, h3Simple⟩ :=
    bar2_quasisimple_and_dvd_card_center_quotient d hcal hp (by omega) hRank
  obtain ⟨hQL, hQperf, -, π, hπ, hπ2⟩ :=
    SCThetaComponents.perfect_complement_lift_of_le_axis_pair d hcal hki hkj hb
  let Q := CFSG.Quasithin.perfectCore ((d.Lf k ⊔ CFSG.Open.pCoreOf 2 d.M) ⊓ C)
  have hQC : Q ≤ C := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hQCL : Q ≤ c.L ⊓ C := le_inf (hQL.trans (d.Lf_le_L k) |>.trans (le_of_eq hdL)) hQC
  have hQI : Q ≤ ONan.perfectCoreL c b := by
    have h := CFSG.Quasithin.le_perfectCore_of_perfect hQCL (Subgroup.isPerfect_iff.mp hQperf)
    rw [CFSG.Quasithin.perfectCore_eq_map_perfectResidual] at h
    exact h
  have hπsol : Group.IsSolvable π.ker := by
    have : Group.IsNilpotent π.ker := hπ2.isNilpotent
    infer_instance
  have hcoreComm :=
    SCThetaComponents.commutator_pPrimeCore_image_eq_bot_of_perfect_quasisimple_quotient
      c CFSG.RankThree.PartTwo.KFacts.kpSz hQI hQperf hQsimple π hπ hπsol hp hp5 hpSimple
      h3Simple hC
  change ⁅(Q.subgroupOf C).map ρ, (CFSG.pPrimeCore 3 C).map ρ⁆ = ⊥ at hcoreComm
  exact ⟨Q, hQC, hQL.trans (d.hLM k), hpBar.trans (Subgroup.card_dvd_of_surjective hπ),
    hcoreComm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha
