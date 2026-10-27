module

public import CFSG.RankThree.PartOne.K133.Alpha
public import CFSG.RankThree.PartOne.K133.AlphaSz
public import CFSG.RankThree.PartOne.S13K.KFLift
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem two_pow_sub_one_dvd (f k : ℕ) : 2 ^ f - 1 ∣ 2 ^ (k * f) - 1 := by
  have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 k
  rwa [one_pow, ← pow_mul'] at this

theorem suzukiModel_of_lieModel {X : Type} [Group X] {f : ℕ}
    (h : CFSG.Blueprint.LieModel X .twistedB2 0 2 f) : CFSG.Blueprint.SuzukiModel X 2 f :=
  (CFSG.Blueprint.LieModel.suzukiModel h).2

theorem splitType_of_suzukiModel {G : Type} [Group G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G} {f : ℕ}
    (hK : CFSG.Blueprint.LieModel ↥K .twistedB2 0 2 f) (hpf : p ∣ 2 ^ f - 1) : SplitType p K :=
  fun _ hb1 hbp =>
    exists_two_subgroup_of_suzukiModel (suzukiModel_of_lieModel hK) hp hp2 hpf hb1 hbp

theorem splitType_of_rowType {G : Type} [Group G] {p : ℕ}
    {L : Subgroup G} {K : Subgroup G} {r f : ℕ} (hr1 : 1 ≤ r) (hr7 : r ≤ 7) (hp : p.Prime)
    (hp2 : p ≠ 2) (hRM : RowModelF p L r f) (hKR : KRowType r f K) : SplitType p K := by
  have hpf : p ∣ 2 ^ f - 1 := by
    interval_cases r <;> exact (by simp only [RowModelF] at hRM; exact hRM.2.1)
  have h3 : p ∣ 2 ^ (3 * f) - 1 := hpf.trans (two_pow_sub_one_dvd f 3)
  have h2 : p ∣ 2 ^ (2 * f) - 1 := hpf.trans (two_pow_sub_one_dvd f 2)
  interval_cases r
  · exact splitType_of_psl_two hp hp2 hKR hpf
  · exact splitType_of_psl_two hp hp2 hKR hpf
  · rcases hKR with hKR | hKR
    · exact splitType_of_psl_two hp hp2 hKR hpf
    · exact splitType_of_psl_two hp hp2 hKR h3
  · rcases hKR with hKR | hKR
    · exact splitType_of_psl_two hp hp2 hKR hpf
    · exact splitType_of_suzukiModel hp hp2 hKR hpf
  · rcases hKR with hKR | hKR
    · exact splitType_of_psl_two hp hp2 hKR hpf
    · exact splitType_of_psl_two hp hp2 hKR h2
  · rcases hKR with hKR | hKR
    · exact splitType_of_psl_two hp hp2 hKR hpf
    · exact splitType_of_psl_two hp hp2 hKR h2
  · exact splitType_of_psl_two hp hp2 hKR hpf

theorem kf133Two_of_E_eq_A (hS : SchreierFor InCatalog)
    (hTypes : ∀ r, 1 ≤ r → r ≤ 7 → KF132Types r) {G : Type} [Group G] [Finite G] {p : ℕ}
    {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A) {t : MulAut E}
    (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L) {K : Subgroup G} (hK : IsKt p E t K)
    {e : G} (he : e ∈ autFixedInG E t) (he1 : e ≠ 1) {I : Subgroup G}
    (hI : I ∈ thetaComponentsAt p e) (hKI : K ≤ I) :
    ((E = A ∧ ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
        StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) ∨
      ∃ J ∈ thetaCompZeroStarE p E, sectionTenRel p I J) := by
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.three_lt; omega
  obtain ⟨-, r, hr1, hr12, hrow, -, hrA, hr9⟩ := hF.three
  have hr8 : r ≤ 8 := by
    by_contra hlt
    have h4 := hr9 (by omega)
    rw [hEA, h.A_card] at h4
    have h5 := Sec12Three.five_le h
    have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  by_cases hr : r = 8
  · subst hr
    exact Or.inl ⟨hEA, hrow⟩
  · have hr7 : r ≤ 7 := by omega
    obtain ⟨f, hRM, hKR, hmov⟩ :=
      hTypes r hr1 hr7 G p A c L E h hF hF13 hT hrow hrA hr9 t ht htL K hK
    exact Or.inr (exists_zeroStar_of_split hS h hEA ht hK
      (splitType_of_rowType hr1 hr7 hp hp2 hRM hKR) (hmov hr8) he he1 hI hKI)

@[expose] def KF133TwoNe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → ∀ K : Subgroup G, IsKt p E t K →
    ∀ e ∈ autFixedInG E t, e ≠ 1 → ∀ I ∈ thetaComponentsAt p e, K ≤ I →
      ∃ J ∈ thetaCompZeroStarE p E, sectionTenRel p I J

theorem kf133Two_of_parts (hS : SchreierFor InCatalog)
    (hTypes : ∀ r, 1 ≤ r → r ≤ 7 → KF132Types r) (hNe : KF133TwoNe) : KF133Two := by
  intro G _ _ p A c L E hH hF hF13 hT t ht htL K hK e he he1 I hI hKI
  by_cases hEA : E = A
  · exact kf133Two_of_E_eq_A hS hTypes hH hF hF13 hT hEA ht htL hK he he1 hI hKI
  · exact Or.inr (hNe G p A c L E hH hF hF13 hT hEA t ht htL K hK e he he1 I hI hKI)

end CFSG.RankThree.PartOne.K133
