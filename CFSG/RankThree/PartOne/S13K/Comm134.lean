module

public import CFSG.RankThree.PartOne.S13K.Pair134
public import CFSG.RankThree.PartOne.S13K.CommDistinct
public import CFSG.RankThree.PartOne.S12.Sec141Row
public import CFSG.RankThree.PartOne.K1320X.TwoSubModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

theorem centralizes_of_distinct_components {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {K₁ K₂ I₁ I₂ : Subgroup G} {e : G} (h1 : I₁ ∈ thetaComponentsAt p e)
    (h2 : I₂ ∈ thetaComponentsAt p e) (hne : I₁ ≠ I₂) (hK₁ : K₁ ≤ I₁) (hK₂ : K₂ ≤ I₂)
    (hperf : Group.IsPerfect ↥K₁)
    (hθ : K₁ ≤ Subgroup.centralizer
      (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) : Set G)) :
    K₁ ≤ Subgroup.centralizer (K₂ : Set G) := by
  set N := inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) with hN
  have hcomm : ⁅K₁, K₂⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact S11d.commutator_mem_theta_of_ne hp h1 h2 hne x (hK₁ hx) y (hK₂ hy)
  have h1' : ⁅⁅K₁, K₂⁆, K₁⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro z hz x hx
    have hzx := Subgroup.mem_centralizer_iff.mp (hθ hx) z (hcomm hz)
    rw [commutatorElement_def, hzx]
    simp
  have h2' : ⁅⁅K₂, K₁⁆, K₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm K₂ K₁]
    exact h1'
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K₁) (H₂ := K₁) (H₃ := K₂)
    h1' h2'
  rw [Subgroup.isPerfect_iff.mp hperf] at h3
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxy : ⁅x, y⁆ ∈ ⁅K₁, K₂⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h3, Subgroup.mem_bot, commutatorElement_def] at hxy
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hxy)).symm

theorem inf_eq_bot_of_centralizes {G : Type} [Group G] {K₁ K₂ : Subgroup G}
    (hc : K₁ ≤ Subgroup.centralizer (K₂ : Set G)) (hcen : Subgroup.center ↥K₁ = ⊥) :
    K₁ ⊓ K₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx.1⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hc y.2) x hx.2).symm
  rw [hcen, Subgroup.mem_bot] at hmem
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hmem)

@[expose] def KFCommSame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    (E ≠ A ∨ (E = A ∧ ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J)) →
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ t ∈ reflectionSet p E, t ∈ torusImage E L →
      s ≠ t → s * t = t * s →
      kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧ kZero p E s ⊓ kZero p E t = ⊥

@[expose] def KFCommAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) →
    (E ≠ A ∨ (E = A ∧ ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J)) →
    ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → s * t = t * s →
      kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧ kZero p E s ⊓ kZero p E t = ⊥

theorem hcase_of_reinst {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E B : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hB : B ∈ admissibleTriples p E)
    (hcase : E ≠ A ∨ (E = A ∧ ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J)) :
    E ≠ B ∨ (E = B ∧ ∀ J : Subgroup G, J ∈ sectionTenZeroStar p B → IsLThreeTypeAt p J) := by
  have hBcard : Nat.card B = p ^ 3 := hB.2.2.1
  rcases hcase with hEA | ⟨hEA, hall⟩
  · left
    intro hEB
    apply hEA
    refine (Subgroup.eq_of_le_of_card_ge h.A_le_E (le_of_eq ?_)).symm
    rw [h.A_card, ← hBcard, hEB]
  · right
    have hBA : B = A := by
      refine Subgroup.eq_of_le_of_card_ge (hEA ▸ hB.1) (le_of_eq ?_)
      rw [h.A_card, hBcard]
    exact ⟨hEA.trans hBA.symm, fun J' hJ' => hall J' (hBA ▸ hJ')⟩

@[expose] def KF141a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f → E = A →
    (∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J) →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → KFAt p E f t

theorem kfCommAll_of_inputs (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hLift : KFLiftAll)
    (h133 : KF133Two) (hDist : KFCommDistinct) (hKF141a : KF141a) (hSame : KFCommSame) :
    KFCommAll := by
  intro G _ _ p A c L E h hF hF13 hT hcase s hs t ht hst hcomm
  have hp := h.prime
  have hLs := hLift G p A c L E h hF hF13 hT hcase s hs
  have hLt := hLift G p A c L E h hF hF13 hT hcase t ht
  have hLs' : KFLiftAt p E s := hLs
  have hLt' : KFLiftAt p E t := hLt
  obtain ⟨hqs, hcs, hns, hms, ks, hks, hksK, hks_eq⟩ := hLs
  obtain ⟨hqt, hct, hnt, hmt, kt, hkt, hktK, hkt_eq⟩ := hLt
  rcases pair_cases_dich hS hRe hLift h133 h hF hF13 hT hcase hs ht with
    ⟨e, I₁, I₂, heE, he1, hesE, hetE, hI₁, hI₂, hne, hK₁, hK₂⟩ | ⟨J, hJ, hKsJ, hKtJ⟩
  ·
    have hspl : E ≠ A ∨ HasTwoSub E (kZero p E s) ∨ HasTwoSub E (kZero p E t) := by
      rcases hcase with hEA | ⟨hEA, hall⟩
      · exact Or.inl hEA
      · right
        left
        obtain ⟨hrs, X, hX, hsX⟩ := hs
        obtain ⟨B, c', hB, hc'B, hc'1, hX12, hXF, hX13, hXT⟩ := hRe G p A c L E h hF13 hT X hX
        have hBA : B = A := by
          refine Subgroup.eq_of_le_of_card_ge (hEA ▸ hB.1) (le_of_eq ?_)
          rw [h.A_card, hB.2.2.1]
        obtain ⟨a, ha1, hpa, hmodel3⟩ := hall X (hBA ▸ Sec12Three.L_mem_zeroStar hX12)
        have hEB : E = B := hEA.trans hBA.symm
        have hallB : ∀ J : Subgroup G, J ∈ sectionTenZeroStar p B → IsLThreeTypeAt p J :=
          fun J hJ => hall J (hBA ▸ hJ)
        have hK := hKF141a G p B c' X E a hX12 hXF hX13 hXT ha1 hpa hmodel3 hEB hallB s
          ⟨hrs, X, hX, hsX⟩ hsX
        exact K1320X.hasTwoSub_of_kfAt h hF13 ⟨hrs, X, hX, hsX⟩ hK hpa
    have hc : kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) :=
      hDist G p A c L E h hF hF13 hT s hs t ht hLs' hLt' hspl hcomm e
        (Subgroup.mem_inf.mpr ⟨hesE, hetE⟩) he1 I₁ hI₁ I₂ hI₂ hne hK₁ hK₂
    exact ⟨hc, inf_eq_bot_of_centralizes hc hcs⟩
  · obtain ⟨B, c', hB, hc'B, hc'1, hJ12, hJF, hJ13, hJT⟩ := hRe G p A c L E h hF13 hT J hJ
    exact hSame G p B c' J E hJ12 hJF hJ13 hJT (hcase_of_reinst h hB hcase) s hs
      (Sec12Three.mem_torusImage_iff.mpr ⟨ks, hKsJ hksK, hks, hks_eq⟩) t ht
      (Sec12Three.mem_torusImage_iff.mpr ⟨kt, hKtJ hktK, hkt, hkt_eq⟩) hst hcomm

@[expose] def KFCommRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → E ≠ A → RowModel p L r →
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ t ∈ reflectionSet p E, t ∈ torusImage E L →
      s ≠ t → s * t = t * s →
      kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧ kZero p E s ⊓ kZero p E t = ⊥

theorem kfCommRow9_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFCommRow 9 := by
  intro G _ _ p A c L E h hF hEA hrow s hs hsL t ht htL hst hcomm
  obtain ⟨f, hf, hpq, hmodel⟩ := hrow
  exact ((kf126U4_of_multipliers hGA G p A c L E f h hF hf hpq hmodel
    (card_E_of_ne hF hEA)).2 s hs hsL t ht htL hst).1 hcomm

theorem kfCommSame_of_rows (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine)
    (h122 : Node122) (h9 : KFCommRow 9) (h10 : KFCommRow 10) (h11 : KFCommRow 11)
    (h12 : KFCommRow 12) : KFCommSame := by
  intro G _ _ p A c L E h hF hF13 hT hcase s hs hsL t ht htL hst hcomm
  rcases hcase with hEA | ⟨hEA, hall⟩
  · obtain ⟨-, r, hr1, hr12, hrow, -, hr8, hr9⟩ := hF.three
    have hr9' : 9 ≤ r := by
      by_contra hlt
      exact hEA (hr8 (by omega))
    interval_cases r
    · exact h9 G p A c L E h hF hEA hrow s hs hsL t ht htL hst hcomm
    · exact h10 G p A c L E h hF hEA hrow s hs hsL t ht htL hst hcomm
    · exact h11 G p A c L E h hF hEA hrow s hs hsL t ht htL hst hcomm
    · exact h12 G p A c L E h hF hEA hrow s hs hsL t ht htL hst hcomm
  · exfalso
    have hm1 : RowModel p L 1 := hall L (Sec12Three.L_mem_zeroStar h)
    obtain ⟨-, hweyl, -⟩ := Sec141Row.rowOne_data hRow1 h107 h109 h122 h hm1
    obtain ⟨ψ⟩ := hweyl
    have hs2 : s * s = 1 := RefFacts.mul_self_eq_one hs.1
    have ht2 : t * t = 1 := RefFacts.mul_self_eq_one ht.1
    have hs1 : s ≠ 1 := fun h1 => by
      have := hs.1.1
      rw [h1, orderOf_one] at this
      omega
    have ht1 : t ≠ 1 := fun h1 => by
      have := ht.1.1
      rw [h1, orderOf_one] at this
      omega
    have key : ∀ a b : Equiv.Perm (Fin 3), a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a ≠ b →
        a * b ≠ b * a := by decide
    let s' : ↥(torusImage E L) := ⟨s, hsL⟩
    let t' : ↥(torusImage E L) := ⟨t, htL⟩
    refine key (ψ s') (ψ t') ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul]
      have : s' * s' = 1 := Subtype.ext hs2
      rw [this, map_one]
    · rw [← map_mul]
      have : t' * t' = 1 := Subtype.ext ht2
      rw [this, map_one]
    · intro h1
      exact hs1 (congrArg Subtype.val (ψ.injective (h1.trans (map_one ψ).symm)))
    · intro h1
      exact ht1 (congrArg Subtype.val (ψ.injective (h1.trans (map_one ψ).symm)))
    · intro h1
      exact hst (congrArg Subtype.val (ψ.injective h1))
    · rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext hcomm)

@[expose] def KF141b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f → E = A →
    (∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J) →
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ t ∈ reflectionSet p E, t ∈ torusImage E L →
      s ≠ t → KFPairL p E f s t

@[expose] def KF141c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G) (f : ℕ),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → 1 ≤ f → p ∣ 2 ^ f - 1 →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f → E = A →
    (∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J) →
    ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → s * t = t * s →
      kZero p E s ≤ Subgroup.centralizer (kZero p E t : Set G) ∧ kZero p E s ⊓ kZero p E t = ⊥

theorem kf141_of_parts (ha : KF141a) (hb : KF141b) (hc : KF141c) : KF141 := by
  intro G _ _ p A c L E f hH hF hF13 hT hf hpq hmodel hEA hall
  exact ⟨ha G p A c L E f hH hF hF13 hT hf hpq hmodel hEA hall,
    hb G p A c L E f hH hF hF13 hT hf hpq hmodel hEA hall,
    hc G p A c L E f hH hF hF13 hT hf hpq hmodel hEA hall⟩

theorem kf141c_of_commAll (h : KFCommAll) : KF141c := by
  intro G _ _ p A c L E f hH hF hF13 hT _ _ _ hEA hall s hs t ht hst hcomm
  exact h G p A c L E hH hF hF13 hT (Or.inr ⟨hEA, hall⟩) s hs t ht hst hcomm

end CFSG.RankThree.PartOne.S13K
