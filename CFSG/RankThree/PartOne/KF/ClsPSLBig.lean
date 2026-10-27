module

public import CFSG.RankThree.PartOne.KF.ClsCover
public import CFSG.RankThree.PartOne.KF.ClsTorus
public import CFSG.RankThree.PartOne.S12.InputsTable
public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PerfectCover CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial
open Matrix

namespace KFU

theorem exists_odd_prime_dvd_two_pow_sub_one_ne_five {f : ℕ} (hf : 2 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 5 ∧ r ∣ 2 ^ f - 1 := by
  rcases Nat.even_or_odd f with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨3, Nat.prime_three, by norm_num, by norm_num, ?_⟩
    have h : 2 ^ f = 4 ^ k := by
      rw [hk, ← two_mul, pow_mul]
      norm_num
    have h3 : 3 ∣ 4 ^ k - 1 := by
      have := Nat.sub_dvd_pow_sub_pow 4 1 k
      simpa only [one_pow] using this
    rw [h]
    exact h3
  · have hne : 2 ^ f - 1 ≠ 1 := by
      have : 8 ≤ 2 ^ f := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
    have hodd : (2 ^ f - 1) % 2 = 1 := by
      have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    have hr2 : r ≠ 2 := by
      rintro rfl
      omega
    refine ⟨r, hr, hr2, ?_, hrd⟩
    rintro rfl
    have h4 : ∀ j : ℕ, 4 ^ j % 5 = 1 ∨ 4 ^ j % 5 = 4 := by
      intro j
      induction j with
      | zero => left; rfl
      | succ j ih =>
        rcases ih with h | h <;> [right; left] <;> omega
    have h2f : 2 ^ f = 2 * 4 ^ k := by
      rw [hk, pow_succ, pow_mul]
      norm_num
      ring
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have := h4 k
    omega

theorem card_hopfMultiplier_psl
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {n f : ℕ} (hn : 5 ≤ n) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) :
    Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) ∧
      Nat.card (hopfMultiplier (Matrix.ProjectiveSpecialLinearGroup (Fin n) K)) =
        Nat.gcd n (2 ^ f - 1) := by
  have hadm : StatedLieAdmissible .PSL n 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  have hcl : StatedClassicalModel (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) .PSL n 2 f :=
    ⟨hadm, K, inferInstance, inferInstance, hK,
      ⟨projectiveSpecialLinearGroupEquivStatedProj n K⟩⟩
  have hm : Models.LieModel (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) .PSL n 2 f :=
    ⟨hadm, Or.inl hcl⟩
  obtain ⟨hcomm, ⟨e⟩⟩ := hGA _ .PSL n 2 f hm
  have hperf : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) := ⟨hcomm⟩
  refine ⟨hperf, ?_⟩
  rw [Nat.card_congr (hopfMultiplierEquivGriess _).symm.toEquiv, Nat.card_congr e.toEquiv]
  have hgen : Blueprint.Multiplier.genericOrders .PSL n 2 f = (Nat.gcd n (2 ^ f - 1), 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSL n 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]

theorem exists_cover_psl
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {n f : ℕ} (hn : 5 ≤ n) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) {L : Type} [Group L] [Finite L] (hLp : Group.IsPerfect L)
    (p : L →* Matrix.ProjectiveSpecialLinearGroup (Fin n) K) (hp : Function.Surjective p)
    (hpc : p.ker ≤ Subgroup.center L) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin n) K →* L, Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
  obtain ⟨hperf, hcardM⟩ := card_hopfMultiplier_psl hGA hn hf hK
  have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by omega)
  set π : Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    QuotientGroup.ker_mk' _
  have hcard : Nat.card (hopfMultiplier (Matrix.ProjectiveSpecialLinearGroup (Fin n) K)) =
      Nat.card π.ker := by
    rw [hcardM, hπk, ← LinearFlag.scalars_eq_center, card_scalars (by omega), hK]
  obtain ⟨ρ, hρ, hρs⟩ := exists_hom_of_card_multiplier_eq hperf hSL π hπs hπk.le hcard p hp hpc
  refine ⟨ρ, hρs hLp, fun x hx => ?_⟩
  have h1 : π x = 1 := by
    rw [← hρ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]
  rw [← hπk]
  exact h1

end KFU

open KFU in
theorem psl_large_false {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Table123Generic p L A₀ F) {n f : ℕ} (hn : 5 ≤ n)
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) : False := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hf1 : 1 ≤ f := hadm.2.1
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd h.prime).mpr h.center_pPrime
  let e' : ↥L ⧸ Subgroup.center ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm
  have hq := isCentralPQuot_center e' hcop
  have hLp : Group.IsPerfect ↥L := h.quasisimple.1
  obtain ⟨ρ, hρs, hρk⟩ := exists_cover_psl hGA hn hf1 hK hLp _ hq.surjective hq.central
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  rcases Nat.lt_or_ge f 2 with hf | hf2
  ·
    have hf1' : f = 1 := by omega
    subst hf1'
    have hcenSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) = ⊥ := by
      rw [← Subgroup.card_eq_one, ← LinearFlag.scalars_eq_center, card_scalars (by omega), hK]
      simp
    have hρinj : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact eq_bot_iff.mpr (hρk.trans hcenSL.le)
    let ψ : Matrix.SpecialLinearGroup (Fin n) K ≃* ↥L := MulEquiv.ofBijective ρ ⟨hρinj, hρs⟩
    let π : Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    have hπinj : Function.Injective π := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcenSL]
    let χ : Matrix.SpecialLinearGroup (Fin n) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
      MulEquiv.ofBijective π ⟨hπinj, QuotientGroup.mk'_surjective _⟩
    exact h.not_PSL_two n ⟨hadm, K, hKf, hKfin, hK,
      ⟨ψ.symm.trans (χ.trans (projectiveSpecialLinearGroupEquivStatedProj n K))⟩⟩
  ·
    obtain ⟨r, hr, hr2, hr5, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
    have hrK : r ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hrd
    have hcen : 4 + 1 < n ∨ ¬ r ∣ n := by
      by_cases hn6 : 6 ≤ n
      · exact Or.inl (by omega)
      · right
        have : n = 5 := by omega
        subst this
        intro hrn
        exact hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp hrn)
    have h4 := le_localRank_of_surjective_torus hr hrK (by omega : 4 < n) (by omega) hcen ρ hρs hρk
    have h3 := (CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans h.evenRank_le
    omega

end CFSG.RankThree.PartOne
