module

public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofClassical

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial

theorem seitzU1_psuField_conj_mem {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (σ : K ≃+* K) {x : MulAut (unitaryPSU h 3)} (hx : x ∈ (psuConj h).range) :
    psuField h σ * x * (psuField h σ)⁻¹ ∈ (psuConj h).range := by
  obtain ⟨A, rfl⟩ := hx
  exact ⟨_, (psuField_mul_psuConj_mul_inv σ A).symm⟩

theorem seitzU1_conj_injective {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun φ : MulAut G => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    exact (mul_inv_eq_iff_eq_mul.1 hx).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hmem

theorem seitzU1_rankLE2_unitaryPSU {p f : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData p f K} (h3 : (3 : K) ≠ 0) (hq : 2 < p ^ f) :
    RankLE2 3 (unitaryPSU h 3) := by
  intro F hF
  have hinj : Function.Injective (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)) :=
    seitzU1_conj_injective (CFSG.RankThree.PartTwo.KFacts.center_unitaryPSU_three_eq_bot h hq)
  have hF' := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hF
    (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3))
  have hsub : F.map (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)) ≤
      (psuConj h).range := by
    rintro _ ⟨x, -, rfl⟩
    exact (stdPinnedPSU3 h).inn_le ⟨x, rfl⟩
  have hle := CFSG.RankThree.PartTwo.Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range
    h3 _ hF' hsub
  rw [Subgroup.card_map_of_injective hinj] at hle
  exact le_trans hle (le_of_eq (by norm_num))

theorem seitzU1_planeRank2 {p f : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData p f K} (h3 : (3 : K) ≠ 0)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hD : E ≤ (psuConj h).range) :
    PlaneRank2 3 E := by
  set M : Subgroup (MulAut (unitaryPSU h 3)) :=
    (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range ⊔ E with hMdef
  have hM : M ≤ (psuConj h).range := sup_le (stdPinnedPSU3 h).inn_le hD
  intro F hF
  have hF' := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hF M.subtype
  have hinj : Function.Injective M.subtype := Subtype.val_injective
  have hsub : F.map M.subtype ≤ (psuConj h).range := by
    rintro _ ⟨x, -, rfl⟩
    exact hM x.2
  have hle := CFSG.RankThree.PartTwo.Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range
    h3 _ hF' hsub
  rw [Subgroup.card_map_of_injective hinj] at hle
  exact le_trans hle (le_of_eq (by norm_num))

theorem not_le_psuConj_range_of_not_narrow {p f : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData p f K} (h3 : (3 : K) ≠ 0) (hq : 2 < p ^ f)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : IsElemAbelian 3 E)
    (hN : ¬ NarrowScope 3 E) : ¬ E ≤ (psuConj h).range :=
  fun hD => hN (And.intro (seitzU1_rankLE2_unitaryPSU h3 hq) (Or.inr (seitzU1_planeRank2 h3 hD)))

theorem exists_ne_one_inf_psuConj_range {p f : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData p f K} (h3 : (3 : K) ≠ 0) (hq : 2 < p ^ f)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 9) (hn : ¬ E ≤ (psuConj h).range) :
    ∃ y ∈ E, y ∈ (psuConj h).range ∧ y ≠ 1 := by
  have := h.finite
  set N := (psuConj h).range with hNdef
  set C := (psuField h).range with hCdef
  have hcycK := (card_ringAut_and_isCyclic h.prime K h.card).2
  have hcyc : IsCyclic C :=
    isCyclic_of_surjective (psuField h).rangeRestrict (psuField h).rangeRestrict_surjective
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut (unitaryPSU h 3))) := by
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact SetLike.mem_coe.mpr (seitzU1_psuField_conj_mem σ (SetLike.mem_coe.mp hx))
    · intro hx
      have h2 := seitzU1_psuField_conj_mem σ⁻¹ (SetLike.mem_coe.mp hx)
      rw [map_inv] at h2
      have e : (psuField h σ)⁻¹ * (psuField h σ * x * (psuField h σ)⁻¹) * ((psuField h σ)⁻¹)⁻¹
          = x := by group
      rw [e] at h2
      exact SetLike.mem_coe.mpr h2
  have hBNC : ∀ b ∈ E, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b _
    obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq b
    exact ⟨psuConj h A, ⟨A, rfl⟩, psuField h σ, ⟨σ, rfl⟩, hAσ⟩
  have h1 := CFSG.RankThree.PartTwo.Sec4.card_le_three_mul_card_inf hE hcyc hCN hBNC
  rw [hc] at h1
  by_contra hno
  have hbot : E ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    rw [Subgroup.mem_bot]
    by_contra hy1
    exact hno ⟨y, hy.1, hy.2, hy1⟩
  rw [hbot, Subgroup.card_bot] at h1
  omega

end CFSG.RankThree.PartTwo.Sec19
