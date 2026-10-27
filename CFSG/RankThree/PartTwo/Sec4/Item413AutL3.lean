module

public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {K : Type} [Field K] [Finite K]

theorem ker_conjAut_three :
    (conjAut 3 K).ker = CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K := by
  ext A
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) (by norm_num) A 1
      (by rw [map_one, mul_one]; exact h)
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    exact conjAut_scalar c

omit [Finite K] in
theorem linearAutGroup_three_eq_range : linearAutGroup 3 K = (conjAut 3 K).range := by
  rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]

theorem card_inf_linearAutGroup_three_le (h3 : (3 : K) ≠ 0)
    {B : Subgroup (MulAut (projectiveSL 3 K))} (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card (B ⊓ linearAutGroup 3 K : Subgroup _) ≤ 9 := by
  have hNr := linearAutGroup_three_eq_range (K := K)
  set e : GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K ≃*
      (conjAut 3 K).range :=
    (QuotientGroup.quotientMulEquivOfEq ker_conjAut_three.symm).trans
      (QuotientGroup.quotientKerEquivRange _)
  have hle : B ⊓ linearAutGroup 3 K ≤ (conjAut 3 K).range := hNr ▸ inf_le_right
  set E : Subgroup (GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K) :=
    ((B ⊓ linearAutGroup 3 K).subgroupOf (conjAut 3 K).range).map e.symm.toMonoidHom
  have hcard : Nat.card E = Nat.card (B ⊓ linearAutGroup 3 K : Subgroup _) := by
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [← hcard]
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine card_le_nine_of_pgl3 h3 E ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hBc _ (Subgroup.mem_subgroupOf.mp hx).1 _ (Subgroup.mem_subgroupOf.mp hy).1
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hB.2 _ (Subgroup.mem_subgroupOf.mp hx).1)
    rw [this, map_one]

theorem card_le_27_of_mulAut_projectiveSL_three (h3 : (3 : K) ≠ 0)
    (B : Subgroup (MulAut (projectiveSL 3 K))) (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≤ 27 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, f, hp, hK⟩ := FiniteField.card' K
  have hcycK := (card_ringAut_and_isCyclic hp K (by rw [Nat.card_eq_fintype_card, hK])).2
  have hcyc : IsCyclic (fieldAut 3 K).range :=
    isCyclic_of_surjective (fieldAut 3 K).rangeRestrict (fieldAut 3 K).rangeRestrict_surjective
  have hCN : (fieldAut 3 K).range ≤
      Subgroup.normalizer
        ((linearAutGroup 3 K : Subgroup _) : Set (MulAut (projectiveSL 3 K))) := by
    rintro _ ⟨σ, rfl⟩
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    rw [linearAutGroup_three_eq_range] at hx ⊢
    obtain ⟨A, rfl⟩ := hx
    refine ⟨Matrix.GeneralLinearGroup.map (σ : K →+* K) A, ?_⟩
    rw [fieldAut_mul_conjAut, mul_inv_cancel_right]
  have hBNC : ∀ b ∈ B, ∃ n ∈ linearAutGroup 3 K, ∃ c ∈ (fieldAut 3 K).range, b = n * c := by
    intro b hb
    by_cases hbN : b ∈ linearAutGroup 3 K
    · exact ⟨b, hbN, 1, one_mem _, (mul_one b).symm⟩
    · obtain ⟨σ, -, H, hH⟩ :=
        KFacts.linear_order_three_field_descent (by norm_num) b (hB.2 b hb) hbN
      refine ⟨conjAut 3 K H * conjAut 3 K (Matrix.GeneralLinearGroup.map (σ : K →+* K) H⁻¹),
        ?_, fieldAut 3 K σ, ⟨σ, rfl⟩, ?_⟩
      · rw [linearAutGroup_three_eq_range]
        exact ⟨_, map_mul _ _ _⟩
      · rw [hH, ← map_inv, mul_assoc, fieldAut_mul_conjAut, ← mul_assoc]
  have h1 := card_le_three_mul_card_inf hB hcyc hCN hBNC
  have h2 := card_inf_linearAutGroup_three_le h3 hB
  omega

theorem rankAutL3_holds : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 3 → 1 ≤ f →
    CFSG.pRank 3 (MulAut (projSL 3 (GaloisField p f))) ≤ 3 := by
  intro p f _ hp3 hf
  have h3 := three_ne_zero_of_card (Fact.out) hp3 (GaloisField.card p f (by omega))
  exact pRank_three_le_of_card_le (card_le_of_mulEquiv_mulAut (projSLEquivProjectiveSL 3 _)
    (card_le_27_of_mulAut_projectiveSL_three h3))

omit [Finite K] in
theorem descendAut_three_injective :
    Function.Injective (descendAut 3 K) := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro e he
  rw [MonoidHom.mem_ker] at he
  rw [Subgroup.mem_bot]
  refine KFacts.eq_one_of_forall_mul_inv_mem_center fun s => ?_
  have h := congrArg (fun φ : MulAut (projectiveSL 3 K) => φ (proj 3 K s)) he
  simp only [descendAut_proj, MulAut.one_apply] at h
  rw [proj_eq_proj_iff, scalars_eq_center] at h
  have := (Subgroup.center _).inv_mem h
  simpa using this

theorem rankAutSL3_holds : ∀ (p f : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K], p ≠ 3 →
    Nat.card K = p ^ f → CFSG.pRank 3 (MulAut (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) ≤ 3 := by
  intro p f _ K _ _ hp3 hK
  have h3 := three_ne_zero_of_card (Fact.out) hp3 hK
  refine pRank_three_le_of_card_le (card_le_of_mulEquiv_mulAut
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm fun B hB => ?_)
  have := card_le_27_of_mulAut_projectiveSL_three h3 (B.map (descendAut 3 K))
    (isElemAbelian_map _ hB)
  rwa [Subgroup.card_map_of_injective descendAut_three_injective] at this

end CFSG.RankThree.PartTwo.Sec4
