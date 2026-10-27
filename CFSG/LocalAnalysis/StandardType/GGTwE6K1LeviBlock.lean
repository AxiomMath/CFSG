module

public import CFSG.LocalAnalysis.StandardType.GGTwE6K1LeviPair
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralBlocks
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem e6LeviBlock_a2Roots_subset {L : Type} [Field L] {b : Fin Tag.E6.rank → Lˣ}
    {α β : Fin Tag.E6.rank → ℤ} (h : IsA2Pair α β) (hα : rootChar b α = 1)
    (hβ : rootChar b β = 1) : a2Roots α β ⊆ rootCharKernel b := by
  have hneg : ∀ v, rootChar b v = 1 → rootChar b (-v) = 1 := fun v hv => by
    have e := rootChar_add b v (-v)
    rwa [add_neg_cancel, rootChar_zero, hv, one_mul, eq_comm] at e
  have hab : rootChar b (α + β) = 1 := by rw [rootChar_add, hα, hβ, one_mul]
  intro γ hγ
  refine ⟨a2Roots_isRoot h γ hγ, ?_⟩
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hα, hneg _ hα, hβ, hneg _ hβ, hab, hneg _ hab]

theorem e6Levi_exists_conj_block_step {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {a : Fin Tag.E6.rank → Lˣ}
    (hblk : ∀ w ∈ kernelReflectionGroup a, w ^ 3 = 1 → w ≠ 1 →
      ∃ α β : Fin Tag.E6.rank → ℤ, IsA2Pair α β ∧ w = pairRefl (α, β))
    {x₀ : ModGL Tag.E6 L} (hx₀ : x₀ ∈ monomialSubgroup Tag.E6 L) (hx₀3 : x₀ ^ 3 = 1)
    (hW : weylQuotientHom Tag.E6 L ⟨x₀, hx₀⟩ ∈ kernelReflectionGroup a)
    {A : Subgroup (ModGL Tag.E6 L)} (hA : A ≤ torusGroup Tag.E6 L)
    (hcomm : ∀ y ∈ A, x₀ * y = y * x₀) :
    ∃ g ∈ adjointGroup Tag.E6 L, (∀ y ∈ A, g * y = y * g) ∧
      g * x₀ * g⁻¹ ∈ torusGroup Tag.E6 L := by
  by_cases hw1 : weylQuotientHom Tag.E6 L ⟨x₀, hx₀⟩ = 1
  · refine ⟨1, one_mem _, fun y _ => by rw [one_mul, mul_one], ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact mem_torusGroup_of_weylQuotientHom_eq_one hx₀ hw1
  obtain ⟨α, β, hαβ, hwe⟩ := hblk _ hW (weylQuotientHom_pow_eq_one hx₀ hx₀3) hw1
  obtain ⟨g, hg, hgx⟩ := exists_conj_mem_torusGroup_of_blocks a2BlockToral_E6 hL [(α, β)]
    (fun p hp => by rw [List.mem_singleton.1 hp]; exact hαβ) (List.pairwise_singleton _ _) x₀ hx₀
    (by rw [hwe, List.map_singleton, List.prod_singleton])
  refine ⟨g, (Subgroup.closure_le _).2 (fun x hx => ?_) hg, fun y hy => ?_, hgx⟩
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨p, -, hx⟩ := hx
    exact rootSpan_le_adjointGroup L _ hx
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hA hy)
  have hfix : weylTuple (pairRefl (α, β)) b = b := by
    rw [← hwe]
    obtain ⟨u, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hx₀
    have hc := hcomm _ hy
    subst e
    rw [weylQuotientHom_torus_mul hk u hx₀]
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective
    rw [← canonicalRep_conj_rootDiagUnit, mul_inv_eq_iff_eq_mul]
    refine mul_left_cancel (a := k) ?_
    rw [← mul_assoc, hc, ← mul_assoc, rootDiagUnit_mul_comm_of_mem_torusGroup b hk, mul_assoc]
  obtain ⟨h1, h2⟩ := e6_rootChar_eq_one_of_pairRefl_fixed b hαβ hfix
  have hle : Subgroup.closure (⋃ p ∈ [(α, β)], (rootSpan Tag.E6 L (a2Roots p.1 p.2) :
      Set (ModGL Tag.E6 L))) ≤ Subgroup.centralizer {rootDiagUnit Tag.E6 b} := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    simp only [Set.mem_iUnion] at hx
    obtain ⟨p, hp, hx⟩ := hx
    obtain rfl := List.mem_singleton.1 hp
    exact rootSpan_le_centralizer b (e6LeviBlock_a2Roots_subset hαβ h1 h2) hx
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

end CFSG.StandardType.SCFourCover
