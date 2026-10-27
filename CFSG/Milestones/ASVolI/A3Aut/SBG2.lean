module

public import CFSG.Milestones.ASVolI.A3Aut.SBBase

public section

namespace CFSG.ASVolI

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.X6

section Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem burnsideAut_xElt_one_ne_one
    (i : Fin τ.rank) : xElt (τ := τ) (K := K) i 1 ≠ 1 := by
  intro h
  have h1 : (xUnit τ K i 1 : Module.End K (RootModule τ K)) = xUnit τ K i 0 := by
    rw [xUnit_zero]
    exact congrArg (fun g : adjointGroup τ K => ((g : ModGL τ K) : Module.End K (RootModule τ K))) h
  exact one_ne_zero (xOp_injective i h1)

theorem burnsideAut_rankOneSubgroup_le
    {Y : Subgroup (adjointGroup τ K)}
    (hUY : (posUnipotent τ K).subgroupOf (adjointGroup τ K) ≤ Y) {i : Fin τ.rank}
    (hn : (⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup τ K) ∈ Y) :
    rankOneSubgroup (τ := τ) (K := K) i ≤ Y := by
  have hx : ∀ c : K, xElt (τ := τ) (K := K) i c ∈ Y := fun c =>
    hUY (Subgroup.mem_subgroupOf.2 (xUnit_mem_posUnipotent i c))
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, hc⟩ := mem_simplePosSubgroup.1 hg
    rw [show g = xElt i c from Subtype.ext hc]
    exact hx c
  · obtain ⟨c, hc⟩ := mem_simpleNegSubgroup.1 hg
    have hg' : g = (⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup τ K) *
        xElt i (-c) * (⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup τ K)⁻¹ :=
      Subtype.ext (by rw [hc, yUnit_eq_weylElt_mul]; rfl)
    rw [hg']
    exact mul_mem (mul_mem hn (hx _)) (inv_mem hn)

theorem burnsideAut_solvBorel_chevalley
    [Finite K] (hK : 4 ≤ Nat.card K) :
    burnsideAut_SolvBorel ↥(adjointGroup τ K) ((posUnipotent τ K).subgroupOf (adjointGroup τ K)) := by
  intro Y hUY hYs
  set Y' : Subgroup (ModGL τ K) := Y.map (adjointGroup τ K).subtype with hY'
  have hY'C : Y' ≤ adjointGroup τ K := Subgroup.map_subtype_le Y
  have hUY' : posUnipotent τ K ≤ Y' := fun u hu =>
    ⟨⟨u, posUnipotent_le_adjointGroup hu⟩, hUY (Subgroup.mem_subgroupOf.2 hu), rfl⟩
  have hK' : (4 : ℕ∞) ≤ ENat.card K := by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast hK
  have hJ : ∀ i, i ∉ {i | weylElt τ K i 1 ∈ Y'} := by
    intro i hi
    obtain ⟨y, hy, hyn⟩ := hi
    have hn : (⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup τ K) ∈ Y := by
      rw [show (⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ : adjointGroup τ K) = y from
        Subtype.ext hyn.symm]
      exact hy
    exact burnsideAut_not_isSolvable_of_perfect_le ((rank_one_scalar_perfect τ K i).2 hK')
      (Subgroup.mem_sup_left (xElt_mem_simplePosSubgroup i 1)) (burnsideAut_xElt_one_ne_one i)
      (burnsideAut_rankOneSubgroup_le hUY hn) hYs
  have hY'B : Y' ≤ borelGroup τ K := by
    have h := le_parabolicSubgroup_of_posUnipotent_le hY'C hUY'
    rwa [Set.eq_empty_of_forall_notMem hJ, parabolicSubgroup, Set.image_empty,
      Subgroup.closure_empty, sup_bot_eq] at h
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    sup_le torusGroup_le_normalizer_posUnipotent Subgroup.le_normalizer
  intro y hy
  have hyN : (y : ModGL τ K) ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    hBN (hY'B ⟨y, hy, rfl⟩)
  rw [← Subgroup.subgroupOf_normalizer_eq posUnipotent_le_adjointGroup]
  exact Subgroup.mem_subgroupOf.2 hyN

theorem burnsideAut_isSylowTwoOf_posUnipotent
    [Finite K] [CharP K 2] :
    CFSG.QuasithinUnique.IsSylowTwoOf ((posUnipotent τ K).subgroupOf (adjointGroup τ K)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL τ K) := finite_modGL
  exact isSylowTwoOf_subgroupOf_top
    (isSylowTwoOf_iff_isSylowOf.2 (unique_Chevalley_positive_Sylow (τ := τ) (K := K) 2).1)

end Chevalley

theorem burnsideAut_solvBorel_G2 :
    ∀ (X : Type) [Group X] [Finite X] (f : ℕ), 2 ≤ f → CFSG.Quasithin.IsG2 2 f X →
      ∀ S : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ → burnsideAut_SolvBorel X S := by
  intro X _ _ f hf hX S hS
  obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact burnsideAut_solvBorel_of_isSylow e burnsideAut_isSylowTwoOf_posUnipotent
    (burnsideAut_solvBorel_chevalley hK4) hS

end CFSG.ASVolI
