module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeWhole

public section

namespace CFSG.RankThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.CatalogueBSmallRee
open scoped commutatorElement

theorem le_center_of_inf_commutator_eq_bot {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]
    (h : N ⊓ commutator G = ⊥) : N ≤ Subgroup.center G := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : ⁅n, g⁆ ∈ N ⊓ commutator G := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have := mul_mem hn (hN.conj_mem n⁻¹ (inv_mem hn) g)
      simpa only [commutatorElement_def, mul_assoc] using this
    · rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top n) (Subgroup.mem_top g)
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem small_Ree_native_fixed_groups_solvable_radical_trivial (a : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (∀ R : Subgroup (ReeTag.G2.reeGamma K a), R.Normal → Group.IsSolvable R → R = ⊥) ∧
    (1 ≤ a → IsSimpleGroup (ReeTag.G2.reeGamma K a) ∧
      ∃ x y : ReeTag.G2.reeGamma K a, x * y ≠ y * x) ∧
    (a = 0 → ∀ w₀ : WeylGroup ReeTag.G2.tag, (∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
        (coxeterSystem ReeTag.G2.tag).length w₀) →
      (commutator (ReeTag.G2.reeGamma K a)).map (ReeTag.G2.reeGamma K a).subtype =
          Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ∧
        Nat.card (Subgroup.closure
          {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀}) = 504 ∧
        ∀ g : ReeTag.G2.reeGamma K a, (∀ d ∈ Subgroup.closure
          {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀},
            (g : ModGL ReeTag.G2.tag K) * d = d * g) → g = 1) := by
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  obtain ⟨hsimp, hnc, -, -, hzero, -⟩ := small_Ree_whole_group_p_components a K hK
  have hZ : Subgroup.center Γ = ⊥ := (small_Ree_fixed_group_center_trivial a K hK).1
  have := hsimp
  have hnsol : ¬ Group.IsSolvable (commutator Γ) := fun h => by
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable).2 h x y)
  have hcentS : Subgroup.center (commutator Γ) = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (commutator Γ)) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      exact hxy (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top y) x)
  have hbot : ∀ N : Subgroup Γ, N.Normal → N ⊓ commutator Γ = ⊥ → N = ⊥ := by
    intro N hN h
    have := le_center_of_inf_commutator_eq_bot N h
    rwa [hZ, le_bot_iff] at this
  refine ⟨fun R hR hRsol => hbot R hR ?_, fun ha => ?_, fun ha w₀ hw₀ => ?_⟩
  ·
    rcases Subgroup.Normal.eq_bot_or_eq_top (R.subgroupOf (commutator Γ)) with h | h
    · exact disjoint_iff.1 (Subgroup.subgroupOf_eq_bot.1 h)
    · exfalso
      have hle : commutator Γ ≤ R := Subgroup.subgroupOf_eq_top.1 h
      exact hnsol (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))
  · obtain ⟨-, hs, hn⟩ := reeGamma_G2_simple ha K hK
    exact ⟨hs, hn⟩
  · obtain ⟨hmap, hcard, -⟩ := hzero ha w₀ hw₀
    refine ⟨hmap, ?_, fun g hg => ?_⟩
    · rw [← hmap, Subgroup.card_map_of_injective Γ.subtype_injective, hcard]
    ·
      have hgC : g ∈ Subgroup.centralizer ((commutator Γ : Subgroup Γ) : Set Γ) := by
        refine Subgroup.mem_centralizer_iff.2 fun c hc => Subtype.ext ?_
        have hcD : (c : ModGL ReeTag.G2.tag K) ∈ Subgroup.closure
            {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} := by
          rw [← hmap]
          exact ⟨c, hc, rfl⟩
        exact (hg _ hcD).symm
      have hCS : Subgroup.centralizer ((commutator Γ : Subgroup Γ) : Set Γ) ⊓ commutator Γ = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).2 fun x ⟨hxC, hxS⟩ => ?_
        have hxZ : (⟨x, hxS⟩ : commutator Γ) ∈ Subgroup.center (commutator Γ) :=
          Subgroup.mem_center_iff.2 fun y => Subtype.ext
            (Subgroup.mem_centralizer_iff.1 hxC y y.2)
        rw [hcentS, Subgroup.mem_bot] at hxZ
        exact congrArg Subtype.val hxZ
      have hC := hbot _ inferInstance hCS
      rw [hC, Subgroup.mem_bot] at hgC
      exact hgC

end CFSG.RankThree
