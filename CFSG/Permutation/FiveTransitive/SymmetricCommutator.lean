module

public import CFSG.Permutation.FiveTransitive.CyclicNormalizerAlternating

public section

namespace CFSG

open scoped commutatorElement

namespace FiveTransitive.SymmetricCommutator

private theorem three_cycle_mem
    {F : Type*} [Fintype F] [DecidableEq F]
    {g : Equiv.Perm F} (hg : g.IsThreeCycle) : g ∈ commutator (Equiv.Perm F) := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < g.support.card by rw [hg.card_support]; decide)
  have heq := hg.eq_swap_mul_swap_iff_mem_support.mpr ha
  let u := Equiv.swap a (g a)
  let v := Equiv.swap (g a) (g (g a))
  have hcomm : ⁅u,v⁆ = g * g := by
    rw [heq]
    simp only [commutatorElement_def,u,v,Equiv.swap_inv,mul_assoc]
  have hmem : g * g ∈ commutator (Equiv.Perm F) := by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)
  have hcube : g * g * g = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg.orderOf] at h
    simpa only [pow_succ,pow_zero,one_mul] using h
  have hfour : (g * g) * (g * g) = g := by
    rw [← mul_assoc, hcube,one_mul]
  exact hfour ▸ (commutator (Equiv.Perm F)).mul_mem hmem hmem

private theorem eq_alternating
    (F : Type*) [Fintype F] [DecidableEq F] :
    commutator (Equiv.Perm F) = alternatingGroup F := by
  refine le_antisymm alternatingGroup.commutator_perm_le ?_
  let D := (commutator (Equiv.Perm F)).comap (alternatingGroup F).subtype
  have hle : Subgroup.closure {g : alternatingGroup F | g.val.IsThreeCycle} ≤ D := by
    apply (Subgroup.closure_le D).mpr
    intro g hg
    exact three_cycle_mem hg
  rw [alternatingGroup.closure_isThreeCycles_eq_top] at hle
  intro g hg
  exact hle (Subgroup.mem_top (⟨g,hg⟩ : alternatingGroup F))

private theorem exists_centralizing_lift
    {G F : Type*} [Group G] (Q : Subgroup G) [IsCyclic Q]
    [Fintype F] [DecidableEq F]
    (f : Subgroup.normalizer (Q : Set G) →* Equiv.Perm F)
    (hf : Function.Surjective f) (σ : Equiv.Perm F) (hσ : σ ∈ alternatingGroup F) :
    ∃ a : Subgroup.normalizer (Q : Set G),
      (a : G) ∈ Subgroup.centralizer (Q : Set G) ∧ f a = σ := by
  have hm : (commutator (Subgroup.normalizer (Q : Set G))).map f =
      alternatingGroup F := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact eq_alternating F
  rw [← hm] at hσ
  obtain ⟨a, ha, hfa⟩ := hσ
  exact ⟨a, CyclicNormalizerAlternating.commutator_le_centralizer Q ha, hfa⟩

theorem alternating_le_centralizer_image
    {G F : Type*} [Group G] (Q : Subgroup G) [IsCyclic Q]
    [Fintype F] [DecidableEq F]
    (f : Subgroup.normalizer (Q : Set G) →* Equiv.Perm F)
    (hf : Function.Surjective f) :
    alternatingGroup F ≤
      ((Subgroup.centralizer (Q : Set G)).subgroupOf
        (Subgroup.normalizer (Q : Set G))).map f := by
  intro σ hσ
  obtain ⟨a, ha, hfa⟩ := exists_centralizing_lift Q f hf σ hσ
  exact ⟨a, ha, hfa⟩

end FiveTransitive.SymmetricCommutator

end CFSG
