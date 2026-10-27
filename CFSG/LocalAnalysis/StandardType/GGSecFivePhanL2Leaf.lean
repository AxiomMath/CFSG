module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanWeylTriple
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylRest5
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCount
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

theorem ggPhan_comm_reflections_of_genL
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hgen : L = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e},
      ggRankOneIn L Bs r) :
    ∃ r ∈ ggAutomizer L Bs, ∃ r' ∈ ggAutomizer L Bs,
      r ∈ ggCoxRefl M e ∧ r' ∈ ggCoxRefl M e ∧ r ≠ r' ∧ r * r' = r' * r := by
  classical
  by_contra hcon
  push Not at hcon
  let R' : Set (MulAut ↥Bs) := {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e}
  let R : Set M.Group := {t : M.Group |
    ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ R'}
  have hgenR' : L = ⨆ r ∈ R', ggRankOneIn L Bs r := hgen
  have hR : ∀ t ∈ R, ∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹ := by
    intro t ht
    have htR' : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ R' := ht
    obtain ⟨w, i, hw⟩ := htR'.2
    exact ⟨w, i, e.injective (Subtype.val_injective hw)⟩
  have hcl : ∀ t ∈ R, ∀ t' ∈ R, t * t' * t⁻¹ ∈ R := by
    intro t ht t' ht'
    have htR' : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ R' := ht
    have ht'R' : ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ R' := ht'
    have heq : ((e (t * t' * t⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
        ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
          ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)⁻¹ := by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htR'.1 ht'R'.1) (Subgroup.inv_mem _ htR'.1)
    · obtain ⟨w, i, hw⟩ := ht'R'.2
      refine ⟨t * w, i, ?_⟩
      rw [heq, hw]
      rw [show (t * w) * M.simple i * (t * w)⁻¹ = t * (w * M.simple i * w⁻¹) * t⁻¹ by group]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hnc : ∀ t ∈ R, ∀ t' ∈ R, t ≠ t' → t * t' ≠ t' * t := by
    intro t ht t' ht' hne hcomm
    have htR' : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ R' := ht
    have ht'R' : ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ R' := ht'
    have hrr' : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ≠
        ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := fun h =>
      hne (e.injective (Subtype.val_injective h))
    have hcommR : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
      have h1 : ((e (t * t') : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
          ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
            ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
        simp only [map_mul, Subgroup.coe_mul]
      have h2 : ((e (t' * t) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
          ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
            ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
        simp only [map_mul, Subgroup.coe_mul]
      rw [← h1, ← h2, hcomm]
    exact (hcon _ htR'.1 _ ht'R'.1 htR'.2 ht'R'.2 hrr') hcommR
  rcases ggWeyl_triple_of_pairwise_noncomm hpres.1 hle3 R hR hcl hnc with
    hRempty | ⟨t₁, ht₁, t₂, ht₂, hsub⟩
  · exfalso
    have hR'empty : R' = ∅ := by
      ext r
      refine ⟨fun hr => ?_, fun hr => hr.elim⟩
      have hrA : r ∈ ggAutomizerJoin L Bs 𝒦 :=
        (le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦) hr.1
      let t : M.Group := e.symm ⟨r, hrA⟩
      have ht : t ∈ R := by
        show ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ R'
        have h1 : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = r := by
          dsimp only [t]
          simp only [MulEquiv.apply_symm_apply, Subtype.coe_mk]
        rw [h1]
        exact hr
      rw [hRempty] at ht
      exact ht
    have hLle : L ≤ ⊥ := by
      rw [hgenR']
      refine iSup_le fun r => iSup_le fun hr => ?_
      exact (hR'empty ▸ hr).elim
    exact ggRouteCfg_ne_bot hcfg (le_bot_iff.mp hLle)
  · exfalso
    let r₁ : MulAut ↥Bs := (e t₁ : ↥(ggAutomizerJoin L Bs 𝒦))
    let r₂ : MulAut ↥Bs := (e t₂ : ↥(ggAutomizerJoin L Bs 𝒦))
    have ht₁R' : ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ R' := ht₁
    have ht₂R' : ((e t₂ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ R' := ht₂
    have hr₁refl : GGIsReflection p r₁ :=
      ggCoxRefl_isReflection (fun i => hpres.2 i) ht₁R'.2
    have hr₂refl : GGIsReflection p r₂ :=
      ggCoxRefl_isReflection (fun i => hpres.2 i) ht₂R'.2
    have hsub' : R' ⊆ {r₁, r₂, r₁ * r₂ * r₁} := by
      intro r hr
      have hrA : r ∈ ggAutomizerJoin L Bs 𝒦 :=
        (le_sup_left : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦) hr.1
      let t : M.Group := e.symm ⟨r, hrA⟩
      have ht : t ∈ R := by
        show ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ R'
        have h1 : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = r := by
          dsimp only [t]
          simp only [MulEquiv.apply_symm_apply, Subtype.coe_mk]
        rw [h1]
        exact hr
      have he : r = ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
        dsimp only [t]
        simp only [MulEquiv.apply_symm_apply, Subtype.coe_mk]
      have htmem := hsub ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htmem
      rcases htmem with h | h | h
      · rw [Set.mem_insert_iff]
        left
        rw [he, h]
      · rw [Set.mem_insert_iff]
        right
        rw [Set.mem_insert_iff]
        left
        rw [he, h]
      · rw [Set.mem_insert_iff]
        right
        rw [Set.mem_insert_iff]
        right
        rw [he, h]
        show ((e (t₁ * t₂ * t₁) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
          ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
            ((e t₂ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
            ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
        simp only [map_mul, Subgroup.coe_mul]
    let R₂ : Finset (MulAut ↥Bs) := {r₁, r₂}
    have hR₂ : ∀ r ∈ R₂, GGIsReflection p r := by
      intro r hr
      simp only [R₂, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hr₁refl
      · exact hr₂refl
    have hcl₂ : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
        r ∈ Subgroup.closure (R₂ : Set (MulAut ↥Bs)) := by
      intro r hrA hrR
      have hr' := hsub' (show r ∈ R' from ⟨hrA, hrR⟩)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr'
      rcases hr' with h | h | h
      · rw [h]; exact Subgroup.subset_closure (by simp [R₂])
      · rw [h]; exact Subgroup.subset_closure (by simp [R₂])
      · rw [h]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _
          (Subgroup.subset_closure (by simp [R₂]))
          (Subgroup.subset_closure (by simp [R₂])))
          (Subgroup.subset_closure (by simp [R₂]))
    have hcount := ggPhan_card_bstar_le_of_genL hcfg hgen R₂ hR₂ hcl₂
    have hcard2 : R₂.card ≤ 2 := by
      change ({r₁, r₂} : Finset (MulAut ↥Bs)).card ≤ 2
      have h := Finset.card_insert_le r₁ ({r₂} : Finset (MulAut ↥Bs))
      simp only [Finset.card_singleton] at h
      omega
    have hcontra : p ^ 4 ≤ p ^ 3 := by
      calc p ^ 4 ≤ Nat.card Bs := (ggConfig_bstar_facts hcfg.1.1).2.2.2
        _ ≤ p ^ (R₂.card + 1) := hcount
        _ ≤ p ^ 3 := Nat.pow_le_pow_right (ggConfig_bstar_facts hcfg.1.1).1.pos (by omega)
    have hp1 : 1 < p := (ggConfig_bstar_facts hcfg.1.1).1.one_lt
    exact absurd hcontra (not_le.mpr (Nat.pow_lt_pow_right hp1 (by norm_num : 3 < 4)))

end CFSG.StandardType

end
