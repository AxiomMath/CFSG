module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.Hom
import CFSG.ClassicalGroups.Orthogonal.FiveSquareModel

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.ClassicalGroups.Orthogonal

@[expose] noncomputable def fivePlusHom :
    fiveReflectionGroup 4 true true →* FiveSquareFrameGeneration.derived :=
  ((fiveGLEquiv.toMonoidHom.comp fivePlusMap).comp
    (fiveReflectionGroup 4 true true).subtype).codRestrict _ fun g => fivePlusMap_mem_derived g.2

theorem coe_fivePlusHom_apply (g : fiveReflectionGroup 4 true true) :
    (fivePlusHom g : (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)) =
      fiveGLEquiv (fivePlusMap g) :=
  rfl

theorem fivePlusHom_surjective : Function.Surjective fivePlusHom := by
  haveI : IsSimpleGroup FiveSquareFrameGeneration.derived :=
    FiveSquareFrameGeneration.derived_isSimpleGroup
  have hnormal : fivePlusHom.range.Normal := by
    refine ⟨fun n hn d => ?_⟩
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hn
    have hdO : (d : (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5)) ∈
        FiveSquareFrameGeneration.O :=
      Subgroup.commutator_le_self FiveSquareFrameGeneration.O d.2
    obtain ⟨g, hg, hconj⟩ := exists_isometry_fivePlusMap_conj hdO
    have hgmem : g * (k : GL (Fin 5) (ZMod 5)) * g⁻¹ ∈
        Subgroup.closure (fiveReflections 4 true true) :=
      Subgroup.closure_induction
        (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure (fiveReflections 4 true true))
        (fun r hr => Subgroup.subset_closure (conj_mem_fiveReflections hg hr))
        (by simp)
        (fun x y _ _ ihx ihy => by
          have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
          rw [hxy]
          exact Subgroup.mul_mem _ ihx ihy)
        (fun x _ ih => by
          have hx' : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
          rw [hx']
          exact Subgroup.inv_mem _ ih)
        k.2
    refine MonoidHom.mem_range.mpr
      ⟨⟨g * (k : GL (Fin 5) (ZMod 5)) * g⁻¹, hgmem⟩, ?_⟩
    apply Subtype.ext
    rw [coe_fivePlusHom_apply, hconj (k : GL (Fin 5) (ZMod 5))]
    rfl
  obtain ⟨r, hr, hz⟩ := exists_fivePlusMap_eq_z
  have hzmem : FiveSquareFrameGeneration.zD ∈ fivePlusHom.range := by
    refine MonoidHom.mem_range.mpr ⟨⟨r, Subgroup.subset_closure hr⟩, ?_⟩
    apply Subtype.ext
    rw [coe_fivePlusHom_apply, hz]
  have hz_ne_one : FiveSquareFrameGeneration.zD ≠ 1 := by
    intro h
    have hz1 : FiveSquareFrameGeneration.z = 1 := by
      have h' := congrArg (fun x : FiveSquareFrameGeneration.derived =>
        (x : (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5))) h
      simpa using h'
    have h0 : FiveSquareFrameGeneration.z (FiveSquareFrameGeneration.e 0) =
        FiveSquareFrameGeneration.e 0 := by
      rw [hz1]
      rfl
    rw [FiveSquareFrameGeneration.z_e] at h0
    have h2 : (-FiveSquareFrameGeneration.e 0 : Fin 5 → ZMod 5) ≠
        FiveSquareFrameGeneration.e 0 := by
      intro hh
      have h3 := congrFun hh 0
      simp only [Pi.neg_apply, FiveSquareFrameGeneration.Generic.e_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne] at h3
      exact (by decide : ¬((-1 : ZMod 5) = 1)) h3
    exact h2 (by simpa using h0)
  have hne : fivePlusHom.range ≠ ⊥ := by
    intro hbot
    exact hz_ne_one (Subgroup.mem_bot.mp (hbot ▸ hzmem))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal fivePlusHom.range with h | h
  · exact absurd h hne
  · exact MonoidHom.range_eq_top.mp h

theorem ker_fivePlusHom :
    fivePlusHom.ker = Subgroup.center (fiveReflectionGroup 4 true true) := by
  apply le_antisymm
  · intro k hk
    have hk1 : fivePlusHom k = 1 := MonoidHom.mem_ker.mp hk
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    have hmap1 : fivePlusMap (k : GL (Fin 5) (ZMod 5)) = 1 := by
      have h' := congrArg (fun x : FiveSquareFrameGeneration.derived =>
        (x : (Fin 5 → ZMod 5) ≃ₗ[ZMod 5] (Fin 5 → ZMod 5))) hk1
      rw [coe_fivePlusHom_apply] at h'
      exact fiveGLEquiv.injective (by rw [map_one]; simpa using h')
    exact (commute_of_fivePlusMap_eq_one hmap1 (m : GL (Fin 5) (ZMod 5))).symm.eq
  · intro k hk
    rw [Subgroup.mem_center_iff] at hk
    haveI : IsSimpleGroup FiveSquareFrameGeneration.derived :=
      FiveSquareFrameGeneration.derived_isSimpleGroup
    have hcenter : fivePlusHom k ∈ Subgroup.center FiveSquareFrameGeneration.derived := by
      rw [Subgroup.mem_center_iff]
      intro d
      obtain ⟨m, rfl⟩ := fivePlusHom_surjective d
      simp only [← map_mul]
      exact congrArg fivePlusHom (hk m)
    have hbot : Subgroup.center FiveSquareFrameGeneration.derived = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center FiveSquareFrameGeneration.derived) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := FiveSquareModel.exists_noncommuting_derived
        have ha : a ∈ Subgroup.center FiveSquareFrameGeneration.derived := by
          rw [h]
          exact Subgroup.mem_top a
        exact hab ((Subgroup.mem_center_iff.mp ha) b).symm
    rw [hbot] at hcenter
    exact Subgroup.mem_bot.mp hcenter

theorem exists_fivePlusEquiv :
    ∃ e : (fiveReflectionGroup 4 true true ⧸ Subgroup.center (fiveReflectionGroup 4 true true)) ≃*
      FiveSquareFrameGeneration.derived,
      ∀ g, e (QuotientGroup.mk g) = fivePlusHom g := by
  refine ⟨(QuotientGroup.quotientMulEquivOfEq ker_fivePlusHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective fivePlusHom fivePlusHom_surjective), ?_⟩
  intro g
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk fivePlusHom g

end CFSG.OddTranspositions.PartThree
