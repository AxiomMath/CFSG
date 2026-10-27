module

public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.Open.StatedDefs
import CFSG.OddTranspositions.PartThree.Eleven.Five.Equiv
import CFSG.OddTranspositions.PartThree.Eleven.Five.Central
import CFSG.ClassicalGroups.Orthogonal.FiveSquareModel
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.GroupTheory.CentralizerMapMulEquiv

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.ClassicalGroups.Orthogonal

theorem isFiveReflectionModel_four_true_true_of_psp {G : Type} [Group G] [Finite G] (u : G)
    (hu : orderOf u = 2) (hPSp : CFSG.Open.StatedClassicalModel G .PSp 2 5 1)
    (h64 : 64 ∣ Nat.card (Subgroup.centralizer {u})) :
    IsFiveReflectionModel 4 true true {g | IsConj u g} := by
  unfold IsFiveReflectionModel CFSG.Open.fischerCentralQuotientModel
  have hΩ : CFSG.Open.StatedClassicalModel FiveSquareFrameGeneration.derived .PSp 2 5 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num)
      CFSG.ClassicalGroups.Orthogonal.FiveSquareModel.lieModel_derived
  obtain ⟨ψG⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hPSp hΩ
  obtain ⟨e, he⟩ := exists_fivePlusEquiv
  refine ⟨ψG.trans e.symm, ?_⟩
  intro g
  rw [Set.mem_setOf_eq]
  have ht : orderOf (ψG u) = 2 := by rw [MulEquiv.orderOf_eq ψG u, hu]
  have h64ψ : 64 ∣ Nat.card
      (Subgroup.centralizer ({ψG u} : Set FiveSquareFrameGeneration.derived)) := by
    rw [← CFSG.GroupTheory.card_centralizer_singleton_mulEquiv ψG u]
    exact h64
  have hzDt : IsConj FiveSquareFrameGeneration.zD (ψG u) :=
    isConj_zD_of_dvd_card_centralizer ht h64ψ
  obtain ⟨r0, hr0T, hr0z⟩ := exists_fivePlusMap_eq_z
  have hr0H : r0 ∈ fiveReflectionGroup 4 true true := Subgroup.subset_closure hr0T
  have hψr0 : fivePlusHom ⟨r0, hr0H⟩ = FiveSquareFrameGeneration.zD := by
    apply Subtype.ext
    simpa [coe_fivePlusHom_apply] using hr0z
  constructor
  · intro hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    obtain ⟨d0, hd0⟩ := isConj_iff.mp hzDt
    have h1 : ψG c * ψG u * (ψG c)⁻¹ = ψG g := by
      rw [← hc]
      simp only [map_mul, map_inv]
    have hg_eq : ψG g =
        (ψG c * d0) * FiveSquareFrameGeneration.zD * (ψG c * d0)⁻¹ := by
      rw [← h1, ← hd0]
      group
    obtain ⟨m, hm⟩ := fivePlusHom_surjective (ψG c * d0)
    have hψh : fivePlusHom (m * ⟨r0, hr0H⟩ * m⁻¹) = ψG g := by
      simp only [map_mul, map_inv, hm, hψr0]
      exact hg_eq.symm
    refine ⟨m * ⟨r0, hr0H⟩ * m⁻¹, ?_, ?_⟩
    · have hcoe : (((m * ⟨r0, hr0H⟩ * m⁻¹ : fiveReflectionGroup 4 true true) :
          GL (Fin 5) (ZMod 5)))
          = (m : GL (Fin 5) (ZMod 5)) * r0 * (m : GL (Fin 5) (ZMod 5))⁻¹ := by
        simp
      rw [hcoe]
      exact conj_mem_fiveReflections
        (fiveForm_mulVec_of_mem (n := 4) (ε := true) (π := true) m.2) hr0T
    · apply e.injective
      change e (e.symm (ψG g)) = e (QuotientGroup.mk (m * ⟨r0, hr0H⟩ * m⁻¹))
      rw [MulEquiv.apply_symm_apply, he (m * ⟨r0, hr0H⟩ * m⁻¹)]
      exact hψh.symm
  · rintro ⟨h, hhT, hφg⟩
    have hgψ : ψG g = fivePlusHom h := by
      have h2 := congrArg e hφg
      change e (e.symm (ψG g)) = e (QuotientGroup.mk h) at h2
      rw [MulEquiv.apply_symm_apply, he h] at h2
      exact h2
    obtain ⟨m, hmH, hmconj⟩ := exists_conj_eq_of_mem_fiveReflections hhT hr0T
    have hmconjH : (⟨m, hmH⟩ : fiveReflectionGroup 4 true true) * h *
        (⟨m, hmH⟩ : fiveReflectionGroup 4 true true)⁻¹ = ⟨r0, hr0H⟩ := by
      apply Subtype.ext
      simpa using hmconj
    have key : fivePlusHom ⟨m, hmH⟩ * fivePlusHom h * (fivePlusHom ⟨m, hmH⟩)⁻¹ =
        FiveSquareFrameGeneration.zD := by
      have hthis := congrArg fivePlusHom hmconjH
      simpa only [map_mul, map_inv, hψr0] using hthis
    have hψh : fivePlusHom h = (fivePlusHom ⟨m, hmH⟩)⁻¹ *
        FiveSquareFrameGeneration.zD * fivePlusHom ⟨m, hmH⟩ := by
      rw [← key]
      group
    have hzg : IsConj FiveSquareFrameGeneration.zD (ψG g) := by
      refine isConj_iff.mpr ⟨(fivePlusHom ⟨m, hmH⟩)⁻¹, ?_⟩
      rw [inv_inv, hgψ]
      exact hψh.symm
    have hzu : IsConj (ψG u) (ψG g) := hzDt.symm.trans hzg
    have hmap := MonoidHom.map_isConj
      (ψG.symm : FiveSquareFrameGeneration.derived →* G) hzu
    simpa using hmap

end CFSG.OddTranspositions.PartThree
