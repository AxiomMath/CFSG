module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpRoot
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactSpTau
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpFixRoot
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical

variable {k : ℕ} {F : Type} [Field F]

private theorem spUFix_spEnd_injective (g : StatedSp k F) : Function.Injective (spEnd g) := by
  intro x y h
  have h1 := congrArg (spEnd g⁻¹) h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one,
    Module.End.one_apply, Module.End.one_apply] at h1

private theorem spUFix_semilinear_of_normalForm {α : MulAut ↥(StatedSp k F)} {s : StatedSp k F}
    {σ : F ≃+* F}
    (hσ : ∀ g, α g = s * CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp k F σ g
      * s⁻¹)
    (hout : α ∉ (MulAut.conj : ↥(StatedSp k F) →* MulAut ↥(StatedSp k F)).range) :
    ∃ (σ' : F ≃+* F) (ψ : (Fin k ⊕ Fin k → F) →+ (Fin k ⊕ Fin k → F)), σ' ≠ 1 ∧
      (∀ (c : F) (v : Fin k ⊕ Fin k → F), ψ (c • v) = σ' c • ψ v) ∧ Function.Injective ψ ∧
      (∀ v w, spForm k F v w = 0 → spForm k F (ψ v) (ψ w) = 0) ∧
      ∀ v, (spUFixRootSp v).map α.toMonoidHom = spUFixRootSp (ψ v) := by
  have happ : ∀ g : ↥(StatedSp k F),
      α.toMonoidHom g = s * CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp k F σ g
        * s⁻¹ := fun g => hσ g
  have hσne : σ ≠ 1 := by
    intro h1
    refine hout ⟨s, ?_⟩
    refine MulEquiv.ext fun g => ?_
    rw [MulAut.conj_apply, hσ g, h1, map_one, MulAut.one_apply]
  have hzero : spEnd s (σ ∘ (0 : Fin k ⊕ Fin k → F)) = 0 := by
    rw [show (σ ∘ (0 : Fin k ⊕ Fin k → F)) = 0 by ext i; simp, map_zero]
  have hadd : ∀ u v : Fin k ⊕ Fin k → F,
      spEnd s (σ ∘ (u + v)) = spEnd s (σ ∘ u) + spEnd s (σ ∘ v) := by
    intro u v
    rw [show σ ∘ (u + v) = (σ ∘ u) + (σ ∘ v) by ext i; simp, map_add]
  have hsemil : ∀ (c : F) (v : Fin k ⊕ Fin k → F),
      spEnd s (σ ∘ (c • v)) = σ c • spEnd s (σ ∘ v) := by
    intro c v
    rw [show (σ ∘ (c • v)) = σ c • (σ ∘ v) by ext i; simp [Pi.smul_apply, map_mul]]
    rw [map_smul]
  have hinj : Function.Injective (fun v => spEnd s (σ ∘ v)) := by
    intro u v huv
    have h1 : σ ∘ u = σ ∘ v := spUFix_spEnd_injective s huv
    ext i
    exact σ.injective (congrFun h1 i)
  have horth : ∀ v w : Fin k ⊕ Fin k → F, spForm k F v w = 0 →
      spForm k F (spEnd s (σ ∘ v)) (spEnd s (σ ∘ w)) = 0 := by
    intro v w hvw
    rw [CFSG.RankThree.PartOne.CTP.spEnd_isometry, spForm_comp_ringEquiv, hvw, map_zero]
  have hmap : ∀ v : Fin k ⊕ Fin k → F,
      (spUFixRootSp v).map α.toMonoidHom = spUFixRootSp (spEnd s (σ ∘ v)) := by
    intro v
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [mem_spUFixRootSp] at hy ⊢
      obtain ⟨t, rfl⟩ := hy
      refine ⟨σ t, ?_⟩
      rw [happ (spTransvection v t), borel86_spr_fieldSp_spTransvection,
        CFSG.RankThree.PartOne.CTP.spTransvection_conj]
    · intro x hx
      rw [mem_spUFixRootSp] at hx
      obtain ⟨t, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := σ.surjective t
      rw [Subgroup.mem_map]
      refine ⟨spTransvection v c, mem_spUFixRootSp.mpr ⟨c, rfl⟩, ?_⟩
      rw [happ (spTransvection v c), borel86_spr_fieldSp_spTransvection,
        CFSG.RankThree.PartOne.CTP.spTransvection_conj]
  exact ⟨σ, { toFun := fun v => spEnd s (σ ∘ v), map_zero' := hzero, map_add' := hadd },
    hσne, hsemil, hinj, horth, hmap⟩

theorem spUFix_exists_semilinear_statedSp [Finite F] [CharP F 2] (hk : 2 ≤ k)
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) (α : MulAut ↥(StatedSp k F))
    (hαR : (spUFixRootSp a).map α.toMonoidHom = spUFixRootSp a)
    (hout : α ∉ (MulAut.conj : ↥(StatedSp k F) →* MulAut ↥(StatedSp k F)).range) :
    ∃ (σ : F ≃+* F) (ψ : (Fin k ⊕ Fin k → F) →+ (Fin k ⊕ Fin k → F)), σ ≠ 1 ∧
      (∀ (c : F) (v : Fin k ⊕ Fin k → F), ψ (c • v) = σ c • ψ v) ∧ Function.Injective ψ ∧
      (∀ v w, spForm k F v w = 0 → spForm k F (ψ v) (ψ w) = 0) ∧
      ∀ v, (spUFixRootSp v).map α.toMonoidHom = spUFixRootSp (ψ v) := by
  by_cases hk3 : 3 ≤ k
  · obtain ⟨s, σ, hσ⟩ := CFSG.SeitzReduction.F4Pilot.exists_eq_conj_mul_fieldSp (K := F) hk3 α
    exact spUFix_semilinear_of_normalForm hσ hout
  · obtain rfl : k = 2 := by omega
    obtain ⟨s, σ, hσ | hτ⟩ := CFSG.SeitzReduction.F4Pilot.exists_eq_conj_mul_fieldSp_tauSp α
    · exact spUFix_semilinear_of_normalForm hσ hout
    · exfalso
      have hmem : α (spTransvection a 1) ∈ spUFixRootSp a := by
        rw [← hαR]
        exact ⟨spTransvection a 1, mem_spUFixRootSp.mpr ⟨1, rfl⟩, rfl⟩
      rw [mem_spUFixRootSp] at hmem
      obtain ⟨t, ht⟩ := hmem
      exact spUFix_eq_tau_spTransvection_ne hτ ha one_ne_zero a t ht

end CFSG.LocalAnalysis.WeakClosure81

end
