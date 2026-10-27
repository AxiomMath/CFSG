module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenSylow
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem conjSub_kerMOf_of_mem {M H : Subgroup G} {m : G} (hm : m ∈ H) :
    A1b.conjSub m (kerMOf M H) = kerMOf M H :=
  B6.conjSub_eq_self (E1.mem_normalizer_of_conj_mem fun _ hx => conj_mem_kerMOf hm hx)

theorem kerMOf_conjSub_of_mem {M H : Subgroup G} {m : G} (hm : m ∈ M) :
    kerMOf M (A1b.conjSub m H) = A1b.conjSub m (kerMOf M H) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxH, hall⟩ := mem_kerMOf_iff.1 hx
    rw [A1b.mem_conjSub_iff] at hxH
    rw [A1b.mem_conjSub_iff, mem_kerMOf_iff]
    refine ⟨hxH, fun g hg => ?_⟩
    have hg' : m * g * m⁻¹ ∈ A1b.conjSub m H := A1b.mem_conjSub_of_mem hg
    have h1 := hall _ hg'
    have h2 : m⁻¹ * ((m * g * m⁻¹) * x * (m * g * m⁻¹)⁻¹) * m ∈ M :=
      M.mul_mem (M.mul_mem (M.inv_mem hm) h1) hm
    have e : m⁻¹ * ((m * g * m⁻¹) * x * (m * g * m⁻¹)⁻¹) * m =
        g * (m⁻¹ * x * m) * g⁻¹ := by
      group
    rwa [e] at h2
  · intro hx
    rw [A1b.mem_conjSub_iff, mem_kerMOf_iff] at hx
    obtain ⟨hxH, hall⟩ := hx
    rw [mem_kerMOf_iff]
    refine ⟨A1b.mem_conjSub_iff.2 hxH, fun g hg => ?_⟩
    rw [A1b.mem_conjSub_iff] at hg
    have h1 := hall _ hg
    have h2 : m * ((m⁻¹ * g * m) * (m⁻¹ * x * m) * (m⁻¹ * g * m)⁻¹) * m⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem hm h1) (M.inv_mem hm)
    have e : m * ((m⁻¹ * g * m) * (m⁻¹ * x * m) * (m⁻¹ * g * m)⁻¹) * m⁻¹ =
        g * x * g⁻¹ := by
      group
    rwa [e] at h2

theorem FiveTenConc.exists_le_sylow {H M T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (hT : IsSylowIn 2 T H) (hTM : T ≤ M) (h : FiveTenConc H M Ω) :
    ∃ A ∈ Ω, A ≤ T ∧ ∃ H' : Subgroup G, H' ≤ H ∧ A ≤ H' ∧ kerMOf M H ≤ kerMOf M H' ∧
      ¬ A ≤ kerMOf M H' ∧ maxOver H' (A ⊔ kerMOf M H') = {M ⊓ H'} := by
  obtain ⟨A, hA, hAM, H', hH'H, hAH', hker, hnot, hmax⟩ := h
  have hAH : A ≤ H := hAH'.trans hH'H
  obtain ⟨m, hm, hmA⟩ := exists_conjSub_le_of_isSylowIn hT hTM
    (hΩ.isElemAbelian A hA).isPGroup hAM hAH
  have hmM : m ∈ M := (Subgroup.mem_inf.1 hm).1
  have hmH : m ∈ H := (Subgroup.mem_inf.1 hm).2
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  have hcH : A1b.conjSub m H = H := B6.conjSub_eq_self (Subgroup.le_normalizer hmH)
  have hcM : A1b.conjSub m M = M := B6.conjSub_eq_self (Subgroup.le_normalizer hmM)
  refine ⟨A1b.conjSub m A, hΩ.conj A hA m hmH, hmA, A1b.conjSub m H', ?_, ?_, ?_, ?_, ?_⟩
  · calc A1b.conjSub m H' ≤ A1b.conjSub m H := A1b.conjSub_mono m hH'H
      _ = H := hcH
  · exact A1b.conjSub_mono m hAH'
  · rw [kerMOf_conjSub_of_mem hmM, ← conjSub_kerMOf_of_mem (M := M) hmH]
    exact A1b.conjSub_mono m hker
  · intro hle
    rw [kerMOf_conjSub_of_mem hmM] at hle
    apply hnot
    have h1 := A1b.conjSub_mono m⁻¹ hle
    rwa [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one, ← A1b.conjSub_mul,
      inv_mul_cancel, A1b.conjSub_one] at h1
  · have h1 : A1b.conjSub m A ⊔ kerMOf M (A1b.conjSub m H') =
        A1b.conjSub m (A ⊔ kerMOf M H') := by
      rw [kerMOf_conjSub_of_mem hmM]
      exact (Subgroup.map_sup _ _ _).symm
    rw [h1]
    have h2 := maxOver_conjSub (g := m) (U := H') (X := A ⊔ kerMOf M H')
    rw [hmax, Set.image_singleton] at h2
    have h3 : B6.conjSub m (M ⊓ H') = M ⊓ A1b.conjSub m H' := by
      have : A1b.conjSub m (M ⊓ H') = A1b.conjSub m M ⊓ A1b.conjSub m H' :=
        Subgroup.map_inf _ _ _ hinj
      rw [hcM] at this
      exact this
    rw [h3] at h2
    exact h2

theorem maxOver_kerQuotImg_of_inf {M H A : Subgroup G} (hAH : A ≤ H)
    (h : maxOver H (A ⊔ kerMOf M H) = {M ⊓ H}) :
    maxOver ⊤ (kerQuotImg M H A) = {kerQuotImg M H M} := by
  have hlift_top : kerQuotLift M H (⊤ : Subgroup (KerQuot M H)) = H := by
    ext x
    rw [mem_kerQuotLift_iff]
    exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, Subgroup.mem_top _⟩⟩
  have key : ∀ Y : Subgroup (KerQuot M H), Y ∈ maxOver ⊤ (kerQuotImg M H A) ↔
      kerQuotLift M H Y ∈ maxOver H (A ⊔ kerMOf M H) := by
    intro Y
    have e : IsMaxSubgroupIn H (kerQuotLift M H Y) ↔ IsMaxSubgroupIn ⊤ Y := by
      have := isMaxSubgroupIn_kerQuotLift (M := M) (H := H) (Y := ⊤) (N := Y)
      rwa [hlift_top] at this
    have e2 : A ⊔ kerMOf M H ≤ kerQuotLift M H Y ↔ kerQuotImg M H A ≤ Y := by
      rw [sup_le_iff, le_kerQuotLift_iff hAH]
      exact ⟨fun h => h.1, fun h => ⟨h, kerMOf_le_kerQuotLift M H Y⟩⟩
    simp only [maxOver, Set.mem_setOf_eq, e, e2]
  ext Y
  rw [key, h, Set.mem_singleton_iff, Set.mem_singleton_iff]
  constructor
  · intro hY
    refine le_antisymm ?_ ?_
    · exact kerQuotLift_le_kerQuotLift_iff.1 (hY.le.trans (kerQuotLift_kerQuotImg_left M H).ge)
    · exact kerQuotLift_le_kerQuotLift_iff.1 ((kerQuotLift_kerQuotImg_left M H).le.trans hY.ge)
  · rintro rfl
    exact kerQuotLift_kerQuotImg_left M H

end CFSG.LocalAnalysis.WeakClosure81
