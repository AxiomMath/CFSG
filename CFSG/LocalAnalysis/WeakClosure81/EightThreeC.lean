module

public import CFSG.LocalAnalysis.WeakClosure81.EightThreeB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp83

variable {V H T : Subgroup G}

theorem inf_normalizer_le_normalizer_kGen (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    H ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (kGen V H T : Set G) := by
  intro m hm
  obtain ⟨hmH, hmV⟩ := Subgroup.mem_inf.mp hm
  rw [← conjSubgroup_eq_iff_mem_normalizer, h.conjSubgroup_kGen hOmH hmH,
    conjSubgroup_eq_iff_mem_normalizer.mpr hmV, ← kGen_eq_kOrbSub]

theorem mem_omegaOrb_of_mem_normalizer_kGen (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) {x : G}
    (hx : x ∈ H ⊓ Subgroup.normalizer (kGen V H T : Set G)) :
    conjSubgroup V x ∈ omegaOrb V H T := by
  obtain ⟨hxH, hxK⟩ := Subgroup.mem_inf.mp hx
  have hΓ := h.conjSubgroup_self_mem_omegaSet hxH
  obtain ⟨-, -, hE, -⟩ := mem_omegaSet.mp hΓ
  have hKx : conjSubgroup (kGen V H T) x = kGen V H T :=
    conjSubgroup_eq_iff_mem_normalizer.mpr hxK
  have hVK : conjSubgroup V x ≤ kGen V H T :=
    calc conjSubgroup V x ≤ conjSubgroup (kGen V H T) x := Subgroup.map_mono (le_kGen_self V H T)
      _ = kGen V H T := hKx
  have hxO : x⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 (kGen V H T) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.inv_mem _ hxK)
  have hnotO : ¬ conjSubgroup V x ≤ pCoreOf 2 (kGen V H T) := by
    intro hle
    apply h.not_le_pCoreOf_kGen hOmH
    have hmap : conjSubgroup (conjSubgroup V x) x⁻¹ ≤
        conjSubgroup (pCoreOf 2 (kGen V H T)) x⁻¹ := Subgroup.map_mono hle
    rwa [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
      CFSG.Quasithin.conjSubgroup_one, conjSubgroup_eq_iff_mem_normalizer.mpr hxO] at hmap
  have hmem : conjSubgroup V x ∈ omegaSetIn V (kGen V H T) (eSub V H T) :=
    ⟨mem_omegaSet.mpr ⟨x, rfl, hE, hnotO⟩, hVK⟩
  exact h.mem_omegaOrb_of_mem_omegaSetIn hOmH hmem

theorem exists_mul_of_mem_normalizer_kGen (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) {x : G}
    (hx : x ∈ H ⊓ Subgroup.normalizer (kGen V H T : Set G)) :
    ∃ m ∈ H ⊓ Subgroup.normalizer (V : Set G), ∃ k ∈ kGen V H T, x = m * k := by
  obtain ⟨k, hk, hxk⟩ := h.kGen_transitive hOmH (h.mem_omegaOrb_of_mem_normalizer_kGen hOmH hx)
  have hm : x * k⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← CFSG.Quasithin.conjSubgroup_conjSubgroup, hxk,
      CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  exact ⟨x * k⁻¹, Subgroup.mem_inf.mpr
    ⟨H.mul_mem hx.1 (H.inv_mem (h.kGen_le_H hOmH hk)), hm⟩, k, hk, by group⟩

theorem coe_inf_normalizer_kGen (h : Hyp83 V H T)
    (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H) :
    ((H ⊓ Subgroup.normalizer (kGen V H T : Set G) : Subgroup G) : Set G) =
      (kGen V H T : Set G) * ((H ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm, k, hk, hmk⟩ := h.exists_mul_of_mem_normalizer_kGen hOmH
      ((H ⊓ Subgroup.normalizer (kGen V H T : Set G)).inv_mem hx)
    refine ⟨k⁻¹, (kGen V H T).inv_mem hk, m⁻¹, (H ⊓ Subgroup.normalizer (V : Set G)).inv_mem hm,
      ?_⟩
    show k⁻¹ * m⁻¹ = x
    rw [← mul_inv_rev, ← hmk, inv_inv]
  · rintro ⟨k, hk, m, hm, rfl⟩
    exact (H ⊓ Subgroup.normalizer (kGen V H T : Set G)).mul_mem
      ⟨h.kGen_le_H hOmH hk, Subgroup.le_normalizer hk⟩
      ⟨hm.1, h.inf_normalizer_le_normalizer_kGen hOmH hm⟩

end Hyp83

end CFSG.LocalAnalysis.WeakClosure81
