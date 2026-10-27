module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenApi

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

private def oTwoSetN (N K : Subgroup G) : Set (Subgroup G) :=
  {W | N ≤ W ∧ W ≤ K ∧ (W.subgroupOf K).Normal ∧ ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ N}

private theorem oTwoMod_eq_iSup_N (N K : Subgroup G) :
    oTwoMod N K = ⨆ W ∈ oTwoSetN N K, W := rfl

private theorem conj_mem_oTwoSetN {N K : Subgroup G} {h : G}
    (hhN : h ∈ Subgroup.normalizer (N : Set G))
    (hhK : h ∈ Subgroup.normalizer (K : Set G))
    {W : Subgroup G} (hW : W ∈ oTwoSetN N K) : conjSubgroup W h ∈ oTwoSetN N K := by
  have hleK : conjSubgroup W h ≤ K := by
    calc conjSubgroup W h ≤ conjSubgroup K h := Subgroup.map_mono hW.2.1
      _ = K := conjSubgroup_eq_iff_mem_normalizer.mpr hhK
  refine ⟨?_, hleK, ?_, ?_⟩
  · calc N = conjSubgroup N h := (conjSubgroup_eq_iff_mem_normalizer.mpr hhN).symm
      _ ≤ conjSubgroup W h := Subgroup.map_mono hW.1
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hleK]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [mem_conjSubgroup_iff] at hx ⊢
      have hkK : h * k * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hhK k).1 hk
      have hWnorm : K ≤ Subgroup.normalizer (W : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hW.2.1).mp hW.2.2.1
      have hconj : (h * k * h⁻¹) * (h * x * h⁻¹) * (h * k * h⁻¹)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hWnorm hkK) (h * x * h⁻¹)).1 hx
      simpa [mul_assoc] using hconj
    · intro hx
      rw [mem_conjSubgroup_iff] at hx ⊢
      have hkK : h * k * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hhK k).1 hk
      have hWnorm : K ≤ Subgroup.normalizer (W : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hW.2.1).mp hW.2.2.1
      exact (Subgroup.mem_normalizer_iff.mp (hWnorm hkK) (h * x * h⁻¹)).2
        (by simpa [mul_assoc] using hx)
  · intro w' hw'
    rw [mem_conjSubgroup_iff] at hw'
    obtain ⟨k, hk⟩ := hW.2.2.2 (h * w' * h⁻¹) hw'
    refine ⟨k, ?_⟩
    rw [← conjSubgroup_eq_iff_mem_normalizer.mpr hhN, mem_conjSubgroup_iff, ← conj_pow]
    exact hk

private theorem normalizer_oTwoModN {N K : Subgroup G} :
    Subgroup.normalizer (N : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (oTwoMod N K : Set G) := by
  have hsup : (⨆ x : oTwoSetN N K, (x : Subgroup G)) = oTwoMod N K :=
    (iSup_subtype'' (oTwoSetN N K) id).trans (oTwoMod_eq_iSup_N N K).symm
  have key : ∀ h ∈ Subgroup.normalizer (N : Set G),
      h ∈ Subgroup.normalizer (K : Set G) → ∀ x ∈ oTwoMod N K, h * x * h⁻¹ ∈ oTwoMod N K := by
    intro h hhN hhK x hx
    have hhN' : h⁻¹ ∈ Subgroup.normalizer (N : Set G) := (Subgroup.normalizer _).inv_mem hhN
    have hhK' : h⁻¹ ∈ Subgroup.normalizer (K : Set G) := (Subgroup.normalizer _).inv_mem hhK
    have hx' : x ∈ ⨆ W : oTwoSetN N K, (W : Subgroup G) := by rwa [hsup]
    have hgoal : h * x * h⁻¹ ∈ ⨆ W : oTwoSetN N K, (W : Subgroup G) := by
      refine Subgroup.iSup_induction (fun W : oTwoSetN N K => (W : Subgroup G))
        (C := fun a => h * a * h⁻¹ ∈ ⨆ W : oTwoSetN N K, (W : Subgroup G)) hx' ?_ ?_ ?_
      · intro W a haW
        have hWmem : conjSubgroup (W : Subgroup G) h⁻¹ ∈ oTwoSetN N K :=
          conj_mem_oTwoSetN hhN' hhK' W.2
        have hmem : h * a * h⁻¹ ∈ conjSubgroup (W : Subgroup G) h⁻¹ := by
          rw [mem_conjSubgroup_iff]
          have heq : h⁻¹ * (h * a * h⁻¹) * h⁻¹⁻¹ = a := by group
          rwa [heq]
        exact Subgroup.mem_iSup_of_mem ⟨conjSubgroup (W : Subgroup G) h⁻¹, hWmem⟩ hmem
      · simpa using Subgroup.one_mem (⨆ W : oTwoSetN N K, (W : Subgroup G))
      · intro a b ha hb
        rw [show h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) by group]
        exact (⨆ W : oTwoSetN N K, (W : Subgroup G)).mul_mem ha hb
    rwa [hsup] at hgoal
  intro g hg
  obtain ⟨hgN, hgK⟩ := Subgroup.mem_inf.mp hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact key g hgN hgK x hx
  · intro hx
    have h := key g⁻¹ ((Subgroup.normalizer _).inv_mem hgN) ((Subgroup.normalizer _).inv_mem hgK)
      (g * x * g⁻¹) hx
    simpa [mul_assoc] using h

theorem Sit813.a_le_normalizer_oTwoMod {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : A ≤ normalizer (oTwoMod (cGrp H T) K : Set G) := by
  have hyp := h.minCex.hyp
  have hAH : A ≤ H := h.mem.1.trans (isSylowIn_of_isCalH h.calH0.1 hyp.sylow).le
  exact fun a ha => normalizer_oTwoModN (Subgroup.mem_inf.mpr
    ⟨h.le_normalizer_cGrp (hAH ha), Sit813.a_le_normalizer h ha⟩)

end CFSG.LocalAnalysis.WeakClosure81

end
