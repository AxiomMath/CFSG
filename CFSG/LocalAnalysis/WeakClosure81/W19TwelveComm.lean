module

public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

private lemma mul_inv_mem_of_notMem_of_index_two {A : Type*} [Group A] {K : Subgroup A}
    (hK : K.index = 2) {x y : A} (hx : x ∉ K) (hy : y ∉ K) : x * y⁻¹ ∈ K := by
  rw [Subgroup.mul_mem_iff_of_index_two hK]
  exact iff_of_false hx (mt (inv_mem_iff (x := y)).mp hy)

theorem commutator_mem_of_card_four {I V₀ : Subgroup G} {t : G} (hI : Nat.card I = 4)
    (hV : Nat.card V₀ = 2) (hVI : V₀ ≤ I) (htI : t ∈ normalizer (I : Set G))
    (htV : t ∈ normalizer (V₀ : Set G)) : ∀ a ∈ I, ⁅a, t⁆ ∈ V₀ := by
  have hcardV : Nat.card (V₀.subgroupOf I) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVI).toEquiv, hV]
  have hVidx : (V₀.subgroupOf I).index = 2 := by
    have h := Subgroup.card_mul_index (H := V₀.subgroupOf I)
    rw [hcardV, hI] at h
    omega
  intro a ha
  have hb : t * a * t⁻¹ ∈ I := (Subgroup.mem_set_normalizer_iff.mp htI a).mp ha
  have hmem : (⟨a, ha⟩ : I) * (⟨t * a * t⁻¹, hb⟩ : I)⁻¹ ∈ V₀.subgroupOf I := by
    by_cases haV : (⟨a, ha⟩ : I) ∈ V₀.subgroupOf I
    · have hbV : (⟨t * a * t⁻¹, hb⟩ : I) ∈ V₀.subgroupOf I := by
        rw [Subgroup.mem_subgroupOf] at haV ⊢
        exact (Subgroup.mem_set_normalizer_iff.mp htV a).mp haV
      exact (V₀.subgroupOf I).mul_mem haV ((V₀.subgroupOf I).inv_mem hbV)
    · have hbV : (⟨t * a * t⁻¹, hb⟩ : I) ∉ V₀.subgroupOf I := by
        intro hbV
        apply haV
        rw [Subgroup.mem_subgroupOf] at hbV ⊢
        have h1 : t⁻¹ * (t * a * t⁻¹) * t ∈ V₀ := by
          simpa using
            (Subgroup.mem_set_normalizer_iff.mp (inv_mem htV) (t * a * t⁻¹)).mp hbV
        have h2 : t⁻¹ * (t * a * t⁻¹) * t = a := by group
        rwa [h2] at h1
      exact mul_inv_mem_of_notMem_of_index_two hVidx haV hbV
  rw [Subgroup.mem_subgroupOf] at hmem
  have hcoe : (((⟨a, ha⟩ : I) * (⟨t * a * t⁻¹, hb⟩ : I)⁻¹ : I) : G) = ⁅a, t⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, commutatorElement_def]
    group
  simpa [hcoe] using hmem

theorem commutator_mem_of_mem_conjClosure {H O I V₀ : Subgroup G} (hIH : I ≤ H)
    (hOn : ∀ h ∈ H, ∀ o ∈ O, h⁻¹ * o * h ∈ O) (hV₀ : ∀ h ∈ H, ∀ v ∈ V₀, h * v = v * h)
    (hIO : ∀ a ∈ I, ∀ o ∈ O, ⁅a, o⁆ ∈ V₀) :
    ∀ e ∈ CFSG.Quasithin.conjClosure I H, ∀ o ∈ O, ⁅e, o⁆ ∈ V₀ := by
  intro e he
  rw [CFSG.Quasithin.conjClosure] at he
  refine Subgroup.closure_induction (p := fun e _ => ∀ o ∈ O, ⁅e, o⁆ ∈ V₀) ?_ ?_ ?_ ?_ he
  · rintro x ⟨h, hh, z, hz, rfl⟩ o ho
    have hw : ⁅z, h⁻¹ * o * h⁆ ∈ V₀ := hIO z hz (h⁻¹ * o * h) (hOn h hh o ho)
    have key : ⁅h * z * h⁻¹, o⁆ = h * ⁅z, h⁻¹ * o * h⁆ * h⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    have hfix : h * ⁅z, h⁻¹ * o * h⁆ * h⁻¹ = ⁅z, h⁻¹ * o * h⁆ := by
      rw [hV₀ h hh _ hw]
      group
    rw [hfix]
    exact hw
  · intro o _
    simpa using (V₀.one_mem)
  · intro x y hx hy ihx ihy o ho
    have hxH : x ∈ H :=
      conjClosure_le_of_le hIH (show x ∈ CFSG.Quasithin.conjClosure I H from hx)
    have hw₂ : ⁅y, o⁆ ∈ V₀ := ihy o ho
    have hw₁ : ⁅x, o⁆ ∈ V₀ := ihx o ho
    have key : ⁅x * y, o⁆ = x * ⁅y, o⁆ * x⁻¹ * ⁅x, o⁆ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    have hfix : x * ⁅y, o⁆ * x⁻¹ = ⁅y, o⁆ := by
      rw [hV₀ x hxH _ hw₂]
      group
    rw [hfix]
    exact V₀.mul_mem hw₂ hw₁
  · intro x hx ih o ho
    have hxH : x ∈ H :=
      conjClosure_le_of_le hIH (show x ∈ CFSG.Quasithin.conjClosure I H from hx)
    have hw : ⁅x, o⁆ ∈ V₀ := ih o ho
    have key : ⁅x⁻¹, o⁆ = x⁻¹ * ⁅x, o⁆⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [key]
    have hfix : x⁻¹ * ⁅x, o⁆⁻¹ * x = ⁅x, o⁆⁻¹ := by
      rw [hV₀ x⁻¹ (H.inv_mem hxH) _ (V₀.inv_mem hw)]
      group
    rw [hfix]
    exact V₀.inv_mem hw

end CFSG.LocalAnalysis.WeakClosure81

end
