module

public import CFSG.Timmesfeld.ARS.BasicTwoGroup
public import CFSG.Timmesfeld.ARS.Sec4Defs

public section

namespace CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

theorem mem_inter_conjSet_of_conjSub_eq {Δ : Set (Subgroup G)} {A : Subgroup G} (hA : A ∈ Δ)
    {g : G} (hg : conjSub A g = A) : A ∈ Δ ∩ conjSet Δ g :=
  ⟨hA, hg ▸ conjSub_mem_conjSet hA g⟩

theorem mem_stabSet_of_subset {Δ : Set (Subgroup G)} {g : G} (h : Δ ⊆ conjSet Δ g)
    (h' : Δ ⊆ conjSet Δ g⁻¹) : g ∈ stabSet Δ := by
  refine Set.Subset.antisymm ?_ h
  have := Set.image_mono (f := fun B => conjSub B g) h'
  rwa [show (fun B => conjSub B g) '' conjSet Δ g⁻¹ = conjSet (conjSet Δ g⁻¹) g from rfl,
    ← conjSet_mul, mul_inv_cancel, conjSet_one] at this

theorem mem_stabSet_of_isTI {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ) {g : G}
    (hne : (Δ ∩ conjSet Δ g).Nonempty) : g ∈ stabSet Δ := by
  have hsub : ∀ x : G, (Δ ∩ conjSet Δ x).Nonempty → Δ ⊆ conjSet Δ x := fun x hx => by
    rcases hΔ.2.2.2 x with h | h
    · rw [h] at hx
      exact absurd hx Set.not_nonempty_empty
    · exact fun B hB => (h.symm ▸ hB : B ∈ Δ ∩ conjSet Δ x).2
  refine mem_stabSet_of_subset (hsub g hne) (hsub g⁻¹ ?_)
  obtain ⟨B, hB, hBg⟩ := hne
  refine ⟨conjSub B g⁻¹, (mem_conjSet).1 hBg, ?_⟩
  rw [mem_conjSet, inv_inv, ← conjSub_mul, mul_inv_cancel, conjSub_one]
  exact hB

theorem isTI_conjSub_image (hR : IsRootClass R) {A : Subgroup G} (hA : A ∈ R) {H : Subgroup G}
    (hNH : Subgroup.normalizer (A : Set G) ≤ H) (hH : H ≠ ⊤) {h : G} (hh : h ∈ H)
    (hAh : conjSub A h ≠ A) : IsTI R ((fun x => conjSub A x) '' (H : Set G)) := by
  set Δ := (fun x => conjSub A x) '' (H : Set G) with hΔ
  have hkey : ∀ g : G, (Δ ∩ conjSet Δ g).Nonempty → g ∈ H := by
    rintro g ⟨X, ⟨h₁, hh₁, rfl⟩, hX⟩
    obtain ⟨Y, ⟨h₂, hh₂, rfl⟩, hY⟩ := hX
    have hY' : conjSub A h₁ = conjSub A (g * h₂) := by
      rw [conjSub_mul]
      exact hY.symm
    have hn : h₂⁻¹ * g⁻¹ * h₁ ∈ Subgroup.normalizer (A : Set G) := by
      rw [← conjSub_eq_self_iff, conjSub_mul, hY', ← conjSub_mul,
        show h₂⁻¹ * g⁻¹ * (g * h₂) = 1 by group, conjSub_one]
    have := H.mul_mem (H.mul_mem hh₂ (hNH hn)) (H.inv_mem hh₁)
    rw [show h₂ * (h₂⁻¹ * g⁻¹ * h₁) * h₁⁻¹ = g⁻¹ by group] at this
    simpa using H.inv_mem this
  have hstab : ∀ g ∈ H, conjSet Δ g = Δ := by
    intro g hg
    ext X
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨g * x, H.mul_mem hg hx, conjSub_mul A g x⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨conjSub A (g⁻¹ * x), ⟨g⁻¹ * x, H.mul_mem (H.inv_mem hg) hx, rfl⟩, ?_⟩
      change conjSub (conjSub A (g⁻¹ * x)) g = conjSub A x
      rw [← conjSub_mul, mul_inv_cancel_left]
  refine ⟨?_, ⟨A, ⟨1, H.one_mem, conjSub_one A⟩, _, ⟨h, hh, rfl⟩, Ne.symm hAh⟩, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hR.conjSub_mem hA x
  · intro hΔR
    apply hH
    refine eq_top_iff.2 fun g _ => ?_
    have hmem : conjSub A g ∈ Δ := hΔR ▸ hR.conjSub_mem hA g
    obtain ⟨x, hx, hxg⟩ := hmem
    have hn : x⁻¹ * g ∈ Subgroup.normalizer (A : Set G) := by
      rw [← conjSub_eq_self_iff, conjSub_mul]
      change conjSub A x = conjSub A g at hxg
      rw [← hxg, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have := H.mul_mem hx (hNH hn)
    rwa [mul_inv_cancel_left] at this
  · intro g
    by_cases hne : (Δ ∩ conjSet Δ g).Nonempty
    · right
      rw [hstab g (hkey g hne), Set.inter_self]
    · left
      exact Set.not_nonempty_iff_eq_empty.1 hne

theorem exists_isTI_iff_of (hR : IsRootClass R) {A : Subgroup G} (hA : A ∈ R)
    (h2 : ∃ B ∈ R, B ≠ A) :
    ¬ IsCoatom (Subgroup.normalizer (A : Set G)) ↔ ∃ Δ, IsTI R Δ ∧ A ∈ Δ := by
  set N := Subgroup.normalizer (A : Set G) with hNdef
  have hNtop : N ≠ ⊤ := by
    intro hN
    obtain ⟨B, hB, hBA⟩ := h2
    obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hB
    have hg : g ∈ N := by
      rw [hN]
      exact Subgroup.mem_top g
    exact hBA (conjSub_eq_self_iff.2 hg)
  constructor
  · intro hco
    obtain ⟨H, hNH, hH⟩ : ∃ H, N < H ∧ H ≠ ⊤ := by
      by_contra! hall
      exact hco ⟨hNtop, fun H hH => hall H hH⟩
    obtain ⟨h, hh, hhN⟩ := IsConcreteLE.exists_of_lt hNH
    refine ⟨_, isTI_conjSub_image hR hA hNH.le hH hh fun e => hhN (conjSub_eq_self_iff.1 e),
      1, H.one_mem, conjSub_one A⟩
  · rintro ⟨Δ, hΔ, hAΔ⟩ hco
    have hNS : N ≤ stabSet Δ := fun g hg =>
      mem_stabSet_of_isTI hΔ ⟨A, mem_inter_conjSet_of_conjSub_eq hAΔ (conjSub_eq_self_iff.2 hg)⟩
    obtain ⟨B, hB, B', hB', hBB'⟩ := hΔ.2.1
    obtain ⟨C, hC, hCA⟩ : ∃ C ∈ Δ, C ≠ A := by
      by_cases h : B = A
      · exact ⟨B', hB', fun e => hBB' (h.trans e.symm)⟩
      · exact ⟨B, hB, h⟩
    obtain ⟨g, hg⟩ := hR.exists_conjSub_eq hA (hΔ.1 hC)
    have hgS : g ∈ stabSet Δ := mem_stabSet_of_isTI hΔ ⟨C, hC, hg ▸ conjSub_mem_conjSet hAΔ g⟩
    have hgN : g ∉ N := fun hgN => hCA (hg ▸ conjSub_eq_self_iff.2 hgN)
    have hlt : N < stabSet Δ := lt_of_le_of_ne hNS fun e => hgN (e ▸ hgS)
    have hStop : stabSet Δ ≠ ⊤ := by
      intro htop
      apply hΔ.2.2.1
      refine Set.Subset.antisymm hΔ.1 fun X hX => ?_
      obtain ⟨x, rfl⟩ := hR.exists_conjSub_eq hA hX
      have hx : conjSet Δ x = Δ := mem_stabSet.1 (by rw [htop]; exact Subgroup.mem_top x)
      rw [← hx]
      exact conjSub_mem_conjSet hAΔ x
    exact hStop (hco.2 _ hlt)

end Sec5

theorem exists_isTI_iff (h : Hyp G R) {A : Subgroup G} (hA : A ∈ R) :
    ¬ IsCoatom (Subgroup.normalizer (A : Set G)) ↔ ∃ Δ, IsTI R Δ ∧ A ∈ Δ := by
  refine Sec5.exists_isTI_iff_of h.root hA ?_
  obtain ⟨E, hE, F, hF, hEF⟩ := h.nondeg
  by_cases hEA : E = A
  · exact ⟨F, hF, fun e => hEF.ne h.root hE (hEA.trans e.symm)⟩
  · exact ⟨E, hE, hEA⟩

end CFSG.Timmesfeld.ARS
