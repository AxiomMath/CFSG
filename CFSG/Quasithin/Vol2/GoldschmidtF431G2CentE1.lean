module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentWeyl

public section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2]

theorem mem_rootSpan_singleton_iff {δ : Fin Tag.G2.rank → ℤ} {y : ModGL Tag.G2 K} :
    y ∈ rootSpan Tag.G2 K {δ} ↔ ∃ s : K, y = pinnedX Tag.G2 K δ s := by
  constructor
  · intro hy
    have h : rootSpan Tag.G2 K {δ} = rootSubgroup Tag.G2 K δ := by
      simp [rootSpan]
    rw [h] at hy
    obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hy
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact pinnedX_mem_rootSpan (Set.mem_singleton _) s

theorem conj_mem_rootSpan_image {w : WeylGroup Tag.G2} {δ : Fin Tag.G2.rank → ℤ}
    (hδ : IsRoot Tag.G2 δ) {x : ModGL Tag.G2 K} (hx : x ∈ rootSpan Tag.G2 K {δ}) :
    canonicalRep (coxeterSystem Tag.G2) K w * x * (canonicalRep (coxeterSystem Tag.G2) K w)⁻¹ ∈
      rootSpan Tag.G2 K {w • δ} := by
  have h := (canonical_weyl_root_transport Tag.G2 K).1 w {δ} (by simpa using hδ)
  rw [Set.image_singleton] at h
  rw [← h]
  exact Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem cent_gX_c_le {s : K} (hs : s ≠ 0) {g : ModGL Tag.G2 K}
    (hg : g ∈ adjointGroup Tag.G2 K) (hgc : g * gX rC s = gX rC s * g) :
    g ∈ parabolicSubgroup Tag.G2 K {i1} := by
  have hg' : g ∈ ⋃ w, bruhatCell Tag.G2 K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem Tag.G2) K w with hn
  set x : ModGL Tag.G2 K := gX rC s with hx
  have hx1 : x ≠ 1 := fun h => hs (gX_eq_one h)
  have hxTC : x ∈ rootSpan Tag.G2 K TC := pinnedX_mem_rootSpan (Set.mem_singleton _) s
  have hnorm : ∀ b ∈ borelGroup Tag.G2 K, b * x * b⁻¹ ∈ rootSpan Tag.G2 K TC := fun b hb =>
    (Subgroup.mem_normalizer_iff.1 (borel_le_normalizer_TC hb) x).1 hxTC
  have hx₂ : b₂ * x * b₂⁻¹ ∈ rootSpan Tag.G2 K TC := hnorm b₂ hb₂
  have hx₂1 : b₂ * x * b₂⁻¹ ≠ 1 := fun h => hx1 (by
    have := congrArg (fun m => b₂⁻¹ * m * b₂) h
    simpa [mul_assoc] using this)
  have hy : n * (b₂ * x * b₂⁻¹) * n⁻¹ = b₁⁻¹ * x * b₁ := by
    have h1 : b₁ * n * b₂ * x * (b₁ * n * b₂)⁻¹ = x := by
      rw [hgc, mul_inv_cancel_right]
    calc n * (b₂ * x * b₂⁻¹) * n⁻¹
        = b₁⁻¹ * (b₁ * n * b₂ * x * (b₁ * n * b₂)⁻¹) * b₁ := by group
      _ = b₁⁻¹ * x * b₁ := by rw [h1]
  have hyTC : b₁⁻¹ * x * b₁ ∈ rootSpan Tag.G2 K TC := by
    have := hnorm b₁⁻¹ (inv_mem hb₁)
    simpa using this
  have hy1 : b₁⁻¹ * x * b₁ ≠ 1 := fun h => hx1 (by
    have := congrArg (fun m => b₁ * m * b₁⁻¹) h
    simpa [mul_assoc] using this)
  have hrc : IsRoot Tag.G2 rC := (pos_TC rC (Set.mem_singleton _)).1
  have hwc : IsRoot Tag.G2 (w • rC) := IsRoot.smul hrc w
  have hyw : b₁⁻¹ * x * b₁ ∈ rootSpan Tag.G2 K {w • rC} := by
    rw [← hy]
    refine conj_mem_rootSpan_image hrc ?_
    show b₂ * x * b₂⁻¹ ∈ rootSpan Tag.G2 K {rC}
    exact hx₂
  obtain ⟨s₁, hs₁⟩ := mem_rootSpan_singleton_iff.1 hyw
  obtain ⟨s₂, hs₂⟩ := (mem_rootSpan_TC_iff).1 hyTC
  have hwc_eq : w • rC = rC := by
    by_contra hne
    rcases IsRoot.height_pos_or_neg hwc with hpos | hneg
    ·
      have := pinnedX_eq_pinnedX_of_ne (K := K) ⟨hwc, hpos⟩ (pos_TC rC (Set.mem_singleton _))
        hne (s := s₁) (s' := s₂) (hs₁.symm.trans hs₂)
      apply hy1
      rw [hs₁, this.1]
      exact pinnedX_zero Tag.G2 K _
    ·
      have hneg' : b₁⁻¹ * x * b₁ ∈ negUnipotent Tag.G2 K := by
        refine rootSpan_le_negUnipotent (S := {w • rC}) (fun α hα => ?_) hyw
        rw [Set.mem_singleton_iff] at hα
        subst hα
        exact ⟨hwc, hneg⟩
      have hle : posUnipotent Tag.G2 K ≤ borelGroup Tag.G2 K := le_sup_right
      have hB : b₁⁻¹ * x * b₁ ∈ borelGroup Tag.G2 K :=
        hle (rootSpan_le_posUnipotent (S := TC) pos_TC hyTC)
      have : b₁⁻¹ * x * b₁ ∈ borelGroup Tag.G2 K ⊓ negUnipotent Tag.G2 K := ⟨hB, hneg'⟩
      rw [borelGroup_inf_negUnipotent] at this
      exact hy1 (Subgroup.mem_bot.1 this)
  have hwJ : w ∈ parabolicWeylGroup Tag.G2 ({i1} : Set (Fin Tag.G2.rank)) :=
    (mem_parabolicWeylGroup_of_coord (A := {i1}) _ w rfl (weyl_fixes_c hwc_eq)).1
  exact bruhatCell_subset_parabolicSubgroup hwJ hw

end CFSG.Quasithin.H13.F431.G2.Cent
