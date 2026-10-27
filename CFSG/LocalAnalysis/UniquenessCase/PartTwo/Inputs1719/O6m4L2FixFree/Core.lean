module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Fixed
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Flag
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Point
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.TwoDim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open Matrix CFSG.LieType.BorelTits

private lemma singFlag_values_F10 {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {R : Subgroup ↥(Omega6 F b c)} {v : Idx → F}
    (hv0 : v ≠ 0) (hW : singSeq (Phi6 hirr) (Rep6 F b c) R 6 = Submodule.span F {v}) :
    (∀ k, singFlag (Phi6 hirr) (Rep6 F b c) R k = ⊥ ∨
      singFlag (Phi6 hirr) (Rep6 F b c) R k = singSeq (Phi6 hirr) (Rep6 F b c) R 6 ∨
      singFlag (Phi6 hirr) (Rep6 F b c) R k =
        (Phi6 hirr).polar.perp (singSeq (Phi6 hirr) (Rep6 F b c) R 6) ∨
      singFlag (Phi6 hirr) (Rep6 F b c) R k = ⊤) ∧
    singFlag (Phi6 hirr) (Rep6 F b c) R 7 =
      (Phi6 hirr).polar.perp (singSeq (Phi6 hirr) (Rep6 F b c) R 6) ∧
    singFlag (Phi6 hirr) (Rep6 F b c) R 13 = ⊤ := by
  have hfin1 : Module.finrank F ↥(singSeq (Phi6 hirr) (Rep6 F b c) R
      (Module.finrank F (Idx → F))) = 1 := by
    rw [finrank_idx F, hW, finrank_span_singleton hv0]
  have hmem : ∀ k, singFlag (Phi6 hirr) (Rep6 F b c) R k = ⊥ ∨
      singFlag (Phi6 hirr) (Rep6 F b c) R k = singSeq (Phi6 hirr) (Rep6 F b c) R 6 ∨
      singFlag (Phi6 hirr) (Rep6 F b c) R k =
        (Phi6 hirr).polar.perp (singSeq (Phi6 hirr) (Rep6 F b c) R 6) ∨
      singFlag (Phi6 hirr) (Rep6 F b c) R k = ⊤ := by
    intro k
    have h := singFlag_mem_of_finrank_eq_one (Phi6 hirr) (Rep6 F b c) R hfin1 k
    rw [finrank_idx F] at h
    exact h
  have hFl7 : singFlag (Phi6 hirr) (Rep6 F b c) R 7 =
      (Phi6 hirr).polar.perp (singSeq (Phi6 hirr) (Rep6 F b c) R 6) := by
    have h := singFlag_finrank_succ (Φ := Phi6 hirr) (ρ := Rep6 F b c) R
    rw [finrank_idx F] at h
    simpa using h
  have hFl13 : singFlag (Phi6 hirr) (Rep6 F b c) R 13 = ⊤ := by
    have h := singFlag_top (Φ := Phi6 hirr) (ρ := Rep6 F b c) R
    rw [finrank_idx F] at h
    simpa using h
  exact ⟨hmem, hFl7, hFl13⟩

private lemma sub_mem_perp_line_F10 {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {R : Subgroup ↥(Omega6 F b c)} (hR : IsPGroup 2 ↥R)
    {v : Idx → F} (hv0 : v ≠ 0)
    (hW : singSeq (Phi6 hirr) (Rep6 F b c) R 6 = Submodule.span F {v}) :
    (∀ g ∈ R, ∀ x ∈ (Phi6 hirr).polar.perp (singSeq (Phi6 hirr) (Rep6 F b c) R 6),
        Rep6 F b c g x - x ∈ singSeq (Phi6 hirr) (Rep6 F b c) R 6) ∧
      (∀ g ∈ R, ∀ x, Rep6 F b c g x - x ∈
        (Phi6 hirr).polar.perp (singSeq (Phi6 hirr) (Rep6 F b c) R 6)) := by
  obtain ⟨hmem, hFl7, hFl13⟩ := singFlag_values_F10 hirr hv0 hW
  have hFl0 : singFlag (Phi6 hirr) (Rep6 F b c) R 0 = ⊥ :=
    singFlag_zero (Phi6 hirr) (Rep6 F b c) R
  have hRle : R ≤ flagKernel (Rep6 F b c) (singFlag (Phi6 hirr) (Rep6 F b c) R) :=
    le_flagKernel_six hirr hR
  have hWiso : singSeq (Phi6 hirr) (Rep6 F b c) R 6 ≤
      (Phi6 hirr).polar.perp (singSeq (Phi6 hirr) (Rep6 F b c) R 6) :=
    (isTotallySingular_singSeq (Phi6 hirr) (Rep6 F b c) R 6).isTotallyIsotropic
  refine ⟨?_, ?_⟩
  · refine sub_mem_of_flag_dichotomy (Rep6 F b c) hFl0 ?_ ⟨7, le_of_eq hFl7.symm⟩ hRle
    intro k
    rcases hmem k with h | h | h | h
    · left; rw [h]; exact bot_le
    · left; exact le_of_eq h
    · right; exact le_of_eq h.symm
    · right; rw [h]; exact le_top
  · have hraw : ∀ g ∈ R, ∀ x ∈ (⊤ : Submodule F (Idx → F)),
        Rep6 F b c g x - x ∈ (Phi6 hirr).polar.perp (singSeq (Phi6 hirr) (Rep6 F b c) R 6) := by
      refine sub_mem_of_flag_dichotomy (Rep6 F b c) hFl0 ?_ ⟨13, le_of_eq hFl13.symm⟩ hRle
      intro k
      rcases hmem k with h | h | h | h
      · left; rw [h]; exact bot_le
      · left; rw [h]; exact hWiso
      · left; exact le_of_eq h
      · right; exact le_of_eq h.symm
    simpa [Submodule.mem_top] using hraw

theorem card_le_of_singSeq_line {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {R : Subgroup ↥(Omega6 F b c)} (hR : IsPGroup 2 ↥R)
    {v : Idx → F} (hv0 : v ≠ 0)
    (hW : singSeq (Phi6 hirr) (Rep6 F b c) R 6 = Submodule.span F {v}) :
    Nat.card ↥R ≤ Nat.card F ^ 4 := by
  obtain ⟨h2, h3⟩ := sub_mem_perp_line_F10 hirr hR hv0 hW
  have hvQ : (Phi6 hirr).Q v = 0 := by
    have hv' : v ∈ singSeq (Phi6 hirr) (Rep6 F b c) R 6 := by
      rw [hW]; exact Submodule.mem_span_singleton_self v
    exact (mem_singSeq.mp hv').2
  have h2' : ∀ g ∈ R, ∀ x ∈ (Phi6 hirr).polar.perp (Submodule.span F {v}),
      Rep6 F b c g x - x ∈ Submodule.span F {v} := by
    simpa only [hW] using h2
  have h3' : ∀ g ∈ R, ∀ x, Rep6 F b c g x - x ∈
      (Phi6 hirr).polar.perp (Submodule.span F {v}) := by
    simpa only [hW] using h3
  have hcard := card_le_of_point (Phi6 hirr) (Rep6 F b c) (natRep_injective _)
    (preserves_Q6 hirr) hv0 hvQ h2' h3'
  rw [finrank_idx F] at hcard
  exact hcard

theorem core_false {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {R J : Subgroup ↥(Omega6 F b c)}
    (S : Sylow 2 ↥(Omega6 F b c)) (hR : IsPGroup 2 ↥R) (hRc : Nat.card F ^ 4 < Nat.card ↥R)
    (hJR : J ≤ Subgroup.normalizer (R : Set ↥(Omega6 F b c))) (hJs : ¬ Group.IsSolvable ↥J)
    (hSJ : (S : Subgroup ↥(Omega6 F b c)) ≤ J) {v : Idx → F} (hv0 : v ≠ 0)
    (hv : ∀ g ∈ J, ((g : GL Idx F) : Matrix Idx Idx F) *ᵥ v = v) : False := by
  have hR1 : R ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hRc
    have hF : 0 < Nat.card F := Nat.card_pos_iff.mpr ⟨⟨(0 : F)⟩, inferInstance⟩
    have hpow : 0 < Nat.card F ^ 4 := pow_pos hF 4
    omega
  have hWne : singSeq (Phi6 hirr) (Rep6 F b c) R 6 ≠ ⊥ := singSeq_six_ne_bot hirr hR hR1
  have hJW : ∀ g ∈ J, ∀ w ∈ singSeq (Phi6 hirr) (Rep6 F b c) R 6,
      Rep6 F b c g w ∈ singSeq (Phi6 hirr) (Rep6 F b c) R 6 := by
    intro g hg w hw
    exact apply_mem_singSeq (preserves_Q6 hirr) R 6 (hJR hg) hw
  have hJv : ∀ g ∈ J, Rep6 F b c g v = v := by
    intro g hg
    exact hv g hg
  have hvW : v ∈ singSeq (Phi6 hirr) (Rep6 F b c) R 6 := by
    refine mem_of_fixed_of_stable (K := F) (V := Idx → F) 2 (Rep6 F b c)
      (S := (S : Subgroup ↥(Omega6 F b c))) S.isPGroup' hWne ?_ ?_
    · intro g hg w hw
      exact hJW g (hSJ hg) w hw
    · intro x hx
      apply fixed_eq_span_of_sylow hirr S hv0 (fun g hg => hv g (hSJ hg)) x
      intro g hg
      exact hx g hg
  have hfr_le : Module.finrank F ↥(singSeq (Phi6 hirr) (Rep6 F b c) R 6) ≤ 2 :=
    finrank_singSeq_le_two hirr R 6
  have hfr_ne : Module.finrank F ↥(singSeq (Phi6 hirr) (Rep6 F b c) R 6) ≠ 0 := by
    intro h0
    exact hWne ((Submodule.finrank_eq_zero).mp h0)
  have hfr12 : Module.finrank F ↥(singSeq (Phi6 hirr) (Rep6 F b c) R 6) = 1 ∨
      Module.finrank F ↥(singSeq (Phi6 hirr) (Rep6 F b c) R 6) = 2 := by omega
  rcases hfr12 with hW1 | hW2
  · have hWspan : singSeq (Phi6 hirr) (Rep6 F b c) R 6 = Submodule.span F {v} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hW1 hvW hv0
    exact absurd (card_le_of_singSeq_line hirr hR hv0 hWspan) (not_le.mpr hRc)
  · exact hJs (isSolvable_of_fix_line_in_plane (Phi6 hirr) (Rep6 F b c) (natRep_injective _)
      (preserves_Q6 hirr) (finrank_idx F) (isTotallySingular_singSeq (Phi6 hirr) (Rep6 F b c) R 6)
      hW2 hvW hv0 J hJv hJW)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF
