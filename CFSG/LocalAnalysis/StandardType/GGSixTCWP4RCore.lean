module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSet
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ROrbLen
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RSimple
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RLabel
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RKind
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RVec

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenLieTag LargeEvenSplit LargeEvenHalfSplit
  LargeEvenUntwisted LargeEvenInLambda2)
open CFSG.StandardType (GGLabelIso)

section Core

variable {τ : Tag} {S : TcrSys}

theorem tcrLabs_mem_of_dataOK {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    {d : TcrCData} (hd : TcDataOK ρ Ψ d) (F : ℕ) :
    tcrLabOf (LabAt ρ F Ψ) ∈ tcrLabsOf d F := by
  obtain ⟨he, hr, hN, hk⟩ := hd
  unfold tcrLabsOf
  rw [List.mem_flatMap]
  refine ⟨tcrKindOfK (twistKindOf ρ Ψ), hk, ?_⟩
  unfold LabAt
  rw [tcrLabOf_componentLabel, he, hr, hN]
  exact List.mem_cons_self

theorem tcrLabs_class_of_dataOK {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    {d : TcrCData} (hd : TcDataOK ρ Ψ d) (F : ℕ) {lab' : LargeEvenLabel}
    (h : GGLabelIso (LabAt ρ F Ψ) lab') : tcrLabOf lab' ∈ tcrLabsOf d F := by
  obtain ⟨he, hr, hN, hk⟩ := hd
  have hok : TcrTagOK (LabAt ρ F Ψ).tag := tcrTagOK_componentLabel _ _ _ _
  have hcls := (tcrLabelClass_of_iso hok h).2
  unfold tcrLabsOf
  rw [List.mem_flatMap]
  refine ⟨tcrKindOfK (twistKindOf ρ Ψ), hk, ?_⟩
  unfold LabAt at hcls
  rw [tcrLabOf_componentLabel] at hcls
  rw [he, hr, hN]
  exact hcls

theorem ggLabelIso_symm {a b : LargeEvenLabel} (h : GGLabelIso a b) : GGLabelIso b a := by
  obtain ⟨t, r, n⟩ := a
  obtain ⟨t', r', n'⟩ := b
  unfold GGLabelIso at h ⊢
  rcases h with h | h | h | h | h | h | h | h
  · left
    exact h.symm
  · right; left
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h2, h1, h3.symm, h4.symm⟩
  · right; right; right; left
    obtain ⟨h1, h2⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h1 h2 ⊢
    obtain ⟨rfl, rfl, -⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp
  · right; right; left
    obtain ⟨h1, h2⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h1 h2 ⊢
    obtain ⟨rfl, rfl, -⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp
  · right; right; right; right; right; left
    obtain ⟨h1, h2⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h1 h2 ⊢
    obtain ⟨rfl, rfl, -⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp
  · right; right; right; right; left
    obtain ⟨h1, h2⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h1 h2 ⊢
    obtain ⟨rfl, rfl, -⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp
  · right; right; right; right; right; right; right
    obtain ⟨h1, h2⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h1 h2 ⊢
    obtain ⟨rfl, rfl, -⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp
  · right; right; right; right; right; right; left
    obtain ⟨h1, h2⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h1 h2 ⊢
    obtain ⟨rfl, rfl, -⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp

theorem tcrLabs_split_of {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    {d : TcrCData} (hd : TcDataOK ρ Ψ d) {F p : ℕ}
    (h : ∃ lab', GGLabelIso lab' (LabAt ρ F Ψ) ∧ LargeEvenSplit p lab') :
    (tcrLabsOf d F).any (tcrSplitT p) = true := by
  obtain ⟨lab', hiso, hs⟩ := h
  have hok : TcrTagOK (LabAt ρ F Ψ).tag := tcrTagOK_componentLabel _ _ _ _
  have hok' := (tcrLabelClass_of_iso hok (ggLabelIso_symm hiso)).1
  rw [List.any_eq_true]
  exact ⟨_, tcrLabs_class_of_dataOK hd F (ggLabelIso_symm hiso), tcrSplitT_of hok' hs⟩

theorem tcrLabs_half_of {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    {d : TcrCData} (hd : TcDataOK ρ Ψ d) {F p : ℕ}
    (h : ∃ (c : Prop) (lab' : LargeEvenLabel), GGLabelIso lab' (LabAt ρ F Ψ) ∧
      LargeEvenHalfSplit p lab' c) :
    (tcrLabsOf d F).any (tcrHalfSplitT p) = true := by
  obtain ⟨c, lab', hiso, hs⟩ := h
  have hok : TcrTagOK (LabAt ρ F Ψ).tag := tcrTagOK_componentLabel _ _ _ _
  have hok' := (tcrLabelClass_of_iso hok (ggLabelIso_symm hiso)).1
  rw [List.any_eq_true]
  exact ⟨_, tcrLabs_class_of_dataOK hd F (ggLabelIso_symm hiso), tcrHalfSplitT_of hok' hs⟩

theorem tcrLabs_overlap_of {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ₁ Ψ₂ : Set (Fin τ.rank → ℤ)}
    {d₁ d₂ : TcrCData} (hd₁ : TcDataOK ρ Ψ₁ d₁) (hd₂ : TcDataOK ρ Ψ₂ d₂) {F : ℕ}
    (hiso : GGLabelIso (LabAt ρ F Ψ₁) (LabAt ρ F Ψ₂)) :
    (tcrLabsOf d₁ F).any (fun l => (tcrLabsOf d₂ F).contains l) = true := by
  rw [List.any_eq_true]
  exact ⟨_, tcrLabs_class_of_dataOK hd₁ F hiso, by simpa using tcrLabs_mem_of_dataOK hd₂ F⟩

theorem tcrSplit_half {p : ℕ} (l : TcrLab) (h : tcrSplitT p l = true) :
    tcrHalfSplitT p l = true := by
  unfold tcrHalfSplitT
  simp [h]

end Core

end CFSG.StandardType.TableCRes

end
