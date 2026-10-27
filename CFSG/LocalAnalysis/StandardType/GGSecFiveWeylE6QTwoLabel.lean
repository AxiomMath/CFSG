module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly

theorem eq_of_ggLabelIso_end {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (h' : ((lab'.tag = .twA ∧ lab'.rank = 5) ∨ (lab'.tag = .D ∧ lab'.rank = 4) ∨
      (lab'.tag = .twD ∧ lab'.rank = 5)) ∧ lab'.n = 1) :
    lab = lab' := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  simp only [GGLabelIso, LargeEvenLabel.mk.injEq] at h
  rcases h with h | h | h | h | h | h | h | h <;>
    (obtain ⟨h' | h' | h', -⟩ := h' <;> obtain ⟨rfl, rfl⟩ := h' <;> simp_all)

variable {G : Type} [Group G]

theorem innerDiagOnLabel_of_marking (hRig : GGLabelRigidInput) {p : ℕ} {Bs L : Subgroup G}
    {S : LargeEvenLabel → Prop} (hS : ∀ lab lab', GGLabelIso lab lab' → S lab' → S lab)
    (hID : GGInnerDiagOn Bs L) (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => S lab)) :
    GGInnerDiagOnLabel (fun _ lab => S lab) p Bs L := by
  obtain ⟨hperf, lab₁, hΛ₁, hraw₁⟩ := hID
  obtain ⟨-, lab₂, hΛ₂, hraw₂⟩ := hlab
  obtain ⟨-, _, _, _, -, -, -, hS₂⟩ := largeEvenRawDatum_exists hraw₂
  have hgl₂ : GGHasLabel lab₂ (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw₂
  have hgl₁ : GGHasLabel lab₁ (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw₁
  have hiso : GGLabelIso lab₁ lab₂ := hRig lab₁ lab₂ _ hΛ₁ hΛ₂ hgl₁ hgl₂
  exact ⟨hperf, lab₁, hΛ₁,
    largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hS lab₁ lab₂ hiso hS₂, hP⟩) hraw₁⟩

end CFSG.StandardType.E6QTwo
