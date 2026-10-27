module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86AsmLOrb
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan517_of_lab (F : FanTree Γ G) (h40 : Fan40 F) (h517a : Fan517a F) (h517c : Fan517c F)
    (L : ZLab Γ G) : Fan517 F L := by
  intro α hα
  have hc : L.z α ∈ Cinv G α := AsmL.cinv_lab L hα
  have hne3 : valence Γ α ≠ 3 := by omega
  have hz : L.zGroup 2 α = Subgroup.closure (zBall Γ α (L.z α) 2) := by
    unfold ZLab.zGroup
    rw [AsmL.zSet_eq F L hα]
  refine ⟨?_, fun l₁ l₂ l₃ h1 h2 h3 => ?_⟩
  · rw [hz]
    exact h517a h40 α (L.z α) hne3 hc
  · obtain ⟨g₁, hg₁, e₁⟩ := AsmL.exists_conj F L hα (AsmL.valence_of_dist_two F hα h1)
    obtain ⟨g₂, hg₂, e₂⟩ := AsmL.exists_conj F L hα (AsmL.valence_of_dist_two F hα h2)
    obtain ⟨g₃, hg₃, e₃⟩ := AsmL.exists_conj F L hα (AsmL.valence_of_dist_two F hα h3)
    rw [e₁, e₂, e₃]
    exact h517c h40 α (L.z α) hne3 hc g₁ g₂ g₃ (by rw [hg₁]; exact h1) (by rw [hg₂]; exact h2)
      (by rw [hg₃]; exact h3)

end CFSG.Quasithin.Fan86
