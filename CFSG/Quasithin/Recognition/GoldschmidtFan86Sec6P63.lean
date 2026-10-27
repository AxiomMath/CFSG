module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P63Fin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P63Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Hyp

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62 P63

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan63 (F : FanTree Γ G) (hΞ : ∃ T : Track Γ G, InXi T) (h61 : Fan61 F) (h62 : Fan62 F)
    (h512b : Fan512b F) (h517a : Fan517a F) (hD : LemmaD F) (h517c : Fan517c F) : Fan63 F := by
  intro h40 α z hz g
  have hα : valence Γ α = 5 := by
    have h1 := h61 h40 α z hz
    have h2 : valence Γ α = 3 ∨ valence Γ α = 5 := F.valence α
    omega
  have hzc : IsCentralInvolIn G α z := cinv_iff.1 hz
  obtain ⟨T, hT⟩ := hΞ
  obtain ⟨c, hc⟩ : ∃ c : ℤ, valence Γ (T.line.vert c) = 5 := by
    by_cases h0 : valence Γ (T.line.vert 0) = 5
    · exact ⟨0, h0⟩
    · refine ⟨1, ?_⟩
      have h1 : valence Γ (T.line.vert 0) ≠ valence Γ (T.line.vert 1) :=
        F.alternating _ _ (by simpa using T.line.adj 0)
      have h2 : valence Γ (T.line.vert 1) = 3 ∨ valence Γ (T.line.vert 1) = 5 := F.valence _
      have h3 : valence Γ (T.line.vert 0) = 3 ∨ valence Γ (T.line.vert 0) = 5 := F.valence _
      omega
  obtain ⟨g₀, hg₀⟩ := exists_smul_of_valence_eq F (u := α) (w := T.line.vert c) (by rw [hc, hα])
  have hz₀ : (labZ F hα hzc).z (T.line.vert c) ∈ Cinv G (T.line.vert c) := lab_cinv F hα hzc hc
  have hz₀e : (labZ F hα hzc).z (T.line.vert c) = g₀ * z * g₀⁻¹ := by
    rw [labZ_z]
    exact labOf_eq hzc.2.2.2 hg₀
  obtain ⟨hZZ, hcore, -⟩ := cinv_core F h40 h62 hT hz₀
  have e1 : c - 1 + 1 = c := by omega
  obtain ⟨L, hL, H⟩ := exists_labHyp F h40 h512b h517a hD h517c T hT (c - 1) hZZ hz₀.1
    (by rw [show c - 1 + 2 = c + 1 by omega]; exact hcore) (by rw [e1]; exact hc)
    (by rw [e1]; exact hz₀)
  rw [e1] at hL
  have hLα : L.z α = z := by
    have := L.equivariant g₀⁻¹ (T.line.vert c) hc
    rw [hL, hz₀e, ← hg₀, inv_smul_smul] at this
    rw [this]
    group
  have hv3 : valence Γ (T.line.vert (c + 1)) = 3 := by
    have h1 : valence Γ (T.line.vert c) ≠ valence Γ (T.line.vert (c + 1)) :=
      F.alternating _ _ (T.line.adj c)
    have h2 : valence Γ (T.line.vert (c + 1)) = 3 ∨ valence Γ (T.line.vert (c + 1)) = 5 :=
      F.valence _
    omega
  have D : LineData L T.line c := ⟨hv3, fun c' i hc' =>
    (cinv_core F h40 h62 hT (cinv_iff.2 (L.isCentral _ hc'))).2.2 i⟩
  have hvg : valence Γ (g • α) = 5 := by rw [F.valence_smul_eq]; exact hα
  have := ballStab_four F h40 H D hvg
  rwa [L.equivariant g α hα, hLα] at this

end CFSG.Quasithin.Fan86
