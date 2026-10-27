module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Defs
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5LangDatum

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section FramePos

private theorem g5_ggLangReidx_ggLangReidx {R N : ℕ} (h : R = N) (v : Fin N → ℤ) :
    ggLangReidx h (ggLangReidx h.symm v) = v := by
  subst h
  funext j
  simp [ggLangReidx]

private theorem g5_ggLangReidx_injective {R N : ℕ} (h : R = N) :
    Function.Injective (ggLangReidx (N := N) h) := by
  intro v w hvw
  funext i
  have h1 := congrFun hvw (Fin.cast h i)
  simp only [ggLangReidx] at h1
  have h2 : Fin.cast h.symm (Fin.cast h i) = i := Fin.ext rfl
  rwa [h2] at h1

private theorem g5_ggGraphLat_eq_permLattice
    {t : StatedLieTag} (ht : GGExcFive t) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hε : eps p f = 1) (u : Fin (langTag t).rank → ℤ) :
    ggGraphLat t u =
      permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) u := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · rw [piB_F4]
    rfl
  · have hdvd : p ∣ 2 ^ f - 1 := (eps_eq_one_iff p f).1 hε
    rw [piB_E6_of_dvd f hdvd]
    rfl
  · rw [piB_E7]
    rfl
  · rw [piB_E8]
    rfl
  · have hdvd : p ∣ 2 ^ f - 1 := (eps_eq_one_iff p f).1 hε
    have hnot : ¬ p ∣ 2 ^ f + 1 := not_dvd_pow_two_add_one_of_dvd hp hp2 f hdvd
    rw [piB_twistedE6_of_not_dvd f hnot]
    rfl

theorem ggG5_frame_pos
    {t : StatedLieTag} {p f : ℕ} (ht : GGExcFive t) (hp : p.Prime)
    (hp2 : p ≠ 2) (hε : eps p f = 1) :
    Nonempty (GGLangFrame t p f ht) := by
  have hw : GGWeylLaw t p f ht (1 : WeylGroup (langTag t)) := by
    intro u
    simpa only [one_smul, hε] using g5_ggGraphLat_eq_permLattice ht hp hp2 hε u
  have hlang : ggPhi t f (1 : ModGL (langTag t) GGL) =
      1 * canonicalRep (coxeterSystem (langTag t)) GGL (1 : WeylGroup (langTag t)) := by
    rw [map_one, canonicalRep_one, one_mul]
  have hg : (1 : ModGL (langTag t) GGL) ∈ adjointGroup (langTag t) GGL := one_mem _
  obtain ⟨M, _hMw, hMg0⟩ := ggG5_datum_of_lang ht hw hg hlang
  have hcomm : GGCommPi t p f ht (1 : WeylGroup (langTag t)) := by
    intro v
    simp
  let hR := rank_eq_langTag f ht
  let frame : Set (Fin (ggU (absTag t) 6 f).D.rank → ℤ) :=
    {β | β ∈ (ggU (absTag t) 6 f).D.roots ∧ latPerm (piB t p f) β = β ∧
      ggGraphLat t (ggLangReidx hR β) = ggLangReidx hR β}
  refine ⟨M, frame, ?_, ?_, ?_, 1, ?_, ?_, ?_⟩
  · intro β hβ
    exact hβ.1
  · intro β hβ
    exact hβ.2.1
  · intro β hβ
    exact hβ.2.2
  · intro β _hβ A
    rw [hMg0]
    simp
  · intro α hα hαfix
    refine ⟨α, ⟨hα, hαfix, ?_⟩, 1, hcomm, ?_⟩
    · have h1 : ggLangReidx hR α =
          permLattice ((finCongr hR).permCongr (piB t p f)) (ggLangReidx hR α) := by
        rw [← ggReidx_latPerm_permLattice hR (piB t p f) α, hαfix]
      exact (g5_ggGraphLat_eq_permLattice ht hp hp2 hε (ggLangReidx hR α)).trans h1.symm
    · simp
  · intro β hβ hgβ
    let β₀ : Fin (ggU (absTag t) 6 f).D.rank → ℤ := ggLangReidx hR.symm β
    have hβ₀ : ggLangReidx hR β₀ = β := g5_ggLangReidx_ggLangReidx hR β
    refine ⟨β₀, ⟨?_, ?_, ?_⟩, 1, ?_, ?_⟩
    · rw [mem_roots_iff_isRoot f ht, hβ₀]
      exact hβ
    · apply g5_ggLangReidx_injective hR
      rw [ggReidx_latPerm_permLattice hR (piB t p f) β₀, hβ₀]
      exact (g5_ggGraphLat_eq_permLattice ht hp hp2 hε β).symm.trans hgβ
    · rw [hβ₀]
      exact hgβ
    · rw [canonicalRep_one, map_one]
    · rw [one_smul, hβ₀]

end FramePos

end CFSG.StandardType.GGFinModel.G5
