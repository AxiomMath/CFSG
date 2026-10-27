module

public import CFSG.Monster.B.GSide.BT2BridgeLabel
public import CFSG.Monster.B.GSide.BT2Block
public import Certificates.Certificate3130

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam

theorem k1Bad_root : K1Bad k1Root := ⟨by decide, by decide⟩

theorem k1_reach : ∀ v : Fin 8 → ZMod 2, K1Bad v →
    v = k1Root ∨ K1Edge k1Root v ∨ ∃ m, K1Bad m ∧ K1Edge k1Root m ∧ K1Edge m v :=
  Certificates.certificate3130

theorem ne_zero_of_k1Bad {v : Fin 8 → ZMod 2} (hv : K1Bad v) : (0 : Fin 8 → ZMod 2) ≠ v := by
  rintro rfl
  have h := hv.2
  rw [add_zero, qPoly_e0] at h
  exact zero_ne_one h

theorem ne_e0_of_k1Bad {v : Fin 8 → ZMod 2} (hv : K1Bad v) : Pi.single 0 1 ≠ v := by
  rintro rfl
  have h := hv.2
  rw [ZModModule.add_self] at h
  exact absurd h (by decide)

theorem sigVert_ne_cv0
    {v : Fin 8 → ZMod 2} (hv : K1Bad v) : sigVert v ≠ cv0 := by
  have h0 : qPoly (0 : Fin 8 → ZMod 2) = 0 := by decide
  rw [← sigVert_zero, Ne, sigVert_eq_iff hv.1 h0]
  exact fun e => ne_zero_of_k1Bad hv e.symm

theorem sigVert_ne_cw0
    {v : Fin 8 → ZMod 2} (hv : K1Bad v) : sigVert v ≠ cw0 := by
  rw [← sigVert_e0, Ne, sigVert_eq_iff hv.1 qPoly_e0]
  exact fun e => ne_e0_of_k1Bad hv e.symm

theorem adj_cv0_sigVert
    {v : Fin 8 → ZMod 2} (hv : K1Bad v) : cgraph.Adj cv0
    (sigVert v) :=
  cSigma_isClique cv0_mem_cSigma (sigVert_mem hv.1) (sigVert_ne_cv0 hv).symm

theorem adj_cw0_sigVert
    {v : Fin 8 → ZMod 2} (hv : K1Bad v) : cgraph.Adj cw0
    (sigVert v) := by
  have hw : cw0 ∈ cSigma 1 := sigVert_e0 ▸ sigVert_mem qPoly_e0
  exact cSigma_isClique hw (sigVert_mem hv.1) (sigVert_ne_cw0 hv).symm

theorem k1Bad_of_not_isType1782
    {v : Fin 8 → ZMod 2}
    (hv : qPoly v = 0)
    (h0 : cgraph.Adj cv0 (sigVert v)) (h1 : cgraph.Adj cw0 (sigVert v))
    (h : ¬ IsType1782 cv0 cw0 (sigVert v)) : K1Bad v := by
  refine ⟨hv, ?_⟩
  by_contra hq
  have hq' : qPoly (Pi.single 0 1 + v) = 0 :=
    (by decide : ∀ x : ZMod 2, x ≠ 1 → x = 0) _ hq
  have hz : qPoly (0 : Fin 8 → ZMod 2) = 0 := by decide
  have hn0 : (0 : Fin 8 → ZMod 2) ≠ v := by
    rintro rfl
    rw [sigVert_zero] at h0
    exact h0.ne rfl
  have hn1 : (Pi.single 0 1 : Fin 8 → ZMod 2) ≠ v := by
    rintro rfl
    rw [sigVert_e0] at h1
    exact h1.ne rfl
  have h01 : (0 : Fin 8 → ZMod 2) ≠ Pi.single 0 1 := by decide
  apply h
  have e := isType1782_sigVert hz qPoly_e0 hv h01 hn0 hn1 (by rw [zero_add]; exact hq')
  rwa [sigVert_zero, sigVert_e0] at e

theorem triRel_of_k1Edge
    {v w : Fin 8 → ZMod 2}
    (hv : K1Bad v) (hw : K1Bad w)
    (h : K1Edge v w) : TriRel cgraph IsType1782 cv0 cw0 (sigVert v) (sigVert w) := by
  intro h₁ h₂ h₃ h₂' h₃'
  have hz : qPoly (0 : Fin 8 → ZMod 2) = 0 := by decide
  have hT1 : IsType1782 cw0 (sigVert v) (sigVert w) := by
    have e := isType1782_sigVert qPoly_e0 hv.1 hw.1 (ne_e0_of_k1Bad hv) (ne_e0_of_k1Bad hw) h.1
      h.2.2
    rwa [sigVert_e0] at e
  have hT2 : IsType1782 cv0 (sigVert v) (sigVert w) := by
    have e := isType1782_sigVert hz hv.1 hw.1 (ne_zero_of_k1Bad hv) (ne_zero_of_k1Bad hw) h.1
      (by rw [zero_add]; exact h.2.1)
    rwa [sigVert_zero] at e
  exact homotopicT_triLoop_tetra triSymm_isType1782 h₁ h₂ h₃ h₂' h₃' hT2.1.2.2 hT1 hT2

theorem triRel_sigma_root
    {v : Fin 8 → ZMod 2} (hv : K1Bad v) :
    TriRel cgraph IsType1782 cv0 cw0 (sigVert k1Root) (sigVert v) := by
  rcases k1_reach v hv with rfl | he | ⟨m, hm, he₁, he₂⟩
  · exact TriRel.refl _ _ _
  · exact triRel_of_k1Edge k1Bad_root hv he
  · exact (triRel_of_k1Edge k1Bad_root hm he₁).trans (adj_cw0_sigVert hm)
      (adj_cv0_sigVert hm).symm (triRel_of_k1Edge hm hv he₂)

theorem triRel_sigma
    {v w : Fin 8 → ZMod 2} (hv : K1Bad v)
    (hw : K1Bad w) :
    TriRel cgraph IsType1782 cv0 cw0 (sigVert v) (sigVert w) :=
  (triRel_sigma_root hv).symm.trans (adj_cw0_sigVert k1Bad_root)
    (adj_cv0_sigVert k1Bad_root).symm (triRel_sigma_root hw)

theorem triRel_of_mem_cSigma
    {b b' : CVert} (hb : b ∈ cSigma 1)
    (hb' : b' ∈ cSigma 1)
    (h0 : cgraph.Adj cv0 b) (h1 : cgraph.Adj cw0 b) (h : ¬ IsType1782 cv0 cw0 b)
    (h0' : cgraph.Adj cv0 b') (h1' : cgraph.Adj cw0 b') (h' : ¬ IsType1782 cv0 cw0 b') :
    TriRel cgraph IsType1782 cv0 cw0 b b' := by
  obtain ⟨v, hv, rfl⟩ := eq_sigVert_of_mem hb
  obtain ⟨w, hw, rfl⟩ := eq_sigVert_of_mem hb'
  exact triRel_sigma (k1Bad_of_not_isType1782 hv h0 h1 h) (k1Bad_of_not_isType1782 hw h0' h1' h')

end CFSG.Monster.B.GSide
