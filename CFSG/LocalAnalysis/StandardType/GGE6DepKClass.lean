module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKClassOrbit
public import CFSG.LocalAnalysis.StandardType.GGE6DepKClassForm
public import CFSG.LocalAnalysis.StandardType.GGE6DepKClassGen

public section

namespace CFSG.StandardType

namespace E6Dep

open Matrix

theorem kclass {c : ZMod 3} {h : Vec6} (hn : normK c h = 1) (hg : KGen c h) :
    ∃ (sw : List (Fin 5)) (s t u w : ZMod 3), s * u + t * w = 2 ∧ w ≠ 0 ∧ u + w * c = 0 ∧
      evalWord gS sw * rK c h * evalWord gS sw.reverse = gensAll s t u w 6 := by
  obtain ⟨hm, hq, hf⟩ := kgen_parts hn hg
  obtain ⟨sw, hsw⟩ := iso_orbit (m := mpart h) (by simp [mpart]) (by simp [mpart]) hm hq
  have hdec : h = mpart h + h 4 • xs + h 5 • xx := by
    ext i
    fin_cases i <;> simp [mpart, xs, xx]
  have hsh : (evalWord gS sw).mulVec h = h0 + h 4 • xs + h 5 • xx := by
    conv_lhs => rw [hdec]
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hsw,
      evalWord_gS_xs, evalWord_gS_xx]
  have hconj := rK_conj (c := c) (evalWord_gS_mul_reverse sw) (evalWord_gS_isometry c sw) h
  rw [hsh, rK_std] at hconj
  obtain ⟨h1, h2⟩ := rK_std_arith c (h 4) (h 5) hf
  exact ⟨sw, h 4, h 5, c * h 5 - c * c * h 4, c * h 4 - h 5, h1, hf, h2, hconj⟩

end E6Dep

end CFSG.StandardType

end
