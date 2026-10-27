module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelReflRank1

public section

namespace CFSG.StandardType

namespace E6Dep

private def DH : List Vec6 :=
  [![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 0, 1, 2, 1, 0], ![0, 1, 1, 2, 1, 0],
    ![0, 1, 2, 0, 1, 0], ![0, 1, 2, 2, 1, 0], ![1, 0, 1, 2, 0, 0], ![1, 0, 1, 2, 2, 0],
    ![1, 0, 2, 1, 1, 0], ![1, 1, 1, 2, 1, 0], ![1, 1, 2, 0, 1, 0], ![1, 1, 2, 2, 1, 0],
    ![1, 2, 0, 0, 1, 0], ![1, 2, 0, 1, 0, 0], ![1, 2, 0, 1, 2, 0], ![1, 2, 0, 2, 0, 0],
    ![1, 2, 0, 2, 2, 0], ![1, 2, 1, 2, 0, 0], ![1, 2, 1, 2, 2, 0], ![1, 2, 2, 0, 1, 0],
    ![1, 2, 2, 2, 1, 0], ![2, 0, 1, 2, 0, 0], ![2, 0, 1, 2, 2, 0], ![2, 0, 2, 1, 1, 0],
    ![2, 1, 0, 1, 1, 0], ![2, 1, 0, 2, 1, 0], ![2, 1, 2, 1, 1, 0]]

private def DHshift : Fin 6 → Vec6 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0],
    ![2, 1, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0]]

private theorem dh_gen : ∀ i : Fin 6, ∀ d ∈ DH, (gensL i).mulVec d - DHshift i ∈ DH := by
  decide +kernel

private theorem dh_excl : ∀ c : Vec6, c 5 = 0 → norm6 c = 2 → ∀ d' ∈ DH,
    ∃ d ∈ DH, (reflMat (gram6.mulVec c) c).mulVec d + d' ∉ DH := by
  decide +kernel

private theorem gensL_five : ∀ i : Fin 6, ∀ v : Vec6, ((gensL i).mulVec v) 5 = v 5 := by
  decide +kernel

private theorem gensL_isometry : ∀ i : Fin 6,
    (gensL i).transpose * gram6 * gensL i = gram6 := by
  decide +kernel

private def good (g : Mat6) : Prop :=
  (∀ v : Vec6, (g.mulVec v) 5 = v 5) ∧
    g.transpose * gram6 * g = gram6 ∧
    ∃ t : Vec6, ∀ d ∈ DH, g.mulVec d - t ∈ DH

private theorem good_one : good 1 := by
  refine ⟨fun v => by rw [Matrix.one_mulVec], ?_, 0, fun d hd => ?_⟩
  · rw [Matrix.transpose_one, one_mul, mul_one]
  · simpa only [Matrix.one_mulVec, sub_zero] using hd

private theorem good_gensL (i : Fin 6) : good (gensL i) :=
  ⟨gensL_five i, gensL_isometry i, DHshift i, dh_gen i⟩

private theorem good_mul {g h : Mat6} (hg : good g) (hh : good h) : good (g * h) := by
  obtain ⟨hg5, hgiso, tg, hgt⟩ := hg
  obtain ⟨hh5, hhiso, th, hht⟩ := hh
  refine ⟨?_, ?_, tg + g.mulVec th, ?_⟩
  · intro v
    rw [← Matrix.mulVec_mulVec, hg5, hh5]
  · calc
      (g * h).transpose * gram6 * (g * h)
          = h.transpose * (g.transpose * gram6 * g) * h := by
            rw [Matrix.transpose_mul]
            simp only [Matrix.mul_assoc]
      _ = h.transpose * gram6 * h := by rw [hgiso]
      _ = gram6 := hhiso
  · intro d hd
    have hd' : h.mulVec d - th ∈ DH := hht d hd
    have hgd' : g.mulVec (h.mulVec d - th) - tg ∈ DH := hgt _ hd'
    convert hgd' using 1
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub, sub_add_eq_sub_sub_swap]

private theorem closureL_good {g : Mat6} (hg : g ∈ closureL) : good g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact good_gensL i
  | one => exact good_one
  | mul g h _ _ ihg ihh => exact good_mul ihg ihh

theorem eq_refl36_of_isRefl {T : Mat6} (hT : T ∈ closureL) (h2 : T * T = 1)
    (hfix : Fintype.card {v : Vec6 // T.mulVec v = v} * 3 = 3 ^ 6) : T ∈ refl36 := by
  obtain ⟨h5, hiso, t, ht⟩ := closureL_good hT
  obtain ⟨c, hc5, hcase⟩ := isRefl6_cases h5 hiso h2 hfix
  rcases hcase with ⟨hcn, hTeq⟩ | ⟨hcn, hTeq⟩
  · rw [hTeq]
    exact Finset.mem_image.mpr
      ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc5, hcn⟩, rfl⟩
  · exfalso
    have hd0 : (0 : Vec6) ∈ DH := by decide +kernel
    have ht0 : -t ∈ DH := by
      simpa only [Matrix.mulVec_zero, zero_sub] using ht 0 hd0
    obtain ⟨d, hd, hnot⟩ := dh_excl c hc5 hcn (-t) ht0
    apply hnot
    rw [← hTeq]
    simpa only [sub_eq_add_neg] using ht d hd

end E6Dep

end CFSG.StandardType

end
