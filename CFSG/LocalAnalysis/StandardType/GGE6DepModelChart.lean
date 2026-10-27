module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs

public section

namespace CFSG.StandardType

namespace E6Dep

theorem chart (t w c : ZMod 3) (h : t * w = 2) (hc : c ≠ 0) :
    ∃ (g : Mat6) (wv x1 y1 : Vec6),
      (∃ word : List (Fin 7), evalWord (gensAll 0 t 0 w) word = g) ∧
      g.mulVec x1 = xx ∧ g.mulVec y1 = c • xs ∧ g.mulVec xx = wv ∧
      wv 5 = 0 ∧ x1 5 = 0 ∧ y1 5 = 0 ∧ norm6 wv = 1 ∧ norm6 x1 = 1 ∧ norm6 y1 = 1 ∧
      bil6 x1 y1 = 0 ∧ bil6 xs wv = 0 ∧ x1 ≠ y1 ∧ x1 ≠ -y1 ∧ xs ≠ wv ∧ xs ≠ -wv ∧
      (∃ word : List (Fin 6), evalWord gensL word = reflNorm x1) ∧
      (∃ word : List (Fin 6), evalWord gensL word = reflNorm y1) ∧
      (∃ word : List (Fin 6), evalWord gensL word = reflNorm xs) ∧
      (∃ word : List (Fin 6), evalWord gensL word = reflNorm wv) ∧
      reflNorm x1 * reflNorm y1 = reflNorm y1 * reflNorm x1 ∧
      reflNorm xs * reflNorm wv = reflNorm wv * reflNorm xs ∧
      (Finset.univ.filter fun v : Vec6 => bil6 v xx = 0 ∧ bil6 v xs = 0 ∧ bil6 v wv = 0).card =
        27 := by
  have htw : (t = 1 ∧ w = 2) ∨ (t = 2 ∧ w = 1) := by
    revert t w
    decide +kernel
  have hc' : c = 1 ∨ c = 2 := by
    revert c
    decide +kernel
  rcases htw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hc' with rfl | rfl
  ·
    refine ⟨evalWord (gensAll 0 1 0 2) [0, 1, 2, 6, 3, 4, 2, 3, 1, 2, 6], ![1, 0, 0, 0, 0, 0],
      ![1, 0, 2, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ⟨[0, 1, 2, 6, 3, 4, 2, 3, 1, 2, 6], rfl⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨[4, 3, 0, 1, 2, 5, 2, 5, 2, 5, 2, 1, 0, 3, 4], by decide +kernel⟩,
      ⟨[5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5, 5, 5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5], by decide +kernel⟩,
      ⟨[5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5, 5, 5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5], by decide +kernel⟩,
      ⟨[1, 2, 5, 0, 1, 2, 5, 2, 1, 0, 5, 2, 1], by decide +kernel⟩, ?_, ?_, ?_⟩
    all_goals decide +kernel
  ·
    refine ⟨evalWord (gensAll 0 1 0 2) [0, 1, 2, 6, 3, 4, 2, 3, 1, 2, 6], ![1, 0, 0, 0, 0, 0],
      ![1, 0, 2, 1, 0, 0], ![0, 0, 0, 0, 2, 0], ⟨[0, 1, 2, 6, 3, 4, 2, 3, 1, 2, 6], rfl⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨[4, 3, 0, 1, 2, 5, 2, 5, 2, 5, 2, 1, 0, 3, 4], by decide +kernel⟩,
      ⟨[5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5], by decide +kernel⟩,
      ⟨[5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5, 5, 5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5], by decide +kernel⟩,
      ⟨[1, 2, 5, 0, 1, 2, 5, 2, 1, 0, 5, 2, 1], by decide +kernel⟩, ?_, ?_, ?_⟩
    all_goals decide +kernel
  ·
    refine ⟨evalWord (gensAll 0 2 0 1) [1, 2, 6, 3, 4, 2, 3, 1, 2, 6], ![1, 0, 0, 0, 0, 0],
      ![2, 0, 1, 2, 0, 0], ![0, 0, 0, 0, 1, 0], ⟨[1, 2, 6, 3, 4, 2, 3, 1, 2, 6], rfl⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨[5, 4, 3, 0, 1, 2, 5, 2, 1, 0, 3, 4, 5], by decide +kernel⟩,
      ⟨[5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5, 5, 5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5], by decide +kernel⟩,
      ⟨[5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5, 5, 5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5], by decide +kernel⟩,
      ⟨[1, 2, 5, 0, 1, 2, 5, 2, 1, 0, 5, 2, 1], by decide +kernel⟩, ?_, ?_, ?_⟩
    all_goals decide +kernel
  ·
    refine ⟨evalWord (gensAll 0 2 0 1) [1, 2, 6, 3, 4, 2, 3, 1, 2, 6], ![1, 0, 0, 0, 0, 0],
      ![2, 0, 1, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ⟨[1, 2, 6, 3, 4, 2, 3, 1, 2, 6], rfl⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨[5, 4, 3, 0, 1, 2, 5, 2, 1, 0, 3, 4, 5], by decide +kernel⟩,
      ⟨[5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5], by decide +kernel⟩,
      ⟨[5, 2, 3, 4, 1, 2, 3, 0, 1, 2, 5, 5, 5, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5], by decide +kernel⟩,
      ⟨[1, 2, 5, 0, 1, 2, 5, 2, 1, 0, 5, 2, 1], by decide +kernel⟩, ?_, ?_, ?_⟩
    all_goals decide +kernel

end E6Dep

end CFSG.StandardType

end
