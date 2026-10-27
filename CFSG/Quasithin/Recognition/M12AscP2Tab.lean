module

public import CFSG.Quasithin.Recognition.M12AscCountH

public section

namespace CFSG.Quasithin

@[expose] def xTab : List (Fin 12) := tabOf (ascHImg 2)

@[expose] def uTab : List (Fin 12) := tabOf (ascHImg 3)

@[expose] def uzTab : List (Fin 12) := tmul uTab zTab

@[expose] def aFTab : List (Fin 12) := [0, 6, 5, 7, 4, 2, 1, 3, 8, 10, 9, 11]

@[expose] def nrm (x f : List (Fin 12)) : List (Fin 12) :=
  tmul f (tmul (tmul x (tmul f (tmul x x))) (tmul (tmul x x) (tmul f x)))

theorem xTab_mem : xTab ∈ ascHTabs := by decide +kernel
theorem xTab_cube : tmul xTab (tmul xTab xTab) = tid := by decide +kernel
theorem xTab_ne : xTab ≠ tid := by decide +kernel
theorem uTab_not_q : uTab ∉ qTabs := by decide +kernel
theorem uzTab_not_q : uzTab ∉ qTabs := by decide +kernel

theorem CH_x : ∀ h ∈ ascHTabs, tmul h xTab = tmul xTab h →
    ∃ k < 6, h = tpow (tmul xTab zTab) k := by decide +kernel

theorem tpow_six_w : ∀ k < 6, tpow (tpow (tmul xTab zTab) k) 6 = tid := by decide +kernel

theorem cube_split_w : ∀ k < 6, tpow (tpow (tmul xTab zTab) k) 3 = tid →
    tpow (tmul xTab zTab) k = tid ∨ tpow (tmul xTab zTab) k = xTab ∨
      tpow (tmul xTab zTab) k = tmul xTab xTab := by decide +kernel

theorem sq_split_w : ∀ k < 6, tmul (tpow (tmul xTab zTab) k) (tpow (tmul xTab zTab) k) = tid →
    tpow (tmul xTab zTab) k = tid ∨ tpow (tmul xTab zTab) k = zTab := by decide +kernel

theorem nrm_mem : ∀ x' ∈ ascHTabs, tmul x' (tmul x' x') = tid → x' ≠ tid →
    ∀ f ∈ FTabs, nrm x' f = tid ∨ nrm x' f = zTab := by decide +kernel

theorem nrm_mul_z : ∀ f ∈ FTabs, nrm xTab f = zTab → nrm xTab (tmul zTab f) = tid := by
  decide +kernel

theorem conj_not_in_span : ∀ x' ∈ ascHTabs, tmul x' (tmul x' x') = tid → x' ≠ tid →
    ∀ s ∈ FTabs, s ≠ tid → s ≠ zTab → nrm x' s = tid →
      tmul x' (tmul s (tmul x' x')) ≠ tid ∧ tmul x' (tmul s (tmul x' x')) ≠ zTab ∧
      tmul x' (tmul s (tmul x' x')) ≠ s ∧ tmul x' (tmul s (tmul x' x')) ≠ tmul zTab s := by
  decide +kernel

theorem sq_eq_z_mem_q : ∀ h ∈ ascHTabs, tmul h h = zTab → h ∈ qTabs := by decide +kernel

theorem aFTab_mem : aFTab ∈ FTabs := by decide +kernel
theorem aFTab_unique : ∀ f ∈ FTabs, f ≠ tid → nrm xTab f = tid → tmul f uTab = tmul uTab f →
    f = aFTab := by decide +kernel

end CFSG.Quasithin
