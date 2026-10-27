module

public import CFSG.RankThree.PartOne.KFOUT3.KtySUQuot
public import CFSG.RankThree.PartOne.KLAY.RootLayer

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KLAY

variable {M Q : Type} [Group M] [Group Q] {p : ℕ} {q : M →* Q}

theorem bigAt_of_rootLayer (hp : p.Prime) (hq : IsCentralPQuot p q) {u : M} (hu : u ^ p = 1)
    {n : ℕ} (h : RootLayer M p u n) : BigAt p (q u) (· = n) := by
  obtain ⟨R, hRC, hRn, hRs, hRp, hRo, hRn', -⟩ := h
  refine bigAt_of_central hp hq hu hRp hRs hRo ?_ ?_ hRn'
  · intro s hs
    exact Subgroup.mem_centralizer_iff.mp (hRC hs) u (Set.mem_singleton u)
  · intro x hx s hs
    have hxC : x ∈ Subgroup.centralizer ({u} : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hx
    have := hRn.conj_mem ⟨s, hRC hs⟩ (show (⟨s, hRC hs⟩ : Subgroup.centralizer ({u} : Set M)) ∈
      R.subgroupOf (Subgroup.centralizer ({u} : Set M)) from hs) ⟨x, hxC⟩
    exact this

theorem smallAt_of_rootLayer (hq : IsCentralPQuot p q) {u : M} (hu : u ^ p = 1) {n_s n_b : ℕ}
    (h : RootLayer M p u n_s) (hdvd : ¬ n_b ∣ n_s) : SmallAt (q u) (· = n_b) := by
  obtain ⟨R, -, -, -, -, -, hRn', hmax⟩ := h
  refine smallAt_of_central hq hu fun T hT hTc m hm hmT => ?_
  have hTC : T ≤ Subgroup.centralizer ({u} : Set M) := fun τ hτ =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hTc τ hτ
  have hTR : T ≤ R := hmax T hTC hT
  have h1 : Nat.card T ∣ n_s := by
    rw [← hRn']
    exact Subgroup.card_dvd_of_le hTR
  have hm' : m = n_b := hm
  subst hm'
  exact hdvd (hmT.trans h1)

end CFSG.RankThree.PartOne.KFOUT3
