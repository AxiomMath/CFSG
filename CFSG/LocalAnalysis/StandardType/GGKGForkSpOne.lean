module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkSpRow
public import CFSG.LocalAnalysis.StandardType.GGKGForkSpRoot
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableBSymp

theorem recipeSymplectic_rootSL2
    {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 2 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusRootSL2 p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have : NeZero l := ⟨by omega⟩
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_symplectic hp hp2 hpq (by omega),
    ggTorusRootSL2_of_rootDatum hp (fun φ hφ _ => sp_I_subset_inn hφ) center_spProj_eq_bot
      (ggCenterPrime_sp hp hp2) (ggKGRootDatum_symplectic hl hp hp2 hpq)⟩

theorem ggKGOneOn_spSplit
    : GGKGOneOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1 := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := hs
  dsimp only at htag hpn
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  rcases htag with rfl | rfl <;>
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeSymplectic_rootSL2 hp hp2 hpn hl2 hQ

end CFSG.StandardType
